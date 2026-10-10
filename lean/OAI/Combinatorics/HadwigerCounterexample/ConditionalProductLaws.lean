import OAI.Combinatorics.HadwigerCounterexample.FiniteConditioning

namespace OAI

/-! # Conditional Product Laws -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators

variable {A B I : Type} [Fintype A] [Fintype B]

theorem subLaw_pair {w : Wgt A} {v : Wgt B} (hw : SubLaw w) (hv : SubLaw v) :
    SubLaw (pairW w v) := by
  refine ⟨fun x => mul_nonneg (hw.nz _) (hv.nz _),?_⟩
  rw [pairW_tot]
  exact (mul_le_mul hw.total hv.total (tot_nonneg hv.nz) (by norm_num)).trans_eq (one_mul _)

theorem pair_unif :
    unif (α:=A×B) = pairW unif unif := by
  funext x; simp [pairW,unif_apply,mul_comm]

theorem unifOn_slice (p : A × B → Prop) (x : A) (y : B) :
    unifOn p (x,y) =
      mapW (unifOn p) Prod.fst x * unifOn (fun y => p (x,y)) y := by
  classical
  have hm : mapW (unifOn p) Prod.fst x =
      nbr (fun y => p (x,y)) / nbr p := by
    simp only [mapW,pr,avg,Fintype.sum_prod_type,unifOn_val, nbr,tot]
    rw [Finset.sum_eq_single x]
    · simp [ind_true,div_eq_mul_inv,Finset.sum_mul]
    · intro b _ hb
      simp [ind,hb]
    · simp
  rw [hm,unifOn_val,unifOn_val]
  by_cases h : p (x,y)
  · have hh {A : Type} [Fintype A] (p : A → Prop) (x : A) (hx : p x) : 0 < nbr p := by
      have hp := weight_le_tot (fun y => ind_nonneg (p y)) x
      exact lt_of_lt_of_le (ind_one hx ▸ zero_lt_one) hp
    rw [ind_one h]
    have hv := hh _ _ h
    have hw := hh (fun y => p (x,y)) _ h
    field_simp
  · rw [ind_zero h]
    ring

theorem unifOn_and (p q : A → Prop) :
    onW (unifOn p) q = unifOn (fun x => p x ∧ q x) := by
  classical
  have hp : pr (unifOn p) q = nbr (fun x => p x ∧ q x) / nbr p := by
    simp only [pr,avg,unifOn_val,div_eq_mul_inv,ind_and,nbr,tot,Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  funext x
  rw [onW_val,hp,unifOn_val,unifOn_val,ind_and]
  by_cases h : p x
  · by_cases g : q x
    · have hl (p : A → Prop) (h : p x) : 0 < nbr p :=
        lt_of_lt_of_le (ind_one h ▸ zero_lt_one) (weight_le_tot (fun y => ind_nonneg (p y)) x)
      have hh := hl p h
      have hg := hl (fun x => p x ∧ q x) ⟨h,g⟩
      field_simp
    · rw [ind_zero g]
      ring
  · rw [ind_zero h]
    ring

theorem unifOn_and_prod (p : A → Prop) (q : B → Prop) :
    unifOn (fun x : A × B => p x.1 ∧ q x.2) = pairW (unifOn p) (unifOn q) := by
  have h :
      nbr (fun x : A × B => p x.1 ∧ q x.2) = nbr p * nbr q := by
    change tot _ = _ * _
    simp_rw [ind_and]
    exact pairW_tot (fun x => ind (p x)) (fun y => ind (q y))
  funext x
  simp only [pairW,unifOn_val,h,ind_and]
  ring_nf

theorem pr_cap {w v : Wgt A} {c : ℝ} (h : ∀ x, w x ≤ c*v x) (p : A → Prop) :
    pr w p ≤ c*pr v p := calc
  _ ≤ pr (fun x => c*v x) p := pr_mono_left (w:=w) (v:=fun x => c*v x) h _
  _ = _ := by simp only [pr,avg,Finset.mul_sum,mul_assoc]

def semi (w : Wgt A) (k : A → Wgt B) : Wgt (A × B) := fun x => w x.1 * k x.1 x.2

theorem semi_avg (w : Wgt A) (k : A → Wgt B) (f : A × B → ℝ) :
    avg (semi w k) f = avg w (fun x => avg (k x) (fun y => f (x,y))) := by
  simp only [avg,semi,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

theorem pair_semi_avg (w w' : Wgt A) (k k' : A → Wgt B) (f : (A × B) × (A × B) → ℝ) :
    avg (pairW (semi w k) (semi w' k')) f =
      avg (pairW w w') (fun x =>
        avg (pairW (k x.1) (k' x.2)) (fun y => f ((x.1,y.1), (x.2,y.2)))) := by
  simp only [pairW_avg, semi_avg]
  refine avg_congr fun x _ => ?_
  exact avg_avg _ _ _

theorem pair_semi_pr (w w' : Wgt A) (k k' : A → Wgt B) (p : A × A → Prop) (q : B × B → Prop) :
    pr (pairW (semi w k) (semi w' k')) (fun x => p (x.1.1,x.2.1) ∧ q (x.1.2,x.2.2)) =
      avg (pairW w w') (fun x => ind (p x) * pr (pairW (k x.1) (k' x.2)) q) := by
  unfold pr
  rw [pair_semi_avg]
  simp_rw [ind_and]
  refine avg_congr fun x _ => ?_
  exact avg_mul' _ _ _

variable [Fintype I] [DecidableEq I]

/-- Reassociate two arrays of independent columns into componentwise independent pairs. -/
theorem prodW_pair_pr (w v : I → Wgt A) (p : I → A × A → Prop) :
    pr (pairW (prodW w) (prodW v)) (fun x => ∀ i, p i (x.1 i,x.2 i)) =
      ∏ i, pr (pairW (w i) (v i)) (p i) := by
  simp_rw [pr,ind_all,pairW_avg]
  have hx (x : I → A) :
      avg (prodW v) (fun y => ∏ i, ind (p i (x i,y i))) =
        ∏ i, avg (v i) (fun y => ind (p i (x i,y))) :=
    prodW_avg _ (fun i y => ind (p i (x i,y)))
  simp_rw [hx]
  exact prodW_avg w (fun i x => avg (v i) (fun y => ind (p i (x,y))))

end HadwigerCounterexample

end

end OAI
