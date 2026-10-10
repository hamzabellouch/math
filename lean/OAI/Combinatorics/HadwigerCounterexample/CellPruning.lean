import OAI.Combinatorics.HadwigerCounterexample.FiniteConditioning
import OAI.Combinatorics.HadwigerCounterexample.ConditionalProductLaws

namespace OAI

/-! # Cell Pruning -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Finset
variable {A B I J : Type} [Fintype A] [Fintype B] [Fintype I] [Fintype J]

theorem sum_pr_tag (w : Wgt A) (P : A → Prop) (f : A→I) :
    ∑ i:I,pr w (fun x => P x ∧ f x=i) = pr w P := by
  classical
  unfold pr
  rw [← avg_sum]
  refine avg_congr fun x _ => ?_
  simp only [ind_and, ← Finset.mul_sum]
  rw [Finset.sum_eq_single (f x)]
  · rw [ind_one rfl,mul_one]
  · intro j _ hj; exact ind_zero hj.symm
  simp

/-- implication needed only almost surely for finite measures. -/
theorem pr_on_mono {w : Wgt A} (hw : ∀ x,0≤w x) {P Q : A→Prop}
    (h : ∀ x,w x≠0→ P x→ Q x) : pr w P ≤ pr w Q :=
  Finset.sum_le_sum (fun x _ => by
    by_cases he : w x=0
    · simp [he]
    exact mul_le_mul_of_nonneg_left (ind_mono (h x he)) (hw x))

theorem sum_pr_cells (w : Wgt (A × B)) (P : A × B → Prop) (f : A→I) (g : B→J) :
    ∑ i:I,∑ j:J,pr w (fun x => P x ∧ f x.1=i ∧ g x.2=j) = pr w P := by
  classical
  rw [← sum_pr_tag w P (fun x => (f x.1,g x.2)), Fintype.sum_prod_type]
  simp only [Prod.mk.injEq]

/-- restore the full pair-event probability in a specified cell. -/
theorem pair_restore (u : Wgt A) (v : Wgt B) (P : A → Prop) (Q : B → Prop)
    (hP : 0 < pr u P) (hQ : 0 < pr v Q)
    (c : A × B → Prop) :
    pr (pairW u v) (fun x => P x.1 ∧ Q x.2 ∧ c x)=
      pr u P * pr v Q * pr (pairW (onW u P) (onW v Q)) c := by
  classical
  let D := pr u P * pr v Q
  let d := pairW (onW u P) (onW v Q)
  change avg _ _ = D*avg d _
  unfold avg
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [pairW,d,onW_val,D,ind_and]
  field_simp

def memberC (p : A→Prop) (f : A→I) (i : I) (x : A) := p x ∧ f x=i

/-- heavy cells criterion. Loss charged to τ times opposite mass
rather than τ alone (key q fixed). -/
theorem prune_pairs (w : Wgt A) (v : Wgt B) (hw : SubLaw w) (hv : SubLaw v)
    (P : A → Prop) (Q : B→Prop) (f : A→I) (g : B→J)
    (C : A×B→Prop) (H T : ℝ) (hH : 0≤H) (hT : 0<T)
    {L : ℝ} (hi : (Fintype.card I : ℝ) ≤ L)
    (hj : (Fintype.card J : ℝ) ≤ L)
    (h : ∀ i j,T ≤ pr w (memberC P f i) → T ≤ pr v (memberC Q g j) →
      H≤ pr (pairW (onW w (memberC P f i)) (onW v (memberC Q g j))) C) :
    H * (pr w P * pr v Q) ≤ pr (pairW w v) (fun x => P x.1 ∧ Q x.2 ∧ C x) +
      (H*T*L)*(pr w P+pr v Q) := by
  classical
  let a (i:I) := pr w (memberC P f i)
  let b (i:J) := pr v (memberC Q g i)
  let d (i:I) (j:J) := pr (pairW w v) (fun x => memberC P f i x.1 ∧ memberC Q g j x.2 ∧ C x)
  have ha i : 0≤a i := pr_nonneg hw.nz
  have hb i : 0≤b i := pr_nonneg hv.nz
  have he i j : H*(a i*b j) ≤ d i j+ H*T*b j + H*T*a i := by
    have hz : 0≤ d i j := pr_nonneg (subLaw_pair hw hv).nz
    have ha' := mul_nonneg (mul_nonneg hH hT.le) (ha i)
    have hb' := mul_nonneg (mul_nonneg hH hT.le) (hb j)
    by_cases ht : T ≤ a i
    · by_cases hh : T ≤ b j
      · have hc := mul_le_mul_of_nonneg_right (h i j ht hh) (mul_nonneg (ha i) (hb j))
        have h1 := pair_restore w v _ _ (lt_of_lt_of_le hT ht) (lt_of_lt_of_le hT hh) C
        refine hc.trans ?_
        rw [mul_comm (pr _ C)]
        change _ ≤ d i j + _ + _
        unfold d
        rw [h1]
        change _ ≤ a i*b j * _ + _+_
        linarith
      · have hg := mul_le_mul_of_nonneg_left (le_of_not_ge hh) (mul_nonneg hH (ha i))
        calc H*(a i*b j) ≤ H*T*a i := by linarith only [hg]
             _ ≤ _ := by linarith only [hb',hz]
    have hg := mul_le_mul_of_nonneg_left (le_of_not_ge ht) (mul_nonneg hH (hb j))
    calc H*(a i*b j) ≤ H*T*b j := by linarith only [hg]
         _ ≤ _ := by linarith only [ha',hz]
  have hA : pr w P=∑ i,a i := (sum_pr_tag w P f).symm
  have hB : pr v Q=∑ j,b j := (sum_pr_tag v Q g).symm
  have hC :
      pr (pairW w v) (fun x => P x.1 ∧ Q x.2 ∧ C x) = ∑ i,∑ j,d i j := by
    rw [← sum_pr_cells (pairW w v) _ f g]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    unfold d; congr 1; unfold memberC; ext; tauto
  have h1 : H * (pr w P * pr v Q)=∑ i,∑ j,H*(a i*b j) := by
    rw [hA,hB]
    simp only [Finset.sum_mul,Finset.mul_sum]
    exact Finset.sum_comm;
  have h2 : ∑ i:I,∑ j:J,H*T*b j=(Fintype.card I:ℝ)*(H*T*pr v Q) := by
    simp only [← Finset.mul_sum,←hB,Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have h3 : ∑ i:I,∑ j:J,H*T*a i=(Fintype.card J:ℝ)*(H*T*pr w P) := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum,←hA,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    ring
  rw [h1]
  refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => he i j).trans ?_
  simp only [Finset.sum_add_distrib]
  rw [h2,h3,← hC]
  have hh := mul_le_mul_of_nonneg_right hj (show 0≤H*T*pr w P from
    mul_nonneg (mul_nonneg hH hT.le) (pr_nonneg hw.nz))
  have hh' := mul_le_mul_of_nonneg_right hi (show 0≤H*T*pr v Q from
    mul_nonneg (mul_nonneg hH hT.le) (pr_nonneg hv.nz))
  linarith only [hh,hh']

end HadwigerCounterexample

end

end OAI
