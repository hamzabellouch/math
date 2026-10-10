import OAI.Combinatorics.HadwigerCounterexample.PolynomialZeroTests

namespace OAI

/-! # Point Atom Vanishing -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Submodule Function Finset LinearMap
open scoped BigOperators
variable {p : Shape} {n : ℕ} {I A : Type} [Fintype I] [Fintype A]
variable [DecidableEq I] [DecidableEq A]

omit [Fintype A] in
private theorem pointPoly (f : Mat I I→ₗ[F] F) (x : Vec A→Vec I) (d : ℕ)
    (hx : ∀ i,(fun s=>x s i)∈Stocks A d) :
    (fun s=>f (vecMulVec (x s) (x s))) ∈ Stocks A (2*d) := by
  classical
  let E (i : I×I) := vecMulVec (Pi.single i.1 (1:F)) (Pi.single i.2 (1:F))
  have he (v : Vec I) :
      vecMulVec v v=∑ i:I × I,(v i.1*v i.2) • E i := by
    ext i j; rw [Matrix.sum_apply, Finset.sum_eq_single (i,j)]
    · simp [E,Matrix.vecMulVec_apply]
    · intro z _ hz
      have h : i≠z.1 ∨ j≠z.2 := not_and_or.mp (fun h=>hz (Prod.ext h.1.symm h.2.symm))
      rcases h with h|h <;> simp [E,Matrix.vecMulVec_apply,Pi.single_eq_of_ne h]
    simp
  let P (i : I × I) : Vec (Vec A) := f (E i) •
    ((fun s => x s i.1) * (fun s => x s i.2))
  have hm :
      (fun s=>f (vecMulVec (x s) (x s)))=∑ i:I×I,P i := by
    funext s; simp only [he,map_sum,map_smul,Finset.sum_apply,P,
      Pi.smul_apply, Pi.mul_apply,smul_eq_mul]; simp only [mul_comm]
  rw [hm]
  apply Submodule.sum_mem
  intro i _
  unfold P
  rw [two_mul]; exact Submodule.smul_mem _ _ (stock_prod (hx _) (hx _))

set_option maxHeartbeats 600000 in
theorem vat_erase (l : Tag p.g) (s : Label p.b) (f : Moment p n→ₗ[F] F)
    (h : pr (spins p n)
      (fun x => f (mom p s (lit Flavor.full l x)) ≠ 0)<1/4) :
    ∀ z : Base p.g n,allows l z → f (mom p s z)=0 := by
  classical
  let e : Base p.g n ≃ Knobs p.g n := ⟨curry,uncurry,fun _=>rfl,fun _=>rfl⟩
  let Z (x : Base p.g n) := lit Flavor.full l (e x)
  let Q (x : Base p.g n) := point p s (Z x)
  have he (i : Row p n) : (fun x=> Q x i)∈Stocks (BaseIdx p.g n) 1 := by
    rcases i with ⟨a,_|k⟩
    · exact stocks_one _ 1 _
    let h := monoBit s a.val
    by_cases ha : Flavor.full.keeps l k.1
    · unfold Q Z
      simp_rw [point_eval, baseV,Option.elim',lit,ite_eq_left ha]
      exact Submodule.smul_mem _ h (stock_var k)
    unfold Q Z
    simp_rw [point_eval,baseV,Option.elim',lit,ite_eq_right ha]
    exact stocks_one _ _ _
  intro z hz; by_contra ht
  have hZ : Z z=z := by
    funext i
    by_cases hh : Flavor.full.keeps l i.1
    · exact ite_eq_left hh
    rcases i with ⟨⟨d,t⟩|i,j⟩
    · exact (ite_eq_right hh).trans (hz d t hh j).symm
    exact (hh trivial).elim
  have hg := stocks_bound (BaseIdx p.g n) _ _
    (pointPoly f Q 1 he) ⟨z,(by unfold Q; rw [hZ]; exact ht)⟩
  have hpr :
      pr (spins p n) (fun x => f (mom p s (lit Flavor.full l x))≠0) =
      pr unif (fun x => f (vecMulVec (Q x) (Q x))≠0) := by
    unfold spins; rw [←draws_unif,←unif_equiv e,mapW_pr]; rfl
  rw [hpr] at h
  have hi := lt_of_le_of_lt hg h
  norm_num [bp] at hi

set_option maxHeartbeats 800000 in
theorem vat_excluded (z : Base p.g n) (E : Finset (Label p.b)) (f : Moment p n→ₗ[F] F)
    (h : ∀ s,s∉E → f (mom p s z)=0)
    (hE : (E.card:ℝ) < bp ((p.b:ℝ)-2*p.j)) : ∀ s,f (mom p s z)=0 := by
  classical
  let Q := fun s=>point p s z
  have he (i : Row p n) : (fun s=>Q s i)∈ Stocks (Fin p.b) p.j := by
    rcases i with ⟨a,b⟩
    have h : (fun s=>Q s (a,b)) = baseV z b • poly1 a.val := by
      unfold Q poly1; funext s; exact mul_comm _ _
    rw [h]; exact Submodule.smul_mem _ _ (subset_span ⟨_,a.property,rfl⟩)
  intro s; by_contra! hh
  let p' y := f (mom p y z)≠0
  have hz := stocks_bound (Fin p.b) _ _ (pointPoly f Q p.j he) ⟨s,hh⟩
  have ha := hz.trans (pr_mono unif_law.nz (p:=p') (q:=fun s=>s∈ E) fun i hi =>
    not_not.mp (fun hg=> hi (h i hg)))
  rw [pr_unif,nbr_eq_card, card_space (Vec (Fin p.b)), dim_vec,Fintype.card_fin] at ha
  have hh : Fintype.card {i // i∈E}=E.card := Fintype.card_coe E
  rw [hh,le_div_iff₀ (bp_pos _),←bp_add] at ha
  push_cast at ha
  rw [show -(2*(p.j:ℝ)) + p.b=p.b-2*(p.j:ℝ) by ring] at ha
  exact hE.not_ge ha
end HadwigerCounterexample

end

end OAI
