import OAI.Combinatorics.ContingencyTables.Transport.FiniteExposureVariance
import OAI.Combinatorics.ContingencyTables.Transport.AuxiliaryRepairMass

namespace OAI

/-! # Finite variance extension along completion-retaining repairs -/

namespace ContingencyTables.FiniteExposureVariance

open scoped BigOperators Classical
open CommonBasesFPRAS

variable {X : Type*} [Fintype X]

lemma variance_le_center (w H : X → ℝ) (hw : ∀ x,0 ≤ w x) (a : ℝ) :
    variance w H ≤ ∑ x,w x*(H x-a)^2 := by
  by_cases hz : 0 < ∑ x,w x
  · exact finite_center_min Finset.univ w H a hz
  · have hz' : (∑ x,w x)=0 :=
      le_antisymm (le_of_not_gt hz) (Finset.sum_nonneg (fun x _ => hw x))
    have hzero := zero_mass_weights w hw hz'
    simp only [variance,hzero,zero_mul,Finset.sum_const_zero,le_refl]

omit [Fintype X] in
lemma square_repair_split (x y a : ℝ) : (x-a)^2 ≤ 2*(x-y)^2+2*(y-a)^2 := by
  nlinarith [sq_nonneg (x-2*y+a)]

omit [Fintype X] in
lemma repair_center_mass {B D T : Type*} [Fintype B] [Fintype D] [Fintype T]
    (w : B → ℝ) (v : D → ℝ) (H : B → ℝ) (R : D → B) (label : D → T)
    (hw : ∀ b,0 ≤ w b) (hdom : ∀ d,v d ≤ w (R d))
    (hinj : Function.Injective (fun d => (label d,R d))) (a : ℝ) :
    (∑ d,v d*(H (R d)-a)^2) ≤ Fintype.card T*∑ b,w b*(H b-a)^2 := by
  calc
    _ ≤ ∑ d,w (R d)*(H (R d)-a)^2 :=
      Finset.sum_le_sum (fun d _ => mul_le_mul_of_nonneg_right (hdom d) (sq_nonneg _))
    _ ≤ ∑ p : T×B,w p.2*(H p.2-a)^2 :=
      ExcessContextProfiles.finite_injective_sum_le (fun d => (label d,R d)) hinj
        (fun p => w p.2*(H p.2-a)^2) (fun p => mul_nonneg (hw _) (sq_nonneg _))
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

omit [Fintype X] in
/-- The actual typewise repair injection extends a transversal variance
bound to all states, charging each defect-to-repair difference once. -/
theorem variance_sum_repair {B D T : Type*} [Fintype B] [Fintype D] [Fintype T]
    (w : B → ℝ) (v : D → ℝ) (H : B → ℝ) (K : D → ℝ)
    (R : D → B) (label : D → T) (hw : ∀ b,0 ≤ w b) (hv : ∀ d,0 ≤ v d)
    (hdom : ∀ d,v d ≤ w (R d)) (hinj : Function.Injective (fun d => (label d,R d))) :
    variance (Sum.elim w v) (Sum.elim H K) ≤
      (1+2*(Fintype.card T:ℝ))*variance w H+2*∑ d,v d*(K d-H (R d))^2 := by
  have hcenter := variance_le_center (Sum.elim w v) (Sum.elim H K)
    (fun x => Sum.rec hw hv x) (mean w H)
  have hdefect : (∑ d,v d*(K d-mean w H)^2) ≤
      2*(∑ d,v d*(K d-H (R d))^2)+2*(∑ d,v d*(H (R d)-mean w H)^2) := by
    calc
      _ ≤ ∑ d,v d*(2*(K d-H (R d))^2+2*(H (R d)-mean w H)^2) :=
        Finset.sum_le_sum (fun d _ => mul_le_mul_of_nonneg_left
          (square_repair_split (K d) (H (R d)) (mean w H)) (hv d))
      _ = _ := by
        have he (d : D) : v d*(2*(K d-H (R d))^2+2*(H (R d)-mean w H)^2)=
            2*(v d*(K d-H (R d))^2)+2*(v d*(H (R d)-mean w H)^2) := by ring
        simp_rw [he]
        rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  have hmass := repair_center_mass w v H R label hw hdom hinj (mean w H)
  change (∑ d,v d*(H (R d)-mean w H)^2) ≤ Fintype.card T*variance w H at hmass
  rw [Fintype.sum_sum_type] at hcenter
  change variance (Sum.elim w v) (Sum.elim H K) ≤ variance w H+(∑ d,v d*(K d-mean w H)^2) at hcenter
  nlinarith

end ContingencyTables.FiniteExposureVariance

end OAI
