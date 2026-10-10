import OAI.MeasureTheory.Falconer.Measures.DensityCellCharge

namespace OAI

/-! # Finite multiplication of the charged hit-cell masses -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
variable {ι : Type*} [DecidableEq ι]

theorem finite_parent_mass_step (P C : Finset ι) (parent : ι → ι)
    (wp wc : ι → ℝ≥0∞) (F : ℝ≥0∞) (hparent : ∀ i ∈ C, parent i ∈ P)
    (hcharge : ∀ p ∈ P, (∑ i ∈ C with parent i = p, wc i) ≤ F*wp p) :
    (∑ i ∈ C, wc i) ≤ F*(∑ p ∈ P, wp p) := by
  classical
  calc
    _ = ∑ p ∈ P, ∑ i ∈ C with parent i = p, wc i :=
      (Finset.sum_fiberwise_of_maps_to hparent wc).symm
    _ ≤ ∑ p ∈ P, F*wp p := Finset.sum_le_sum hcharge
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem finite_mass_multiplication (I : ℕ → Finset ι) (parent : ℕ → ι → ι)
    (w : ℕ → ι → ℝ≥0∞) (F : ℕ → ℝ≥0∞) (J : ℕ)
    (hparent : ∀ j < J, ∀ i ∈ I (j+1), parent j i ∈ I j)
    (hcharge : ∀ j < J, ∀ p ∈ I j,
      (∑ i ∈ I (j+1) with parent j i = p, w (j+1) i) ≤ F j*w j p) :
    (∑ i ∈ I J, w J i) ≤ (∏ j ∈ Finset.range J, F j)*(∑ i ∈ I 0, w 0 i) := by
  classical
  induction J with
  | zero => simp
  | succ J ih =>
    have hs : (∑ i ∈ I (J+1), w (J+1) i) ≤ F J*(∑ i ∈ I J, w J i) :=
      finite_parent_mass_step (I J) (I (J+1)) (parent J) (w J) (w (J+1)) (F J)
        (hparent J (Nat.lt_succ_self _)) (by
          intro p hp
          exact hcharge J (Nat.lt_succ_self _) p hp)
    have hprev := ih (fun j hj => hparent j (Nat.lt_succ_of_lt hj))
      (fun j hj => hcharge j (Nat.lt_succ_of_lt hj))
    calc
      _ ≤ F J*(∑ i ∈ I J, w J i) := hs
      _ ≤ F J*((∏ j ∈ Finset.range J, F j)*(∑ i ∈ I 0, w 0 i)) := mul_le_mul' le_rfl hprev
      _ = _ := by rw [Finset.prod_range_succ]; ring

end Falconer

end OAI
