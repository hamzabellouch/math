import Mathlib
import OAI.Geometry.DoublingHilbert.CoordinateSupport
import OAI.Geometry.DoublingHilbert.Main

namespace OAI

open Set Metric
open scoped BigOperators
noncomputable section
namespace CompactBanach
open DoublingHilbert

noncomputable def coordinateMap {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (I : Finset ℕ) (v : I → B) : RealL2 →ₗ[ℝ] B where
  toFun z := ∑ i : I, z i • v i
  map_add' z w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c z := by simp [Finset.smul_sum, smul_smul]

theorem coordinateMap_single {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (I : Finset ℕ) (v : I → B) (hv : ∀ i, ‖v i‖ ≤ 1) (j : ℕ) (a : ℝ) :
    ‖coordinateMap I v (lp.single 2 j a)‖ ≤ |a| := by
  classical
  change ‖∑ i : I, (lp.single 2 j a : RealL2) i • v i‖ ≤ |a|
  by_cases hj : j ∈ I
  · have he : (∑ i : I, (lp.single 2 j a : RealL2) i • v i) = a • v ⟨j, hj⟩ := by
      rw [Finset.sum_eq_single ⟨j, hj⟩]
      · simp [lp.single_apply]
      · intro i _ hi
        have hne : (i : ℕ) ≠ j := by
          intro heq
          exact hi (Subtype.ext heq)
        rw [lp.single_apply_ne (E := fun _ : ℕ => ℝ) 2 j a hne, zero_smul]
      · simp
    rw [he, norm_smul, Real.norm_eq_abs]
    simpa using mul_le_mul_of_nonneg_left (hv ⟨j, hj⟩) (abs_nonneg a)
  · have he : (∑ i : I, (lp.single 2 j a : RealL2) i • v i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hne : (i : ℕ) ≠ j := by rintro rfl; exact hj i.property
      rw [lp.single_apply_ne (E := fun _ : ℕ => ℝ) 2 j a hne, zero_smul]
    rw [he, norm_zero]
    exact abs_nonneg a

theorem coordinateMap_lower {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (I : Finset ℕ) (v : I → B)
    (hv : ∀ (c : I → ℝ) i, |c i| ≤ ‖∑ j, c j • v j‖)
    (z : RealL2) (hz : ∀ i ∉ I, z i = 0) :
    ∀ i, |z i| ≤ ‖coordinateMap I v z‖ := by
  intro i
  by_cases hi : i ∈ I
  · exact hv (fun j => z j) ⟨i, hi⟩
  · rw [hz i hi, abs_zero]
    exact norm_nonneg _

end CompactBanach
end

end OAI
