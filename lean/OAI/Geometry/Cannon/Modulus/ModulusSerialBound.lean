import Mathlib
import OAI.Geometry.Cannon.Modulus.ModulusEnergy

namespace OAI

section
section
section
section
noncomputable section
open scoped InnerProductSpace
open Set

namespace CannonCells
open Set CannonDuality

variable {X ι J : Type*} [Fintype ι] [Fintype J]

theorem modulus_serial_bound [Nonempty J]
    (C : ι → Set X) (F : Set (Set X)) (H : J → Set (Set X))
    (w : J → Weights ι) (hw : ∀ j, Admissible (familyVectors C (H j) : Set (Weights ι)) (w j))
    (horth : ∀ i j k, j ≠ k → w j i*w k i=0)
    (hcross : ∀ A ∈ F, ∀ j, ∃ B ∈ H j, B ⊆ A) :
    modulus C F ≤ (∑ j, ‖w j‖^2)/(Fintype.card J : ℝ)^2 := by
  classical
  have hcard : 0 < (Fintype.card J : ℝ) := by exact_mod_cast Fintype.card_pos
  let W : Weights ι := (Fintype.card J : ℝ)⁻¹ • ∑ j, w j
  have hw' (j : J) := (admissible_iff C (H j) (w j)).mp (hw j)
  have hpoint (i : ι) : W i=(Fintype.card J : ℝ)⁻¹ * ∑ j, w j i := by simp [W]
  have hW : Admissible (familyVectors C F : Set (Weights ι)) W := by
    rw [admissible_iff]
    refine ⟨?_,?_⟩
    · intro i
      rw [hpoint]
      exact mul_nonneg (inv_nonneg.mpr hcard.le) (Finset.sum_nonneg (fun j _ => (hw' j).1 i))
    · intro A hA
      have hsum (j : J) : 1 ≤ ∑ i ∈ indices C A, w j i := by
        obtain ⟨B,hB,hBA⟩ := hcross A hA j
        exact ((hw' j).2 B hB).trans (Finset.sum_le_sum_of_subset_of_nonneg
          (indices_mono C hBA) (fun i _ _ => (hw' j).1 i))
      have hh := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hsum j)
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hh
      calc
        1 = (Fintype.card J : ℝ)⁻¹ * Fintype.card J := (inv_mul_cancel₀ (ne_of_gt hcard)).symm
        _ ≤ (Fintype.card J : ℝ)⁻¹ * ∑ j, ∑ i ∈ indices C A, w j i :=
          mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hcard.le)
        _ = ∑ i ∈ indices C A, W i := by
          simp only [hpoint,Finset.mul_sum]
          rw [Finset.sum_comm]
  have hsquare (i : ι) : (∑ j, w j i)^2=∑ j, (w j i)^2 := by
    rw [pow_two,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_eq_single j]
    · rw [pow_two]
    · intro k hk hkj
      exact horth i j k hkj.symm
    · simp
  have henergy : ‖W‖^2=(∑ j, ‖w j‖^2)/(Fintype.card J : ℝ)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [hpoint,mul_pow,hsquare]
    rw [← Finset.mul_sum]
    simp only [EuclideanSpace.real_norm_sq_eq]
    rw [Finset.sum_comm]
    simp only [div_eq_mul_inv,inv_pow,mul_comm]
  exact (modulus_le_energy C F W hW).trans henergy.le

theorem modulus_serial_uniform [Nonempty J]
    (C : ι → Set X) (F : Set (Set X)) (H : J → Set (Set X))
    (w : J → Weights ι) (hw : ∀ j, Admissible (familyVectors C (H j) : Set (Weights ι)) (w j))
    (horth : ∀ i j k, j ≠ k → w j i*w k i=0)
    (hcross : ∀ A ∈ F, ∀ j, ∃ B ∈ H j, B ⊆ A)
    {B : ℝ} (henergy : ∀ j, ‖w j‖^2 ≤ B) :
    modulus C F ≤ B/(Fintype.card J : ℝ) := by
  have hcard : 0 < (Fintype.card J : ℝ) := by exact_mod_cast Fintype.card_pos
  calc
    _ ≤ (∑ j, ‖w j‖^2)/(Fintype.card J : ℝ)^2 :=
      modulus_serial_bound C F H w hw horth hcross
    _ ≤ ((Fintype.card J : ℝ)*B)/(Fintype.card J : ℝ)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
        Finset.sum_le_sum (s:=Finset.univ) (fun j _ => henergy j)
    _ = _ := by field_simp

end CannonCells

end
end
section
noncomputable section

namespace CannonCapacity
open Set Metric Finset

attribute [local instance] Classical.propDecidable

end CannonCapacity

end
end
end
end
end

end OAI
