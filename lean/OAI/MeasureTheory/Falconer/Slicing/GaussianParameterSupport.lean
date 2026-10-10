import OAI.MeasureTheory.Falconer.Slicing.GaussianControlledRows
import OAI.MeasureTheory.Falconer.Slicing.GaussianPointClose
import OAI.MeasureTheory.Falconer.Slicing.GaussianBox

namespace OAI

/-! # A bounded point-parameter region for bounded original source laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussianRowNeighborhood_norm {n : ℕ} (B : Fin h → Space (n+1))
    (hB : ∀ i, ‖B i‖ ≤ 1) {ε : ℝ} {A : Fin h → Space (n+1)}
    (hA : A ∈ gaussianRowNeighborhood B ε) (i : Fin h) : ‖A i‖ ≤ ε+1 := by
  calc
    _ ≤ ‖A i-B i‖+‖B i‖ := by simpa only [sub_add_cancel] using norm_add_le (A i-B i) (B i)
    _ ≤ _ := add_le_add (hA i) (hB i)

theorem gaussianPointBand_parameter_bound (A : Fin h → Space d)
    {M D r : ℝ} (_hM : 0 ≤ M) (hA : ∀ i, ‖A i‖ ≤ M)
    {x : Space d} (hx : ‖x‖ ≤ D) {z : Space h} (hz : x ∈ gaussianPointBand A z r) :
    z ∈ coordinateBox h (D*M+r) := by
  intro i
  calc
    |z i| ≤ |inner ℝ x (A i)|+|inner ℝ x (A i)-z i| := by
      calc
        _ = |inner ℝ x (A i)-(inner ℝ x (A i)-z i)| := by congr 1; ring
        _ ≤ _ := abs_sub _ _
    _ ≤ ‖x‖*‖A i‖+r := add_le_add (abs_real_inner_le_norm _ _) (hz i)
    _ ≤ D*M+r := add_le_add
      (mul_le_mul hx (hA i) (norm_nonneg _) ((norm_nonneg x).trans hx)) le_rfl

theorem gaussian_point_mass_zero_outside_box
    (μ : Measure (Space d)) (A : Fin h → Space d)
    {M D r : ℝ} (hM : 0 ≤ M) (hA : ∀ i, ‖A i‖ ≤ M)
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ D) {z : Space h} (hz : z ∉ coordinateBox h (D*M+r)) :
    gaussianPointMass μ r (A,z) = 0 := by
  have hs : gaussianPointBand A z r ⊆ {x | ¬‖x‖ ≤ D} := by
    intro x hx hnorm
    exact hz (gaussianPointBand_parameter_bound A hM hA hnorm hx)
  have he : μ (gaussianPointBand A z r) = 0 := measure_mono_null hs (ae_iff.mp hμ)
  simp only [gaussianPointMass,he,mul_zero]

end Falconer

end OAI
