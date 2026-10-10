import Mathlib
import OAI.Analysis.HardSphere.Density.DensityOperators

namespace OAI

section

noncomputable section
open scoped ComplexOrder InnerProductSpace NNReal ENNReal
namespace HardSphere.Density
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
lemma quadratic_lower_of_unit (V : Submodule ℂ H) (A : H →L[ℂ] K) {c : ℝ}
    (h : ∀x∈V,‖x‖=1 → c≤‖A x‖^2) {x : H} (hx : x∈V) :
    c*‖x‖^2≤‖A x‖^2 := by
  by_cases hz : x=0
  · simp [hz]
  have hn : ‖x‖≠0 := norm_ne_zero_iff.mpr hz
  have hv : (‖x‖⁻¹:ℝ) • x∈V := by
    exact V.smul_mem ((‖x‖⁻¹:ℝ):ℂ) hx
  have hu : ‖(‖x‖⁻¹:ℝ) • x‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ hn]
  have hh := h _ hv hu
  rw [A.map_smul_of_tower,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),mul_pow] at hh
  have hm := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖x‖)
  calc
    _ ≤ (‖x‖⁻¹)^2*‖A x‖^2*‖x‖^2 := hm
    _ = _ := by field_simp

lemma Operator.compressionTrace_lower (T : Operator H) (A : H →L[ℂ] K) {c : ℝ}
    (h : ∀x∈T.toCLM.kerᗮ,‖x‖=1 → c≤‖A x‖^2) :
    c≤T.compressionTrace A := by
  rw [T.compressionTrace_eq]
  have hs := T.root_hasSum.mul_left c
  calc
    c = ∑' i : basisSet H,c*‖T.root (basis H i)‖^2 := by simpa using hs.tsum_eq.symm
    _ ≤ _ := hs.summable.tsum_le_tsum (fun i ↦ quadratic_lower_of_unit _ A h (T.root_mem_support _))
      (T.image_summable A)

lemma Operator.compressionTrace_upper (T : Operator H) (A : H →L[ℂ] K)
    (h : ∀x,‖A x‖≤‖x‖) : T.compressionTrace A≤1 := by
  rw [T.compressionTrace_eq,←T.root_hasSum.tsum_eq]
  exact (T.image_summable A).tsum_le_tsum (fun i ↦ pow_le_pow_left₀ (norm_nonneg _) (h _) 2)
    T.root_hasSum.summable

end HardSphere.Density
end
end

end OAI
