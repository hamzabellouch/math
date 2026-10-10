import OAI.Geometry.Kahler.BaseDensityStepSupport

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
namespace PinchedHartogs.BaseConstruction

lemma density_degree_ge {Q : ℕ} (hQ : 1 ≤ Q) (j : ℕ) : (Q:ℝ) ≤ (Q:ℝ)^(j+1) := by
  have hq : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  rw [pow_succ]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ hq) (by positivity : (0:ℝ) ≤ Q)

lemma density_sqrt_scale {Q : ℕ} (hQ : 0 < Q) (j : ℕ) :
    Real.sqrt ((Q:ℝ)^(j+1))=Real.sqrt ((Q:ℝ)^j)*Real.sqrt (Q:ℝ) := by
  rw [pow_succ,Real.sqrt_mul (by positivity)]

lemma density_envelope_bound {Q : ℕ} (hQ : 1 ≤ Q) {K R D : ℝ}
    (hK : 0 ≤ K) (hR : 0 ≤ R) (hD : 2*Real.sqrt (2*R) ≤ D) (j : ℕ) :
    K*Real.sqrt ((Q:ℝ)^j)*(2*Real.sqrt (2*R)/Real.sqrt ((Q:ℝ)^(j+1)))+2*R/(Q:ℝ)^(j+1) ≤
      K*D/Real.sqrt (Q:ℝ)+2*R/Q := by
  have hQ0 : 0 < Q := by omega
  have hq : (0:ℝ) < Q := by exact_mod_cast hQ0
  have hs : Real.sqrt ((Q:ℝ)^j) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (pow_pos hq j))
  rw [density_sqrt_scale hQ0 j]
  have he : K*Real.sqrt ((Q:ℝ)^j)*(2*Real.sqrt (2*R)/(Real.sqrt ((Q:ℝ)^j)*Real.sqrt (Q:ℝ)))=
      K*(2*Real.sqrt (2*R))/Real.sqrt (Q:ℝ) := by field_simp
  rw [he]
  apply add_le_add
  · gcongr
  · exact div_le_div_of_nonneg_left (by positivity) hq (density_degree_ge hQ j)

lemma density_phase_scale {Q : ℕ} (hQ : 0 < Q) (K : ℝ) (j : ℕ) :
    (Q:ℝ)^(j+1)*(K/Q)=K*(Q:ℝ)^j := by
  have hq : (Q:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hQ)
  rw [pow_succ]
  field_simp

lemma density_second_scale {Q : ℕ} (hQ : 0 < Q) (C : ℝ) (j : ℕ) :
    ((Q:ℝ)^(j+1))^2*(C/(Q:ℝ)^2)=C*((Q:ℝ)^j)^2 := by
  have hq : (Q:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hQ)
  rw [pow_succ]
  field_simp
  simp only [pow_succ]
  ring

end PinchedHartogs.BaseConstruction

end

end OAI
