import OAI.Geometry.NodalSets.Charts.SphereEnergyL2Injective
import OAI.Geometry.NodalSets.Charts.SphereFiniteVariationalFrame

namespace OAI

namespace Yau.Target
open MeasureTheory
noncomputable section
local instance sphereFormBoundsMeasurable : MeasurableSpace Base := borel Base
local instance sphereFormBoundsBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_resolvent_smooth_variational (d : SphereEnergyData)
    (mu : ℝ) (hmu : mu ≠ 0) (u : SphereEnergySmooth d)
    (he : sphereL2Resolvent d (sphereEnergyL2Linear d u) = mu • sphereEnergyL2Linear d u) :
    ∀ v : SphereEnergyHilbert d,
      inner ℝ (sphereEnergyToCompletion d u) v =
        mu⁻¹ * inner ℝ (sphereEnergyL2Linear d u) (sphereEnergyL2Map d v) := by
  have hz : sphereEnergyToCompletion d u = mu⁻¹ • sphereWeakSolution d (sphereEnergyL2Linear d u) := by
    apply sphereEnergyL2Map_injective d
    rw [sphereEnergyL2Map_coe,map_smul]
    change sphereEnergyL2Linear d u = mu⁻¹ • sphereL2Resolvent d (sphereEnergyL2Linear d u)
    rw [he,smul_smul,inv_mul_cancel₀ hmu,one_smul]
  intro v
  rw [hz,inner_smul_left_eq_smul,smul_eq_mul,sphereWeakSolution_spec]

theorem sphere_resolvent_quadratic_to_form_lower (d : SphereEnergyData)
    (mu : ℝ) (hmu : 0 < mu) (z : SphereEnergyHilbert d)
    (hz : sphereEnergyL2Map d z ≠ 0)
    (hb : inner ℝ (sphereL2Resolvent d (sphereEnergyL2Map d z)) (sphereEnergyL2Map d z) ≤
      mu * ‖sphereEnergyL2Map d z‖^2) :
    (mu⁻¹-1)*‖sphereEnergyL2Map d z‖^2 ≤ sphereCompletedDirichlet d z z := by
  let f := sphereEnergyL2Map d z
  have hweak : ‖sphereWeakSolution d f‖^2 ≤ mu*‖f‖^2 := by
    simpa only [sphereL2Resolvent_inner,real_inner_self_eq_norm_sq] using hb
  have hc := real_inner_le_norm (sphereWeakSolution d f) z
  rw [sphereWeakSolution_spec,real_inner_self_eq_norm_sq] at hc
  have hsq := mul_self_le_mul_self (sq_nonneg ‖f‖) hc
  have hprod := mul_le_mul_of_nonneg_right hweak (sq_nonneg ‖z‖)
  have hn : 0 < ‖f‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hmain : ‖f‖^2 ≤ mu*‖z‖^2 := (mul_le_mul_iff_left₀ hn).mp (by nlinarith)
  have hdiv : ‖f‖^2 / mu ≤ ‖z‖^2 := (div_le_iff₀ hmu).mpr (by nlinarith [hmain])
  rw [sphereCompletedDirichlet,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  change (mu⁻¹-1)*‖f‖^2 ≤ ‖z‖^2-‖f‖^2
  rw [div_eq_mul_inv] at hdiv
  nlinarith

theorem sphere_smooth_rayleigh_of_resolvent_bound (d : SphereEnergyData)
    (mu : ℝ) (hmu : 0 < mu) (u : SphereEnergySmooth d) (hu : u ≠ 0)
    (hb : inner ℝ (sphereL2Resolvent d (sphereEnergyL2Linear d u)) (sphereEnergyL2Linear d u) ≤
      mu * ‖sphereEnergyL2Linear d u‖^2) :
    mu⁻¹-1 ≤ sphereRayleighQuotient d.tensor d.density (SphereEnergySmooth.toSmooth d u) := by
  have hn : sphereEnergyL2Linear d u ≠ 0 := fun h ↦ hu ((sphereEnergyL2Linear_eq_zero_iff d u).mp h)
  have h := sphere_resolvent_quadratic_to_form_lower d mu hmu (sphereEnergyToCompletion d u)
    (by simpa only [sphereEnergyL2Map_coe] using hn) (by simpa only [sphereEnergyL2Map_coe] using hb)
  rw [sphereEnergyL2Map_coe,sphereCompletedDirichlet_coe,sphereEnergyL2Linear_norm_sq] at h
  apply (le_div_iff₀ _).mpr h
  rw [← sphereEnergyL2Linear_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr hn)

end
end Yau.Target

end OAI
