import OAI.Analysis.CircleDomains.Sobolev.DensityL2
import OAI.Analysis.CircleDomains.Topology.EuclideanPlaneCoordinates

namespace OAI

/-! The decaying finite-chart density is globally square integrable.
No compact restriction is needed after inserting the spherical factor. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem spherical_weight_sq_le_areaDensity (z : ℂ) :
    (1 / (1 + ‖z‖ ^ 2)) ^ 2 ≤ sphericalAreaDensity z := by
  rw [div_pow, one_pow, sphericalAreaDensity]
  exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)

theorem global_spherical_weighted_density_memLp
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (he : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) :
    MemLp (fun z : ℂ => (g (z : Sphere)).toReal / (1 + ‖z‖ ^ 2)) 2 volume := by
  let k : ℂ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (1 / (1 + ‖z‖ ^ 2)) * g (z : Sphere)
  have hden (z : ℂ) : 0 ≤ 1 / (1 + ‖z‖ ^ 2) := by positivity
  have hc : Continuous (fun z : ℂ => 1 / (1 + ‖z‖ ^ 2)) :=
    continuous_const.div (continuous_const.add (continuous_norm.pow 2))
      (fun z => ne_of_gt (by positivity))
  have hk : Measurable k := by
    apply Measurable.mul
    · exact hc.measurable.ennreal_ofReal
    · exact hg.comp OnePoint.continuous_coe.measurable
  have hke : (∫⁻z, k z ^ 2) < ∞ := by
    rw [lintegral_sphericalArea _ (hg.pow_const 2)] at he
    apply lt_of_le_of_lt (lintegral_mono fun z => ?_) he
    dsimp [k]
    rw [mul_pow, ← ENNReal.ofReal_pow (hden z)]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (spherical_weight_sq_le_areaDensity z)) le_rfl
  have hm := memLp_two_toReal_of_lintegral_sq_ne_top volume hk hke.ne
  convert hm using 1
  funext z
  dsimp [k]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hden z)]
  simp only [div_eq_mul_inv, one_mul, mul_comm]

theorem global_spherical_weighted_density_memLp_realProd
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (he : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) :
    MemLp (fun p : ℝ × ℝ =>
      (g ((⟨p.1, p.2⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨p.1, p.2⟩ : ℂ)‖ ^ 2))
      2 volume := by
  exact (global_spherical_weighted_density_memLp g hg he).comp_measurePreserving
    (Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd)

theorem global_spherical_weighted_density_memLp_euclidean
    (g : Sphere → ℝ≥0∞) (hg : Measurable g)
    (he : (∫⁻x, g x ^ 2 ∂sphericalArea) < ∞) :
    MemLp (fun x : EuclideanPlane =>
      (g ((⟨x 0, x 1⟩ : ℂ) : Sphere)).toReal / (1 + ‖(⟨x 0, x 1⟩ : ℂ)‖ ^ 2))
      2 volume := by
  exact (global_spherical_weighted_density_memLp_realProd g hg he).comp_measurePreserving
    euclideanPlaneCoordinates_measurePreserving

end CircleDomainRigidity

end

end OAI
