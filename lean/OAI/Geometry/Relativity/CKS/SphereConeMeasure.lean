import OAI.Geometry.Relativity.CKS.SchwarzschildCoordinates
import OAI.Geometry.Relativity.CKS.InducedMetric

namespace OAI

noncomputable section
open Set Filter Manifold Bundle MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal
namespace CKSSchwarzschild
open CKSBoundarySurface

def splitEuclidean : E3 ≃ₜ ℝ × E2 where
  toFun z := (z 0,dropPlane z)
  invFun := join
  left_inv := join_drop
  right_inv z := by cases z; simp
  continuous_toFun := firstCoordinate.continuous.prodMk dropPlane.continuous
  continuous_invFun := join.continuous
lemma splitEuclidean_preserves_volume : MeasurePreserving splitEuclidean volume volume := by
  have ha := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).comp
    (PiLp.volume_preserving_ofLp (Fin 3))
  have hb := (MeasurePreserving.id (volume : Measure ℝ)).prod (PiLp.volume_preserving_toLp (Fin 2))
  have h := hb.comp ha
  convert h using 1
  all_goals rfl
lemma join_preserves_volume : MeasurePreserving join volume volume :=
  splitEuclidean_preserves_volume.symm splitEuclidean.toMeasurableEquiv

lemma lintegral_radial_square : ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (r^2) = ENNReal.ofReal (1/3 : ℝ) := by
  have hn : ∀ᵐ r ∂(volume.restrict (Ioo (0:ℝ) 1)), 0 ≤ r^2 := Filter.Eventually.of_forall sq_nonneg
  have hi : IntegrableOn (fun r : ℝ => r^2) (Ioo 0 1) :=
    ((continuous_id.pow 2).continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  norm_num [integral_pow]

lemma lintegral_join_product (s : Set E2) (f : E2 → ℝ)
    (hf : AEMeasurable f (volume.restrict s)) :
    ∫⁻ z in join '' (Ioo (0 : ℝ) 1 ×ˢ s), ENNReal.ofReal ((z 0)^2 * f (dropPlane z)) =
      ENNReal.ofReal (1/3 : ℝ) * ∫⁻ y in s, ENNReal.ofReal (f y) := by
  rw [← join_preserves_volume.setLIntegral_comp_emb splitEuclidean.symm.measurableEmbedding]
  simp only [join_zero,drop_join]
  simp_rw [ENNReal.ofReal_mul (sq_nonneg _)]
  rw [Measure.volume_eq_prod,← Measure.prod_restrict]
  rw [lintegral_prod_mul (f := fun r : ℝ => ENNReal.ofReal (r^2))
    (g := fun y : E2 => ENNReal.ofReal (f y)) (by fun_prop)
    (ENNReal.measurable_ofReal.comp_aemeasurable hf)]
  rw [lintegral_radial_square]

end CKSSchwarzschild

end

end OAI
