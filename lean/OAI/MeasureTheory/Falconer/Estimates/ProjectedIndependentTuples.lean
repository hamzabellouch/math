import OAI.MeasureTheory.Falconer.Slicing.GaussianPreservesIndependence
import OAI.MeasureTheory.Falconer.Radial.AffineNullTuples

namespace OAI

/-! # Fubini transfers affine independence to almost every projected law -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d n : ℕ}

theorem independent_difference_tuple_measurable :
    MeasurableSet {z : Space d × (Fin (n+1) → Space d) |
      LinearIndependent ℝ (fun i => z.2 i-z.1)} := by
  apply isOpen_setOfPred_linearIndependent.measurableSet.preimage
  exact (continuous_pi (fun i => ((continuous_apply i).comp continuous_snd).sub
    continuous_fst)).measurable

theorem projected_independent_tuple_measurable :
    MeasurableSet {q : (Space d × (Fin (n+1) → Space d)) × (Fin (n+1) → Space d) |
      LinearIndependent ℝ (fun i => gaussianRowMap q.2 (q.1.2 i-q.1.1))} := by
  apply isOpen_setOfPred_linearIndependent.measurableSet.preimage
  apply Continuous.measurable
  apply continuous_pi
  intro i
  change Continuous (fun q : (Space d × (Fin (n+1) → Space d)) × (Fin (n+1) → Space d) =>
    WithLp.toLp 2 (fun j => inner ℝ (q.2 j) (q.1.2 i-q.1.1)))
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro j
  exact ((continuous_apply j).comp continuous_snd).inner
    (((continuous_apply i).comp (continuous_snd.comp continuous_fst)).sub
      (continuous_fst.comp continuous_fst))

theorem gaussian_projected_tuple_independent_ae (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (hnull : ∀ p : Space d, ∀ V : Submodule ℝ (Space d), Module.finrank ℝ V ≤ n →
      μ {x | x-p ∈ V} = 0) :
    ∀ᵐ A : Fin (n+1) → Space d ∂gaussianRows d (n+1),
      ∀ᵐ z : Space d × (Fin (n+1) → Space d) ∂μ.prod (Measure.pi (fun _ => μ)),
        LinearIndependent ℝ (fun i => gaussianRowMap A (z.2 i-z.1)) := by
  have ho : ∀ᵐ z : Space d × (Fin (n+1) → Space d) ∂μ.prod (Measure.pi (fun _ => μ)),
      LinearIndependent ℝ (fun i => z.2 i-z.1) := by
    apply (Measure.ae_prod_iff_ae_ae independent_difference_tuple_measurable).mpr
    exact Filter.Eventually.of_forall (affine_null_differences_independent_ae μ hnull)
  apply (Measure.ae_ae_comm projected_independent_tuple_measurable).mp
  filter_upwards [ho] with z hz
  exact gaussian_preserves_independent_family _ hz

end Falconer

end OAI
