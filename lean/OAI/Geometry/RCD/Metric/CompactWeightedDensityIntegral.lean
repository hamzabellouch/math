import OAI.Geometry.RCD.Metric.CompactFactorExtension
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! # The compact-factor integral is the integral of its actual density

An endpoint law supported on a compact set is used through its exact
pushforward density. This identifies the heat factors with integrals
against bounded, compactly supported functions on the original space.
-/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
theorem compact_weighted_density_integral {S : Set X} (hS : MeasurableSet S)
    (μ : Measure X) (ν : Measure S) (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hν : ν.map Subtype.val = μ.withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : C(S, ℝ)) (k : X → ℝ) :
    (∫ a, k a*F a ∂ν) = ∫ x, k x*(ρ x*compactFactorExtension F x) ∂μ := by
  have he := (MeasurableEmbedding.subtype_coe hS).integral_map
    (μ := ν) (fun x => k x*compactFactorExtension F x)
  rw [hν,integral_withDensity_eq_integral_toReal_smul hρ.ennreal_ofReal
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)] at he
  simp only [ENNReal.toReal_ofReal (hρ0 _),smul_eq_mul,compactFactorExtension_coe] at he
  calc
    _ = ∫ x, ρ x*(k x*compactFactorExtension F x) ∂μ := he.symm
    _ = _ := integral_congr_ae (Eventually.of_forall fun x => by ring)

end RegularPointCoordinates

end

end OAI
