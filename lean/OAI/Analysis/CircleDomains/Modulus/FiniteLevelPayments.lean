import OAI.Analysis.CircleDomains.Selection.AtomicLevelFiniteness
import OAI.Analysis.CircleDomains.Sobolev.CoareaLevels

namespace OAI

/-! Finite physical and atomic payments pass to independent finite level
tuples, including tuples with repeated labels. -/

open Set Function MeasureTheory
open scoped ENNReal

namespace CircleDomainRigidity

theorem ae_finite_lintegral_level_union
    {X T J Λ : Type*} [MeasurableSpace X] [MeasurableSpace T] [Fintype J]
    (μ : Measure X) (ν : Measure T) [SigmaFinite ν]
    (A : Λ → T → Set X) (g : X → ℝ≥0∞) (labels : J → Λ)
    (hfinite : ∀l, ∀ᵐt ∂ν, (∫⁻x in A l t, g x ∂μ) < ∞) :
    ∀ᵐθ ∂Measure.pi (fun _ : J => ν),
      (∫⁻x in ⋃j, A (labels j) (θ j), g x ∂μ) < ∞ := by
  have hcoordinate (j : J) : ∀ᵐθ ∂Measure.pi (fun _ : J => ν),
      (∫⁻x in A (labels j) (θ j), g x ∂μ) < ∞ :=
    (Measure.quasiMeasurePreserving_eval (fun _ : J => ν) j).ae (hfinite (labels j))
  filter_upwards [ae_all_iff.mpr hcoordinate] with θ hθ
  apply lt_of_le_of_lt (lintegral_iUnion_le _ _)
  rw [tsum_fintype]
  exact ENNReal.sum_lt_top.mpr fun j _ => hθ j

end CircleDomainRigidity

end OAI
