import OAI.Analysis.RCDHeat.HeatFisher

namespace OAI

/-! # Passing compact subtype tests to the original local L2 pairing -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem local_L2_pairing_limit_of_subtype_tests {s : Set X} (hs : MeasurableSet s)
    (hfin : μ s ≠ ∞) (H : ℕ → ℝ → X → ℝ) (G : ℝ → X → ℝ) (δ : ℝ)
    (hc : ∀ ψ : ℝ → ℝ, Integrable ψ (volume.restrict (Ioo δ 1)) →
      ∀ φ : s → ℝ, Integrable φ (μ.comap Subtype.val) →
        Tendsto (fun k => ∫ t in Ioo δ 1, ψ t*∫ x : s, φ x*H k t x ∂μ.comap Subtype.val)
          atTop (𝓝 (∫ t in Ioo δ 1, ψ t*∫ x : s, φ x*G t x ∂μ.comap Subtype.val))) :
    ∀ ψ : ℝ → ℝ, Integrable ψ (volume.restrict (Ioo δ 1)) → ∀ v : Lp ℝ 2 μ,
      Tendsto (fun k => ∫ t in Ioo δ 1, ψ t*∫ x in s, v x*H k t x ∂μ)
        atTop (𝓝 (∫ t in Ioo δ 1, ψ t*∫ x in s, v x*G t x ∂μ)) := by
  intro ψ hψ v
  have hv : IntegrableOn v s μ := lp_integrableOn_of_finite μ v s hfin
  have hv' : Integrable (fun x : s => v x) (μ.comap Subtype.val) :=
    (integrableOn_iff_comap_subtypeVal hs).mp hv
  have hh := hc ψ hψ (fun x => v x) hv'
  have hf (k : ℕ) (t : ℝ) :
      (∫ x : s, v x*H k t x ∂μ.comap Subtype.val) = ∫ x in s, v x*H k t x ∂μ :=
    integral_subtype_comap hs (fun x => v x*H k t x)
  have hg (t : ℝ) : (∫ x : s, v x*G t x ∂μ.comap Subtype.val) = ∫ x in s, v x*G t x ∂μ :=
    integral_subtype_comap hs (fun x => v x*G t x)
  simpa only [hf,hg] using hh

end RegularPointCoordinates

end

end OAI
