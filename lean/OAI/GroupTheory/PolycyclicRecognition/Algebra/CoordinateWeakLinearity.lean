import OAI.GroupTheory.PolycyclicRecognition.Algebra.WeakDirectionalLinearity

namespace OAI

/-! # Almost-everywhere additivity of actual horizontal flow derivatives -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory
open scoped NNReal ContDiff

theorem ae_horizontalFlowDeriv_add
    {H V W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (m : V → V → V) (hg : PolynomialGroupLaws m)
    (hm : ContDiff ℝ ∞ (fun z : V × V => m z.1 z.2))
    (μ : Measure (PolynomialCoordinateGroup m hg))
    [SFinite μ] [IsFiniteMeasureOnCompacts μ] [μ.IsMulRightInvariant]
    (f : V → W) (hf : Continuous f) (Ω : Set V) (hΩ : IsOpen Ω)
    (D : H →L[ℝ] V) (C : H → ℝ≥0)
    (hlip : ∀ v g, LipschitzOnWith (C v) (fun t : ℝ => f (m g (t • D v)))
      {t | m g (t • D v) ∈ Ω})
    (v w : H) : ∀ᵐ (g : V) ∂μ, g ∈ Ω →
      coordinateFlowDeriv m f (D (v + w)) g =
        coordinateFlowDeriv m f (D v) g + coordinateFlowDeriv m f (D w) g := by
  let : IsFiniteMeasureOnCompacts (show Measure V from μ) :=
    inferInstanceAs (IsFiniteMeasureOnCompacts μ)
  have hY : Continuous (fun g => fderiv ℝ (m g) 0) :=
    Continuous.fderiv (f := m) hm continuous_const (by simp)
  exact ae_add_of_weak_directional_derivatives (show Measure V from μ) Ω hΩ
    (fun u => coordinateFlowDeriv m f (D u))
    (fun u => locallyIntegrableOn_coordinateFlowDeriv (show Measure V from μ)
      m hm.continuous hg.2.2.1 f hf Ω hΩ (D u) (C u) (hlip u))
    (fun g => (fderiv ℝ (m g) 0).comp D) (hY.clm_comp continuous_const) f hf
    (fun u φ hφ hcφ hsφ => coordinate_flow_integration_by_parts m hg hm μ
      f hf Ω hΩ (D u) (C u) (hlip u) φ hφ hcφ hsφ) v w

end PolycyclicRecognition

end

end OAI
