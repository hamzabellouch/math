import OAI.GroupTheory.PolycyclicRecognition.Geometry.BasisDerivativeField

namespace OAI

/-! # The actual almost-everywhere linear horizontal derivative -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory Module
open scoped NNReal ContDiff

theorem ae_horizontal_hasDerivAt_basisField
    {I H V W : Type*} [Fintype I]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (m : V → V → V) (hg : PolynomialGroupLaws m)
    (hm : ContDiff ℝ ∞ (fun z : V × V => m z.1 z.2))
    (μ : Measure (PolynomialCoordinateGroup m hg))
    [SFinite μ] [IsFiniteMeasureOnCompacts μ] [μ.IsMulRightInvariant]
    (f : V → W) (hf : Continuous f) (Ω : Set V) (hΩ : IsOpen Ω)
    (D : H →L[ℝ] V) (b : Basis I ℝ H) (C : H → ℝ≥0)
    (hlip : ∀ v g, LipschitzOnWith (C v) (fun t : ℝ => f (m g (t • D v)))
      {t | m g (t • D v) ∈ Ω}) (v : H) :
    ∀ᵐ (g : V) ∂μ, g ∈ Ω →
      HasDerivAt (fun t : ℝ => f (m g (t • D v)))
        (basisDerivativeField b (fun u => coordinateFlowDeriv m f (D u)) g v) 0 := by
  have hrepr := ae_eq_basisDerivativeField (show Measure V from μ) Ω b
    (fun u => coordinateFlowDeriv m f (D u))
    (ae_horizontalFlowDeriv_add m hg hm μ f hf Ω hΩ D C hlip)
    (fun c u g => by
      simpa only [map_smul] using coordinateFlowDeriv_smul m f c (D u) g) v
  let G := PolynomialCoordinateGroup m hg
  let e : V ≃ₜ G := PolynomialCoordinateGroup.expHomeomorph m hg
  let : IsTopologicalGroup G := PolynomialCoordinateGroup.isTopologicalGroup m hg hm.continuous
  let : SecondCountableTopology G := e.symm.isOpenEmbedding.secondCountableTopology
  have hd : ∀ᵐ (g : V) ∂μ, g ∈ Ω → HasDerivAt (fun t : ℝ => f (m g (t • D v)))
      (coordinateFlowDeriv m f (D v) g) 0 := by
    exact ae_hasDerivAt_flowDeriv (G := G) μ e e.continuous
      (PolynomialCoordinateGroup.exp_add_smul m hg) (D v) f hf Ω hΩ (C v) (hlip v)
  filter_upwards [hrepr, hd] with g hg hdg hgΩ
  exact (hdg hgΩ).congr_deriv (hg hgΩ)

end PolycyclicRecognition

end

end OAI
