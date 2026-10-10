import OAI.GroupTheory.PolycyclicRecognition.Geometry.MeasurableDerivativeLabels

namespace OAI

/-! # The two segment inequalities give actual measurable horizontal labels -/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory Module
open scoped NNReal ContDiff

theorem exists_measurable_horizontal_profile_label
    {K H V W I B J : Type*} [Fintype K]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    [Fintype I] [Fintype B] [Nonempty B] [Finite J] [Nonempty J] [MeasurableSpace J]
    (m : V → V → V) (hg : PolynomialGroupLaws m)
    (hm : ContDiff ℝ ∞ (fun z : V × V => m z.1 z.2))
    (μ : Measure (PolynomialCoordinateGroup m hg))
    [SFinite μ] [IsFiniteMeasureOnCompacts μ] [μ.IsMulRightInvariant]
    (f : V → W) (hf : Continuous f) (Ω : Set V) (hΩ : IsOpen Ω)
    (D : H →L[ℝ] V) (b : Basis K ℝ H) (C : H → ℝ≥0)
    (hlip : ∀ v g, LipschitzOnWith (C v) (fun t : ℝ => f (m g (t • D v)))
      {t | m g (t • D v) ∈ Ω})
    (P : SupportDatum W I B) (π : H →L[ℝ] W) (hπ : Function.Surjective π)
    (A : J → templateSymmetryGroup P)
    (T : V → H → ℝ) (hT : ∀ z ∈ Ω, ∀ v, 0 < T z v)
    (hinc : ∀ z ∈ Ω, ∀ v, ∀ t, 0 < t → t < T z v →
      t⁻¹ • (f (m z (t • D v)) - f z) ∈ convexHull ℝ (range fun j => (A j).val (π v)))
    (hvol : ∀ z ∈ Ω, ∀ v, ∀ t, 0 < t → t < T z v →
      t * P.segmentSupport (π v) ≤ P.templateSupport ((fun t : ℝ => f (m z (t • D v))) '' Icc 0 t)) :
    ∃ label : V → J, Measurable label ∧ ∀ v, ∀ᵐ (g : V) ∂μ, g ∈ Ω →
      HasDerivAt (fun t : ℝ => f (m g (t • D v))) ((A (label g)).val (π v)) 0 := by
  let q : H → V → W := fun v => coordinateFlowDeriv m f (D v)
  let M : V → H →ₗ[ℝ] W := basisDerivativeField b q
  have hd (v : H) : ∀ᵐ (g : V) ∂μ, g ∈ Ω →
      HasDerivAt (fun t : ℝ => f (m g (t • D v))) (M g v) 0 :=
    ae_horizontal_hasDerivAt_basisField m hg hm μ f hf Ω hΩ D b C hlip v
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense H
  have ha : ∀ᵐ (g : V) ∂μ, g ∈ Ω → ∃ j, M g = (A j).val.toLinearMap.comp π.toLinearMap := by
    apply ae_template_label_of_dense_derivatives (show Measure V from μ) Ω P π hπ A M
      (fun g v t => f (m g (t • D v))) (fun _ _ _ => hf.comp (hm.continuous.comp
        (continuous_const.prodMk (continuous_id.smul continuous_const))))
      S hSc hSd (fun v _ => hd v) T (fun z hz v _ => hT z hz v)
    · intro z hz v _ t ht htT
      simpa only [zero_smul, hg.2.2.1] using hinc z hz v t ht htT
    · intro z hz v _ t ht htT
      exact hvol z hz v t ht htT
  obtain ⟨label, hlabel, hchoose⟩ := exists_measurable_basis_derivative_label b q
    (fun i => (stronglyMeasurable_coordinateFlowDeriv m hm.continuous f hf (D (b i))).measurable)
    (fun j => (A j).val.toLinearMap.comp π.toLinearMap)
  refine ⟨label, hlabel, ?_⟩
  intro v
  filter_upwards [ha, hd v] with g hg hdg hgΩ
  have he := hchoose g (hg hgΩ)
  exact (hdg hgΩ).congr_deriv (LinearMap.congr_fun he v)

end PolycyclicRecognition

end

end OAI
