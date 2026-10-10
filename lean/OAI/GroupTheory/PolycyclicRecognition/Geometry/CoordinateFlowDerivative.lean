import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothFlowTest
import Mathlib.Analysis.Calculus.Deriv.CompMul

namespace OAI

/-! # Weak derivatives in smooth polynomial group coordinates -/

noncomputable section

namespace PolycyclicRecognition

open Set MeasureTheory
open scoped NNReal ContDiff

def coordinateFlowDeriv {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (m : V → V → V) (f : V → W) (v g : V) : W :=
  deriv (fun t : ℝ => f (m g (t • v))) 0

theorem coordinateFlowDeriv_smul {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (m : V → V → V) (f : V → W) (c : ℝ) (v g : V) :
    coordinateFlowDeriv m f (c • v) g = c • coordinateFlowDeriv m f v g := by
  have heq : (fun t : ℝ => f (m g (t • (c • v)))) =
      (fun t : ℝ => f (m g ((c * t) • v))) := by
    funext t
    rw [smul_smul, mul_comm]
  unfold coordinateFlowDeriv
  rw [heq]
  simpa only [mul_zero] using deriv_comp_mul_left c (fun t : ℝ => f (m g (t • v))) 0

theorem stronglyMeasurable_coordinateFlowDeriv {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (m : V → V → V) (hm : Continuous (fun z : V × V => m z.1 z.2))
    (f : V → W) (hf : Continuous f) (v : V) :
    StronglyMeasurable (coordinateFlowDeriv m f v) := by
  have hc : Continuous (fun z : V × ℝ => f (m z.1 (z.2 • v))) :=
    hf.comp (hm.comp (continuous_fst.prodMk (continuous_snd.smul continuous_const)))
  exact (stronglyMeasurable_deriv_with_param
    (f := fun g t => f (m g (t • v))) hc).comp_measurable
    (measurable_id.prodMk (measurable_const (a := (0 : ℝ))))

theorem norm_coordinateFlowDeriv_le {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (m : V → V → V) (hm : Continuous (fun z : V × V => m z.1 z.2))
    (hm0 : ∀ g, m g 0 = g) (f : V → W) (Ω : Set V) (hΩ : IsOpen Ω)
    (v : V) (C : ℝ≥0)
    (hlip : ∀ g, LipschitzOnWith C (fun t : ℝ => f (m g (t • v)))
      {t | m g (t • v) ∈ Ω}) {g : V} (hg : g ∈ Ω) :
    ‖coordinateFlowDeriv m f v g‖ ≤ C := by
  apply norm_deriv_le_of_lipschitzOn _ (hlip g)
  apply (hΩ.preimage (hm.comp (continuous_const.prodMk
    (continuous_id.smul continuous_const)))).mem_nhds
  simpa [hm0] using hg

theorem locallyIntegrableOn_coordinateFlowDeriv {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (μ : Measure V) [IsFiniteMeasureOnCompacts μ]
    (m : V → V → V) (hm : Continuous (fun z : V × V => m z.1 z.2))
    (hm0 : ∀ g, m g 0 = g) (f : V → W) (hf : Continuous f)
    (Ω : Set V) (hΩ : IsOpen Ω) (v : V) (C : ℝ≥0)
    (hlip : ∀ g, LipschitzOnWith C (fun t : ℝ => f (m g (t • v)))
      {t | m g (t • v) ∈ Ω}) : LocallyIntegrableOn (coordinateFlowDeriv m f v) Ω μ := by
  apply (locallyIntegrableOn_iff hΩ.isLocallyClosed).mpr
  intro K hKΩ hK
  apply IntegrableOn.of_bound hK.measure_lt_top
    (stronglyMeasurable_coordinateFlowDeriv m hm f hf v).aestronglyMeasurable.restrict C
  filter_upwards [ae_restrict_mem hK.measurableSet] with g hg
  exact norm_coordinateFlowDeriv_le m hm hm0 f Ω hΩ v C hlip (hKΩ hg)

theorem coordinate_flow_integration_by_parts
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (m : V → V → V) (hg : PolynomialGroupLaws m)
    (hm : ContDiff ℝ ∞ (fun z : V × V => m z.1 z.2))
    (μ : Measure (PolynomialCoordinateGroup m hg))
    [SFinite μ] [IsFiniteMeasureOnCompacts μ] [μ.IsMulRightInvariant]
    (f : V → W) (hf : Continuous f) (Ω : Set V) (hΩ : IsOpen Ω)
    (v : V) (C : ℝ≥0)
    (hlip : ∀ g, LipschitzOnWith C (fun t : ℝ => f (m g (t • v)))
      {t | m g (t • v) ∈ Ω})
    (φ : V → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hsφ : tsupport φ ⊆ Ω) :
    (∫ g, φ g • coordinateFlowDeriv m f v g ∂μ) =
      -(∫ g, fderiv ℝ φ g ((fderiv ℝ (m g) 0) v) • f g ∂μ) := by
  let G := PolynomialCoordinateGroup m hg
  let e : V ≃ₜ G := PolynomialCoordinateGroup.expHomeomorph m hg
  let : IsTopologicalGroup G := PolynomialCoordinateGroup.isTopologicalGroup m hg hm.continuous
  let : SecondCountableTopology G := e.symm.isOpenEmbedding.secondCountableTopology
  let : T2Space G := e.symm.isEmbedding.t2Space
  obtain ⟨dφ, hdφ, hd, hd0⟩ := exists_smooth_flow_test_derivative m hm hg.2.2.1 φ hφ v
  have h := integral_flowDeriv_smul_eq (G := G) μ e e.continuous (by rfl)
    (PolynomialCoordinateGroup.exp_add_smul m hg) v f hf Ω hΩ C hlip
    φ hφ.continuous hcφ hsφ dφ hdφ hd
  change (∫ g : V, φ g • coordinateFlowDeriv m f v g ∂μ) = ∫ g : V, dφ 0 g • f g ∂μ at h
  calc
    _ = ∫ g : V, dφ 0 g • f g ∂μ := h
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with g
      exact (congrArg (fun x : ℝ => x • f (show V from g))
        (hd0 (show V from g))).trans (neg_smul _ _)

end PolycyclicRecognition

end

end OAI
