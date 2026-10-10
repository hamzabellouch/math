import OAI.Probability.SLE.Gauge.RibbonHistoryAdvance
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

namespace OAI

/-! An escaping terminal straight piece makes the complete normal ribbon
proper. Its inverse coordinates therefore extend continuously to the
ambient plane, supplying one actual adapted front process for iteration. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.RibbonCoordinates

lemma closedRibbon_isClosed : IsClosed closedRibbon :=
  (isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_le Complex.continuous_im.abs continuous_const)

lemma ribbon_coordinate_norm_bound
    (P : ℂ → ℂ) (σ : ℝ → ℂ) (T : ℝ) (_hT : 0 ≤ T) (a : ℂ)
    (htail : ∀ t : ℝ, T ≤ t → σ t = a + ((t - T : ℝ) : ℂ) * Complex.I)
    (hwidth : ∀ z ∈ closedRibbon, ‖P z - σ z.re‖ ≤ 1)
    (z : ℂ) (hz : z ∈ closedRibbon) :
    ‖z‖ ≤ T + |a.im| + ‖P z‖ + 2 := by
  have hre : z.re ≤ T + |a.im| + ‖P z‖ + 1 := by
    by_cases hzt : z.re ≤ T
    · linarith [abs_nonneg a.im, norm_nonneg (P z)]
    · have him : z.re - T + a.im = (σ z.re).im := by
        rw [htail z.re (le_of_not_ge hzt)]
        simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
        ring
      have hσ : ‖σ z.re‖ ≤ ‖P z‖ + 1 := by
        calc
          _ ≤ ‖P z‖ + ‖σ z.re - P z‖ := norm_le_insert' _ _
          _ ≤ _ := add_le_add le_rfl (by simpa only [norm_sub_rev] using hwidth z hz)
      have hh := Complex.im_le_norm (σ z.re)
      rw [← him] at hh
      linarith [neg_abs_le a.im]
  have hn := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_nonneg hz.1] at hn
  linarith [hz.2, abs_nonneg a.im, norm_nonneg (P z)]

theorem ribbon_closedEmbedding_of_linear_tail
    (P : ℂ → ℂ) (hP : ContinuousOn P closedRibbon) (hi : InjOn P closedRibbon)
    (σ : ℝ → ℂ) (T : ℝ) (hT : 0 ≤ T) (a : ℂ)
    (htail : ∀ t : ℝ, T ≤ t → σ t = a + ((t - T : ℝ) : ℂ) * Complex.I)
    (hwidth : ∀ z ∈ closedRibbon, ‖P z - σ z.re‖ ≤ 1) :
    Topology.IsClosedEmbedding (fun z : closedRibbon => P z) := by
  have hc : Continuous (fun z : closedRibbon => P z) := hP.domRestrict
  have hinj : Function.Injective (fun z : closedRibbon => P z) := by
    intro z w he
    exact Subtype.ext (hi z.2 w.2 he)
  have hproper : IsProperMap (fun z : closedRibbon => P z) := by
    apply isProperMap_iff_isCompact_preimage.mpr
    refine ⟨hc, fun K hK => ?_⟩
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    have hclosed : IsClosed (closedRibbon ∩ P ⁻¹' K) :=
      hP.preimage_isClosed_of_isClosed closedRibbon_isClosed hK.isClosed
    have hbounded : Bornology.IsBounded (closedRibbon ∩ P ⁻¹' K) := by
      apply isBounded_iff_forall_norm_le.mpr
      refine ⟨T + |a.im| + R + 2, fun z hz => ?_⟩
      exact (ribbon_coordinate_norm_bound P σ T hT a htail hwidth z hz.1).trans
        (by linarith [hR (P z) hz.2])
    apply Subtype.isCompact_iff.mpr
    have he : (Subtype.val '' ((fun z : closedRibbon => P z) ⁻¹' K)) =
        closedRibbon ∩ P ⁻¹' K := by
      ext z
      simp only [mem_image, mem_preimage, mem_inter_iff]
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w.2, hw⟩
      · rintro ⟨hz, hPz⟩
        exact ⟨⟨z, hz⟩, hPz, rfl⟩
    rw [he]
    exact (isCompact_iff_isClosed_bounded).mpr ⟨hclosed, hbounded⟩
  exact .of_continuous_injective_isClosedMap hc hinj hproper.isClosedMap

lemma coordinateInverse_continuousOn_of_embedding
    (P : ℂ → ℂ) (he : Topology.IsEmbedding (fun z : closedRibbon => P z)) :
    ContinuousOn (coordinateInverse P closedRibbon) (P '' closedRibbon) := by
  let q : (P '' closedRibbon) → closedRibbon := fun z =>
    ⟨coordinateInverse P closedRibbon z, coordinateInverse_mem z.2⟩
  have hq : Continuous q := by
    apply he.continuous_iff.mpr
    have hf : (fun z : closedRibbon => P z) ∘ q = Subtype.val := by
      funext z
      exact coordinateInverse_right z.2
    rw [hf]
    exact continuous_subtype_val
  exact continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp hq)

theorem exists_global_ribbon_progress
    (P : ℂ → ℂ) (he : Topology.IsClosedEmbedding (fun z : closedRibbon => P z)) :
    ∃ g : C(ℂ, ℝ), ∀ z ∈ closedRibbon, g (P z) = z.re := by
  have hclosed : IsClosed (P '' closedRibbon) := by
    have hr : range (fun z : closedRibbon => P z) = P '' closedRibbon := by
      ext z
      simp
    exact hr ▸ he.isClosed_range
  have hp : ContinuousOn (longitudinalCoordinate P closedRibbon 0) (P '' closedRibbon) := by
    exact (Complex.continuous_re.comp_continuousOn
      (coordinateInverse_continuousOn_of_embedding P he.isEmbedding)).sub continuousOn_const
  obtain ⟨g, hg⟩ := FrontSuccessMeasurability.exists_continuous_progress_extension
    (longitudinalCoordinate P closedRibbon 0) (P '' closedRibbon) hclosed hp
  have hi : InjOn P closedRibbon := by
    intro z hz w hw heq
    exact congrArg Subtype.val (he.injective (show P (⟨z, hz⟩ : closedRibbon) =
      P (⟨w, hw⟩ : closedRibbon) from heq))
  refine ⟨g, fun z hz => ?_⟩
  rw [← hg (mem_image_of_mem P hz), longitudinalCoordinate, coordinateInverse_left hi hz, sub_zero]

end SLEExactGauge.RibbonCoordinates

end

end OAI
