import OAI.Analysis.CircleDomains.Probability.PhysicalSliceOccupation
import OAI.Analysis.CircleDomains.Sobolev.SmoothCurveImage
import OAI.Analysis.CircleDomains.Sobolev.SmoothPathIntersections
import OAI.Analysis.CircleDomains.Probability.AffinePhysicalOccupation
import OAI.Analysis.CircleDomains.Topology.IntervalPath
import Mathlib.Analysis.Calculus.FDeriv.Measurable

namespace OAI

/-! Weighted local chart estimates for actual quotient paths. The inverse
chart distortion is kept explicit; the length is the existing physical
occupation, with its original parameter multiplicity. -/

open Set Function MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

theorem physical_chart_length_measure_le (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (π : Y → X) (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Y) {A : Set ℂ} (hA : MapsTo φ A G)
    (j : Y → ℂ) (hjm : Measurable j) (hj : ∀ z ∈ A, j (φ z) = z)
    (B : ℝ≥0) (hB : LipschitzOnWith B j (φ '' A))
    (hφA : MeasurableSet (φ '' A)) (γ : FinitePhysicalPath e y₀) :
    (μH[1] : Measure ℂ).restrict (A ∩ (π ∘ φ) ⁻¹' range γ.val) ≤
      (B : ℝ≥0∞) • ((dyadicPhysicalOccupation e y₀ γ).restrict (φ '' A)).map j := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.restrict_apply hS, Measure.smul_apply, Measure.map_apply hjm hS,
    Measure.restrict_apply (hjm hS), smul_eq_mul]
  let E := S ∩ (A ∩ (π ∘ φ) ⁻¹' range γ.val)
  have hEA : E ⊆ A := fun _ h => h.2.1
  have hid : j '' (φ '' E) = E := by
    ext w
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      rwa [hj z (hEA hz)]
    · intro hw
      exact ⟨φ w, ⟨w, hw, rfl⟩, hj w (hEA hw)⟩
  calc
    (μH[1] : Measure ℂ) E = (μH[1] : Measure ℂ) (j '' (φ '' E)) := congrArg _ hid.symm
    _ ≤ (B : ℝ≥0∞) * (μH[1] : Measure Y) (φ '' E) := by
      simpa only [ENNReal.rpow_one] using
        (hB.mono (image_mono hEA)).hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1)
    _ ≤ (B : ℝ≥0∞) * dyadicPhysicalOccupation e y₀ γ (j ⁻¹' S ∩ φ '' A) := by
      apply mul_le_mul' le_rfl
      calc
        (μH[1] : Measure Y) (φ '' E) ≤ (μH[1] : Measure Y)
            ((j ⁻¹' S ∩ φ '' A) ∩ ((physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U))) := by
          apply measure_mono
          rintro _ ⟨z, hz, rfl⟩
          refine ⟨⟨?_, ⟨z, hEA hz, rfl⟩⟩, ?_⟩
          · change j (φ z) ∈ S
            rw [hj z (hEA hz)]
            exact hz.1
          · exact physical_chart_image_subset e y₀ π he φ hA γ.val ⟨z, hz.2, rfl⟩
        _ = ((μH[1] : Measure Y).restrict
            ((physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U))) (j ⁻¹' S ∩ φ '' A) :=
          (Measure.restrict_apply ((hjm hS).inter hφA)).symm
        _ ≤ _ := physical_image_hausdorff_le_occupation e hU y₀ γ _

theorem physical_chart_lintegral_le (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (π : Y → X) (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Y) {A : Set ℂ} (hA : MapsTo φ A G)
    (j : Y → ℂ) (hjm : Measurable j) (hj : ∀ z ∈ A, j (φ z) = z)
    (B : ℝ≥0) (hB : LipschitzOnWith B j (φ '' A))
    (hφA : MeasurableSet (φ '' A)) (γ : FinitePhysicalPath e y₀)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ z in A ∩ (π ∘ φ) ⁻¹' range γ.val, g z ∂(μH[1] : Measure ℂ)) ≤
      (B : ℝ≥0∞) * ∫⁻ y in φ '' A, g (j y) ∂dyadicPhysicalOccupation e y₀ γ := by
  have h := lintegral_mono'
    (physical_chart_length_measure_le e hU y₀ π he φ hA j hjm hj B hB hφA γ)
    (fun z => le_refl (g z))
  rwa [lintegral_smul_measure, lintegral_map hg hjm, smul_eq_mul] at h

theorem smooth_physical_chart_image_le (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (π : Y → X) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Y) (hφ : Continuous φ) {A D : Set ℂ} (hA : MeasurableSet A)
    (hφA : MeasurableSet (φ '' A)) (hAG : MapsTo φ A G) (hAD : A ⊆ D) (hD : IsOpen D)
    (j : Y → ℂ) (hjm : Measurable j) (hj : ∀ z ∈ A, j (φ z) = z)
    (B : ℝ≥0) (hB : LipschitzOnWith B j (φ '' A))
    (γ : FinitePhysicalPath e y₀) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    volume (f '' (A ∩ (π ∘ φ) ⁻¹' range γ.val)) ≤
      (B : ℝ≥0∞) * ∫⁻ y in φ '' A, ENNReal.ofReal ‖fderiv ℝ f (j y)‖
        ∂dyadicPhysicalOccupation e y₀ γ := by
  have hlen := compact_chart_length_le_occupation e hU y₀ π he φ hAG j hj B hB hφA γ
  have hfin : (μH[1] : Measure ℂ) (A ∩ (π ∘ φ) ⁻¹' range γ.val) < ∞ := by
    apply hlen.trans_lt
    apply ENNReal.mul_lt_top ENNReal.coe_lt_top
    rw [physicalOccupationCode_eq e y₀ γ]
    exact (measure_mono (subset_univ _)).trans_lt (by
      rw [dyadicPhysicalOccupation_univ]
      exact γ.property)
  have hE := hA.inter
    (((isCompact_range γ.val.continuous).isClosed.preimage (hπ.comp hφ)).measurableSet)
  exact (smooth_curve_image_bound hD hE
    (inter_subset_left.trans hAD) hfin hf).trans
      (physical_chart_lintegral_le e hU y₀ π he φ hAG j hjm hj B hB hφA γ
        (fun z => ENNReal.ofReal ‖fderiv ℝ f z‖)
        (measurable_fderiv ℝ f).norm.ennreal_ofReal)

/-- The same weighted estimate for the actual quotient-coordinate image. -/
theorem quotient_smooth_image_le_physical (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (π : Y → X) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Y) (hφ : Continuous φ) {A D : Set ℂ} (hA : MeasurableSet A)
    (hφA : MeasurableSet (φ '' A)) (hAG : MapsTo φ A G) (hAD : A ⊆ D) (hD : IsOpen D)
    (j : Y → ℂ) (hjm : Measurable j) (hj : ∀ z ∈ A, j (φ z) = z)
    (B : ℝ≥0) (hB : LipschitzOnWith B j (φ '' A))
    (γ : FinitePhysicalPath e y₀) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    (F : X → ℝ) (Q : Set X) (hF : ∀ z ∈ A, F (π (φ z)) = f z)
    (hcover : ∀ x ∈ range γ.val ∩ Q, ∃ z ∈ A, π (φ z) = x) :
    volume (F '' (range γ.val ∩ Q)) ≤
      (B : ℝ≥0∞) * ∫⁻ y in φ '' A, ENNReal.ofReal ‖fderiv ℝ f (j y)‖
        ∂dyadicPhysicalOccupation e y₀ γ := by
  apply (measure_mono ?_).trans
    (smooth_physical_chart_image_le e hU y₀ π hπ he φ hφ hA hφA hAG hAD hD j hjm hj B hB γ hf)
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨z, hz, hzx⟩ := hcover x hx
  exact ⟨z, ⟨hz, by change π (φ z) ∈ range γ.val; rw [hzx]; exact hx.1⟩, (hF z hz).symm.trans (congrArg F hzx)⟩

theorem smooth_physical_chart_circle_count_le
    (hcoarea : PlanarLipschitzFiberCoarea)
    (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (π : Y → X) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Y) (hφ : Continuous φ) {A D : Set ℂ} (hA : MeasurableSet A)
    (hφA : MeasurableSet (φ '' A)) (hAG : MapsTo φ A G) (hAD : A ⊆ D) (hD : IsOpen D)
    (j : Y → ℂ) (hjm : Measurable j) (hj : ∀ z ∈ A, j (φ z) = z)
    (B : ℝ≥0) (hB : LipschitzOnWith B j (φ '' A))
    (γ : FinitePhysicalPath e y₀) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    (∫⁻ t in Ico (0 : ℝ) 1,
      pathImageCount ((π ∘ φ) '' (A ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)})) γ.val) ≤
      (B : ℝ≥0∞) * ∫⁻ y in φ '' A, ENNReal.ofReal ‖fderiv ℝ f (j y)‖
        ∂dyadicPhysicalOccupation e y₀ γ := by
  let E := A ∩ (π ∘ φ) ⁻¹' range γ.val
  have hE : MeasurableSet E := hA.inter
    (((isCompact_range γ.val.continuous).isClosed.preimage (hπ.comp hφ)).measurableSet)
  have hlen := compact_chart_length_le_occupation e hU y₀ π he φ hAG j hj B hB hφA γ
  have hfin : (μH[1] : Measure ℂ) E < ∞ := by
    apply hlen.trans_lt
    apply ENNReal.mul_lt_top ENNReal.coe_lt_top
    rw [physicalOccupationCode_eq e y₀ γ]
    exact (measure_mono (subset_univ _)).trans_lt (by
      rw [dyadicPhysicalOccupation_univ]
      exact γ.property)
  have hpoint (t : ℝ) := pathImageCount_image_le_hausdorffZero (π ∘ φ)
    (A ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)}) γ.val
  have hcount := lintegral_mono hpoint (μ := volume.restrict (Ico (0 : ℝ) 1))
  have heq (t : ℝ) :
      (A ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)}) ∩
        (π ∘ φ) ⁻¹' range γ.val =
      E ∩ {z | (f z : UnitAddCircle) = (t : UnitAddCircle)} := by
    ext z
    simp only [E, mem_inter_iff]
    tauto
  simp_rw [heq] at hcount
  exact hcount.trans ((smooth_curve_mod_one_coarea_bound hcoarea hD hE
    (inter_subset_left.trans hAD) hfin hf).trans
      (physical_chart_lintegral_le e hU y₀ π he φ hAG j hjm hj B hB hφA γ
        (fun z => ENNReal.ofReal ‖fderiv ℝ f z‖)
        (measurable_fderiv ℝ f).norm.ennreal_ofReal))

variable [MeasurableSpace X] [BorelSpace X]

theorem quotient_smooth_interval_image_le_physical
    (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (π : Y → X) (hπ : Continuous π) (he : ∀ y : G, (e y).val = π y.val)
    (φ : ℂ → Y) (hφ : Continuous φ) {A D : Set ℂ} (hA : MeasurableSet A)
    (hφA : MeasurableSet (φ '' A)) (hAG : MapsTo φ A G) (hAD : A ⊆ D) (hD : IsOpen D)
    (j : Y → ℂ) (hjm : Measurable j) (hj : ∀ z ∈ A, j (φ z) = z)
    (B : ℝ≥0) (hB : LipschitzOnWith B j (φ '' A))
    (γ : FinitePhysicalPath e y₀) {r s : PathTime} (hrs : r < s)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    (F : X → ℝ) (Q : Set X) (hF : ∀ z ∈ A, F (π (φ z)) = f z)
    (hcover : ∀ x ∈ γ.val '' Icc r s ∩ Q, ∃ z ∈ A, π (φ z) = x) :
    volume (F '' (γ.val '' Icc r s ∩ Q)) ≤
      ∫⁻ t in Icc r s, (B : ℝ≥0∞) * (φ '' A).indicator
        (fun y => ENNReal.ofReal ‖fderiv ℝ f (j y)‖) (physicalValue e y₀ (γ.val t))
        ∂physicalTimeLength e y₀ γ := by
  let g : Y → ℝ≥0∞ := fun y => (B : ℝ≥0∞) *
    (φ '' A).indicator (fun y => ENNReal.ofReal ‖fderiv ℝ f (j y)‖) y
  have hg : Measurable g := measurable_const.mul
    ((((measurable_fderiv ℝ f).norm.ennreal_ofReal).comp hjm).indicator hφA)
  have hrange : range (affineFinitePhysicalPath e hU y₀ γ hrs).val = γ.val '' Icc r s :=
    intervalPath_range γ.val hrs
  have hp := quotient_smooth_image_le_physical e hU y₀ π hπ he φ hφ hA hφA
    hAG hAD hD j hjm hj B hB (affineFinitePhysicalPath e hU y₀ γ hrs) hf F Q hF
    (by simpa only [hrange] using hcover)
  rw [hrange] at hp
  have heq : (∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀
      (affineFinitePhysicalPath e hU y₀ γ hrs)) =
      (B : ℝ≥0∞) * ∫⁻ y in φ '' A, ENNReal.ofReal ‖fderiv ℝ f (j y)‖
        ∂dyadicPhysicalOccupation e y₀ (affineFinitePhysicalPath e hU y₀ γ hrs) := by
    rw [show g = fun y => (B : ℝ≥0∞) *
      (φ '' A).indicator (fun y => ENNReal.ofReal ‖fderiv ℝ f (j y)‖) y from rfl,
      lintegral_const_mul' _ _ ENNReal.coe_ne_top, lintegral_indicator hφA]
  rw [← heq, physicalCost_affine e hU y₀ γ hrs g hg] at hp
  exact hp

end CircleDomainRigidity

end

end OAI
