import Mathlib
import OAI.Geometry.CubicTorus.Regularity.BVColumnHeight

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_gradient_norm (g : Plane → ℝ) (y : Plane) :
    ‖gradient g y‖ = ‖fderiv ℝ g y‖ := by
  exact (InnerProductSpace.toDual ℝ Plane).symm.norm_map _

lemma graphAreaVector_norm_sq {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) (y : Plane) :
    ‖graphAreaVector n g y‖ ^ 2 = 1 + ‖fderiv ℝ g y‖ ^ 2 := by
  rw [graphAreaVector, norm_sub_sq_real, hn, one_pow,
    normalPlaneEmbedding_norm, normalPlaneEmbedding_inner hn, plane_gradient_norm]
  ring

lemma graphAreaVector_norm_le {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) (y : Plane) :
    ‖graphAreaVector n g y‖ ≤ 1 + ‖fderiv ℝ g y‖ ^ 2 / 2 := by
  have he := graphAreaVector_norm_sq hn g y
  nlinarith [norm_nonneg (graphAreaVector n g y), sq_nonneg ‖fderiv ℝ g y‖,
    sq_nonneg (‖fderiv ℝ g y‖ ^ 2)]

lemma graph_trace_compactSupport {X : Type*} [Zero X]
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1) {g : Plane → ℝ} (hg : Continuous g)
    {F : Cover → X} (hs : HasCompactSupport F) :
    HasCompactSupport (fun y : Plane ↦ F (a+normalGraph n g y)) := by
  have hc := (hs.comp_homeomorph (graphShearHomeomorph a hn hg)).comp_isClosedEmbedding
    (normalColumnChart_plane_isometry a hn 0).isClosedEmbedding
  have he (y : Plane) : graphShearHomeomorph a hn hg (normalColumnChart a n (0,y)) =
      a+normalGraph n g y := by
    change graphShear a n g (normalColumnChart a n (0,y)) = _
    rw [graphShear_columnChart a hn, zero_add, normalColumnChart_apply a hn]
    rfl
  simpa only [Function.comp_def, he] using hc

lemma graph_trace_continuous {X : Type*} [TopologicalSpace X]
    (a n : Cover) {g : Plane → ℝ} (hg : Continuous g)
    {F : Cover → X} (hF : Continuous F) : Continuous (fun y : Plane ↦ F (a+normalGraph n g y)) := by
  apply hF.comp
  exact continuous_const.add ((normalPlaneLinearIsometry n).continuous.add (hg.smul continuous_const))

lemma graphAreaVector_continuous (n : Cover) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) : Continuous (graphAreaVector n g) := by
  have hd := (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous
  exact continuous_const.sub ((normalPlaneLinearIsometry n).continuous.comp
    ((InnerProductSpace.toDual ℝ Plane).symm.continuous.comp hd))

lemma graph_trace_flux_integrable (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {F : Cover → Cover} (hF : Continuous F) (hs : HasCompactSupport F) :
    Integrable (fun y : Plane ↦ ⟪graphAreaVector n g y, F (a+normalGraph n g y)⟫) := by
  have hc := graph_trace_compactSupport a hn hg.continuous hs
  have hs' : HasCompactSupport (fun y : Plane ↦ ⟪graphAreaVector n g y, F (a+normalGraph n g y)⟫) := by
    apply hc.mono
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro he
    apply hx
    rw [he, inner_zero_right]
  exact ((graphAreaVector_continuous n hg).inner
    (graph_trace_continuous a n hg.continuous hF)).integrable_of_hasCompactSupport hs'

theorem integral_graphSublevel_divergence_le (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hs : HasCompactSupport F)
    {w : Cover → ℝ} (hw : Continuous w) (hws : HasCompactSupport w)
    (hbound : ∀ x, ‖F x‖ ≤ w x) :
    (∫ x : Cover, graphSublevelIndicator a n g x * divergence F x) ≤
      ∫ y : Plane, w (a+normalGraph n g y) * (1+‖fderiv ℝ g y‖ ^ 2 / 2) := by
  rw [integral_graphSublevel_divergence a hn hg hF hs]
  have hcw := graph_trace_continuous a n hg.continuous hw
  have hwc := graph_trace_compactSupport a hn hg.continuous hws
  have hd := (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous
  have hi : Integrable (fun y : Plane ↦ w (a+normalGraph n g y) * (1+‖fderiv ℝ g y‖ ^ 2 / 2)) :=
    (hcw.mul (continuous_const.add ((hd.norm.pow 2).div_const 2))).integrable_of_hasCompactSupport
      hwc.mul_right
  apply integral_mono (graph_trace_flux_integrable a hn hg hF.continuous hs) hi
  intro y
  calc
    _ ≤ ‖graphAreaVector n g y‖ * ‖F (a+normalGraph n g y)‖ := real_inner_le_norm _ _
    _ ≤ (1+‖fderiv ℝ g y‖ ^ 2 / 2) * w (a+normalGraph n g y) :=
      mul_le_mul (graphAreaVector_norm_le hn g y) (hbound _) (norm_nonneg _) (by positivity)
    _ = _ := mul_comm _ _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem cutoff_gluing_local_flux_le {E F : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hp : ∀ n x, w (x + latticeVector n) = w x) (hb : ∀ x, w x ∈ Icc 0 1)
    {X : Cover → Cover} (hX : AdmissibleField X)
    {A : ℝ} (hlocal : (∫ x in fundamentalCube, characteristic F (quotientMap x) *
      divergence (fun y ↦ w y • X y) x) ≤ A) :
    (∫ x in fundamentalCube,
      ((1 - w x) * characteristic E (quotientMap x) + w x * characteristic F (quotientMap x)) *
        divergence X x) ≤
      (∫ z, 1 - w z.1 ∂(μ : Measure NormalBundle)) +
      A +
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E ∆ F), ‖gradient w x‖ := by
  let Y : Cover → Cover := fun x ↦ (1 - w x) • X x
  let Z : Cover → Cover := fun x ↦ w x • X x
  have hY : AdmissibleField Y := admissible_cutoff (contDiff_const.sub hw)
    (fun n x ↦ by rw [hp]) (fun x ↦ by constructor <;> linarith [(hb x).1, (hb x).2]) hX
  have hZ : AdmissibleField Z := admissible_cutoff hw hp hb hX
  let a : Cover → ℝ := fun x ↦ characteristic E (quotientMap x) * divergence Y x
  let b : Cover → ℝ := fun x ↦ characteristic F (quotientMap x) * divergence Z x
  let c : Cover → ℝ := fun x ↦ (characteristic F (quotientMap x) - characteristic E (quotientMap x)) *
    ⟪gradient w x, X x⟫
  have ha : IntegrableOn a fundamentalCube := integrableOn_characteristic_mul hE.nullMeasurableSet
    (integrableOn_divergence hY.1)
  have hb' : IntegrableOn b fundamentalCube := integrableOn_characteristic_mul hF.nullMeasurableSet
    (integrableOn_divergence hZ.1)
  have hi : IntegrableOn (fun x ↦ ⟪gradient w x, X x⟫) fundamentalCube :=
    integrableOn_periodic_continuous ((gradient_contDiff hw).continuous.inner hX.1.continuous)
      (fun n x ↦ by rw [gradient_periodic hp, hX.2.1])
  have hc : IntegrableOn c fundamentalCube := by
    have hh := (integrableOn_characteristic_mul hF.nullMeasurableSet hi).sub
      (integrableOn_characteristic_mul hE.nullMeasurableSet hi)
    simpa only [Pi.sub_def, ← sub_mul, c] using hh
  have hgn : IntegrableOn (fun x ↦ ‖gradient w x‖) fundamentalCube :=
    integrableOn_periodic_continuous (gradient_contDiff hw).continuous.norm
      (fun n x ↦ by rw [gradient_periodic hp])
  have heq (x : Cover) :
      ((1 - w x) * characteristic E (quotientMap x) + w x * characteristic F (quotientMap x)) *
        divergence X x = a x + b x - c x := by
    dsimp [a, b, c, Y, Z]
    rw [divergence_smul_function ((contDiff_const.sub hw).differentiable (by simp)).differentiableAt
      (hX.1.differentiable (by simp)).differentiableAt,
      divergence_smul_function (hw.differentiable (by simp)).differentiableAt
      (hX.1.differentiable (by simp)).differentiableAt,
      gradient_const_sub, inner_neg_left]
    ring
  simp_rw [heq]
  have hab : IntegrableOn (fun x ↦ a x + b x) fundamentalCube := by
    simpa only [Pi.add_def] using ha.add hb'
  rw [integral_sub hab hc, integral_add ha hb']
  have hmassE : (∫ x in fundamentalCube, a x) ≤ ∫ z, 1 - w z.1 ∂(μ : Measure NormalBundle) := by
    dsimp only [a]
    simp_rw [characteristic_mul]
    rw [lift_indicator_integral hE.nullMeasurableSet,
      ← normalMeasure_weighted_flux hμ (contDiff_const.sub hw) (fun n x ↦ by rw [hp]) hX]
    have hh : Continuous (fun z : NormalBundle ↦ 1 - w z.1) := by fun_prop
    apply integral_mono ((hh.mul (normalTest X hX.1.continuous).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
      (hh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    intro z
    exact mul_le_of_le_one_right (by linarith [(hb z.1).2]) (normalTest_le_one hX z)
  have hmassF : (∫ x in fundamentalCube, b x) ≤ A := hlocal
  have herr : -(∫ x in fundamentalCube, c x) ≤
      ∫ x in fundamentalCube ∩ quotientMap ⁻¹' (E ∆ F), ‖gradient w x‖ := by
    rw [← integral_neg, ← lift_indicator_integral (hE.symmDiff hF).nullMeasurableSet]
    have hci := integrableOn_characteristic_mul (hE.symmDiff hF).nullMeasurableSet hgn
    simp_rw [← characteristic_mul] at ⊢ hci
    apply integral_mono hc.neg hci
    intro x
    calc
      -c x ≤ |c x| := neg_le_abs _
      _ = characteristic (E ∆ F) (quotientMap x) * |⟪gradient w x, X x⟫| := by
        dsimp only [c]
        rw [abs_mul, characteristic_symmDiff_abs]
      _ ≤ characteristic (E ∆ F) (quotientMap x) * ‖gradient w x‖ := by
        apply mul_le_mul_of_nonneg_left _ (characteristic_nonneg _ _)
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_of_le_one_right (norm_nonneg _) (hX.2.2 x))
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

def torusGraphRegion (a n : Cover) (g : Plane → ℝ) : Set Torus :=
  {z | ⟪n, representative z - a⟫ < graphHeightExtension a n g (representative z)}

lemma measurableSet_torusGraphRegion (a n : Cover) {g : Plane → ℝ} (hg : Continuous g) :
    MeasurableSet (torusGraphRegion a n g) := by
  apply measurableSet_lt
  · exact measurable_const.inner (measurable_representative.sub_const a)
  · exact (hg.comp ((normalPlaneCoordinates n).continuous.comp
      (continuous_id.sub continuous_const))).measurable.comp measurable_representative

lemma characteristic_torusGraphRegion {x : Cover} (hx : x ∈ fundamentalCube)
    (a n : Cover) (g : Plane → ℝ) :
    characteristic (torusGraphRegion a n g) (quotientMap x) = graphSublevelIndicator a n g x := by
  simp only [characteristic, torusGraphRegion, Set.indicator, Set.mem_ofPred_eq,
    representative_quotientMap_of_mem hx, graphSublevelIndicator]

lemma latticePeriodize_mem_Icc {w : Cover → ℝ} (hc : HasCompactSupport w)
    (hs : tsupport w ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    (hb : ∀ x, w x ∈ Icc 0 1) (x : Cover) : latticePeriodize w x ∈ Icc 0 1 := by
  rw [← periodic_representative (latticePeriodize_periodic w) x]
  have hx := representative_mem_fundamentalCube (quotientMap x)
  rw [(latticePeriodize_eventuallyEq hc hs (fun i ↦ ⟨(hx i).1, (hx i).2.le⟩)).eq_of_nhds]
  exact hb _

lemma interior_cutoff_flux_eq (a n : Cover) (g : Plane → ℝ)
    {w : Cover → ℝ} (hc : HasCompactSupport w)
    (hs : tsupport w ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) (X : Cover → Cover) :
    (∫ x in fundamentalCube, characteristic (torusGraphRegion a n g) (quotientMap x) *
      divergence (fun y ↦ latticePeriodize w y • X y) x) =
      ∫ x : Cover, graphSublevelIndicator a n g x * divergence (fun y ↦ w y • X y) x := by
  rw [← integral_indicator measurableSet_fundamentalCube]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ fundamentalCube
  · rw [indicator_of_mem hx, characteristic_torusGraphRegion hx]
    have he := (latticePeriodize_eventuallyEq hc hs (fun i ↦ ⟨(hx i).1, (hx i).2.le⟩)).smul
      (EventuallyEq.rfl : X =ᶠ[𝓝 x] X)
    have hd := he.fderiv_eq (𝕜 := ℝ)
    simp only [divergence] at hd ⊢
    rw [hd]
  · rw [indicator_of_notMem hx]
    have hsup : tsupport (fun y ↦ w y • X y) ⊆ tsupport w := tsupport_smul_subset_left w X
    have hdiv : divergence (fun y ↦ w y • X y) x = 0 := by
      apply divergence_of_notMem_tsupport
      intro hh
      exact hx (fun i ↦ ⟨(hs (hsup hh) i).1.le, (hs (hsup hh) i).2⟩)
    rw [hdiv, mul_zero]

theorem torusGraphRegion_cutoff_flux_le (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {w : Cover → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hc : HasCompactSupport w)
    (hs : tsupport w ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) (hb : ∀ x, w x ∈ Icc 0 1)
    {X : Cover → Cover} (hX : AdmissibleField X) :
    (∫ x in fundamentalCube, characteristic (torusGraphRegion a n g) (quotientMap x) *
      divergence (fun y ↦ latticePeriodize w y • X y) x) ≤
      ∫ y : Plane, w (a+normalGraph n g y) * (1+‖fderiv ℝ g y‖ ^ 2 / 2) := by
  rw [interior_cutoff_flux_eq a n g hc hs]
  apply integral_graphSublevel_divergence_le a hn hg (hw.smul hX.1)
    (hc.smul_right) hw.continuous hc
  intro x
  change ‖w x • X x‖ ≤ w x
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hb x).1]
  exact mul_le_of_le_one_right (hb x).1 (hX.2.2 x)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem perimeter_glued_local_flux_le {E F : Set Torus}
    (hE : MeasurableSet E) (hF : MeasurableSet F)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {q : Cover → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hp : ∀ n x, q (x + latticeVector n) = q x)
    {K M t d : ℝ} (hK : ∀ u, ‖deriv Real.smoothTransition u‖ ≤ K)
    (hgrad : ∀ x, q x < t → ‖gradient q x‖ ≤ M)
    (hd : HasDerivAt (sublevelVolume (E ∆ F) q) d t)
    {L : ℕ → ℝ} {L₀ : ℝ} (hLlim : Tendsto L atTop (𝓝 L₀))
    (hlocal : ∀ i : ℕ, ∀ X : Cover → Cover, AdmissibleField X →
      (∫ x in fundamentalCube, characteristic F (quotientMap x) *
        divergence (fun y ↦ sublevelCutoff q t (1 / ((i : ℝ)+1)) y • X y) x) ≤ L i) :
    FinitePerimeter (gluedRegion E F (sublevelRegion q t)) ∧
      (perimeter (gluedRegion E F (sublevelRegion q t))).toReal ≤
        (μ.mass : ℝ) - (μ : Measure NormalBundle).real {z | q z.1 < t} +
        L₀ + K * M * d := by
  let ε : ℕ → ℝ := fun i ↦ 1 / ((i : ℝ) + 1)
  have he : ∀ i, 0 < ε i := fun i ↦ by dsimp [ε]; positivity
  have helim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let w : ℕ → Cover → ℝ := fun i ↦ sublevelCutoff q t (ε i)
  have hw (i : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (w i) := sublevelCutoff_contDiff hq t (ε i)
  have hwp (i : ℕ) : ∀ n x, w i (x + latticeVector n) = w i x := sublevelCutoff_periodic hp t (ε i)
  have hwb (i : ℕ) (x : Cover) : w i x ∈ Icc (0 : ℝ) 1 := sublevelCutoff_mem_Icc q t (ε i) x
  have hB := measurableSet_sublevelRegion hq.continuous.measurable t
  have hG := measurableSet_gluedRegion hE hF hB
  let A : ℝ := (μ.mass : ℝ) - (μ : Measure NormalBundle).real {z | q z.1 < t} +
    L₀ + K * M * d
  have hμlim : Tendsto (fun i ↦ ∫ z : NormalBundle, 1 - w i z.1 ∂(μ : Measure NormalBundle))
      atTop (𝓝 ((μ.mass : ℝ) - (μ : Measure NormalBundle).real {z | q z.1 < t})) := by
    have hh := (tendsto_const_nhds (x := (μ.mass : ℝ)) (f := atTop)).sub
      (normalMeasure_sublevelCutoff_tendsto μ hq.continuous hp he helim t)
    convert hh using 1
    funext i
    have hi : Integrable (fun z : NormalBundle ↦ w i z.1) (μ : Measure NormalBundle) :=
      (show Continuous (fun z : NormalBundle ↦ w i z.1) from by fun_prop).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [integral_sub (integrable_const 1) hi, normalMeasure_integral_one]
  have hdlim := tendsto_backward_quotient_of_hasDerivAt hd he helim
  have hright : Tendsto (fun i ↦
      (∫ z : NormalBundle, 1 - w i z.1 ∂(μ : Measure NormalBundle)) +
      L i +
      K * M * ((sublevelVolume (E ∆ F) q t - sublevelVolume (E ∆ F) q (t - ε i)) / ε i))
        atTop (𝓝 A) := (hμlim.add hLlim).add (tendsto_const_nhds.mul hdlim)
  have hbound (X : Cover → Cover) (hX : AdmissibleField X) :
      (∫ x in fundamentalCube ∩ quotientMap ⁻¹' gluedRegion E F (sublevelRegion q t), divergence X x) ≤ A := by
    have hleft := cutoff_gluing_flux_tendsto hE hF hB (fun i ↦ (hw i).continuous) hwb
      (sublevelCutoff_tendsto hp he helim t) hX
    apply le_of_tendsto_of_tendsto' hleft hright
    intro i
    exact (cutoff_gluing_local_flux_le hE hF hμ (hw i) (hwp i) (hwb i) hX (hlocal i X hX)).trans
      (add_le_add_right (sublevelCutoff_gradient_integral_le (hE.symmDiff hF) hq hp hK hgrad (he i)) _)
  have hA : 0 ≤ A := by
    simpa only [divergence_zero, integral_zero] using hbound (fun _ ↦ 0) admissible_zero
  have hb : perimeter (gluedRegion E F (sublevelRegion q t)) ≤ ENNReal.ofReal A := by
    apply iSup_le
    intro X
    apply iSup_le
    intro hX
    exact ENNReal.ofReal_le_ofReal (hbound X hX)
  refine ⟨⟨hG.nullMeasurableSet, hb.trans_lt ENNReal.ofReal_lt_top⟩, ?_⟩
  simpa only [ENNReal.toReal_ofReal hA] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma radialDensityWeight_cell_support {r ε : ℝ} (hr : 0 ≤ r) (hs : r < 1/2) (hε : 0 < ε) :
    tsupport (radialDensityWeight cubeCenter r ε) ⊆ {x | ∀ i, 0 < x i ∧ x i < 1} := by
  intro x hx i
  have hh := radialDensityWeight_tsupport hr hε hx
  have hd : ‖x-cubeCenter‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hh
  have hi := (PiLp.norm_apply_le (x-cubeCenter) i).trans hd
  change ‖x i - (1/2 : ℝ)‖ ≤ r at hi
  rw [Real.norm_eq_abs, abs_le] at hi
  constructor <;> linarith

lemma radialDensityWeight_periodize {r ε : ℝ} (hr : 0 ≤ r) (hs : r < 1/4) (hε : 0 < ε) :
    latticePeriodize (radialDensityWeight cubeCenter r ε) = sublevelCutoff radialSquared (r^2) ε := by
  funext x
  rw [← periodic_representative (latticePeriodize_periodic _) x,
    ← periodic_representative (sublevelCutoff_periodic radialSquared_periodic (r^2) ε) x]
  let z := representative (quotientMap x)
  have hz : z ∈ fundamentalCube := representative_mem_fundamentalCube _
  rw [(latticePeriodize_eventuallyEq (radialDensityWeight_hasCompactSupport hr hε)
    (radialDensityWeight_cell_support hr (by linarith) hε)
    (fun i ↦ ⟨(hz i).1, (hz i).2.le⟩)).eq_of_nhds]
  change radialDensityWeight cubeCenter r ε z = sublevelCutoff radialSquared (r^2) ε z
  by_cases hz' : ‖z-cubeCenter‖ < r
  · have he := (radialSquared_eventuallyEq_norm_sq (hz'.trans hs)).eq_of_nhds
    simp only [radialDensityWeight, sublevelCutoff, he]
  · have hh : ¬ radialSquared z < r^2 := by
      rw [radialSquared_sublevel_iff hz (by nlinarith)]
      have hb : r ≤ ‖z-cubeCenter‖ := le_of_not_gt hz'
      nlinarith [norm_nonneg (z-cubeCenter)]
    rw [radialDensityWeight_zero hr hε (le_of_not_gt hz')]
    exact (Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (le_of_not_gt hh)) hε.le)).symm

lemma graph_trace_energy_integrable (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {w : Cover → ℝ} (hw : Continuous w) (hs : HasCompactSupport w) :
    Integrable (fun y : Plane ↦ w (a+normalGraph n g y) * (1+‖fderiv ℝ g y‖^2/2)) := by
  have hd := (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous
  exact ((graph_trace_continuous a n hg.continuous hw).mul
    (continuous_const.add ((hd.norm.pow 2).div_const 2))).integrable_of_hasCompactSupport
      (graph_trace_compactSupport a hn hg.continuous hs).mul_right

def graphBallQuadraticArea (a n : Cover) (g : Plane → ℝ) (r : ℝ) : ℝ :=
  ∫ y in {y : Plane | a+normalGraph n g y ∈ Metric.ball a r}, 1+‖fderiv ℝ g y‖^2/2

lemma graphBallQuadraticArea_tendsto (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) {r : ℝ} (hr : 0 < r)
    {ε : ℕ → ℝ} (hε : ∀ i, 0 < ε i) (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun i ↦ ∫ y : Plane, radialDensityWeight a r (ε i) (a+normalGraph n g y) *
      (1+‖fderiv ℝ g y‖^2/2)) atTop (𝓝 (graphBallQuadraticArea a n g r)) := by
  have hm : MeasurableSet {y : Plane | a+normalGraph n g y ∈ Metric.ball a r} :=
    Metric.isOpen_ball.measurableSet.preimage (graph_trace_continuous a n hg.continuous
      continuous_id).measurable
  have heps : Tendsto ε atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨hεlim, Eventually.of_forall hε⟩
  have hh := tendsto_integral_of_dominated_convergence
    (bound := fun y : Plane ↦ radialHeightCutoff a r (a+normalGraph n g y) * (1+‖fderiv ℝ g y‖^2/2))
    (F := fun i y ↦ radialDensityWeight a r (ε i) (a+normalGraph n g y) * (1+‖fderiv ℝ g y‖^2/2))
    (f := fun y ↦ (Metric.ball a r).indicator (fun _ : Cover ↦ (1 : ℝ)) (a+normalGraph n g y) *
      (1+‖fderiv ℝ g y‖^2/2))
    (fun i ↦ (graph_trace_energy_integrable a hn hg
      (radialDensityWeight_contDiff a r (ε i)).continuous
      (radialDensityWeight_hasCompactSupport hr.le (hε i))).aestronglyMeasurable)
    (graph_trace_energy_integrable a hn hg (radialDensityWeight_contDiff a (2*r) (3*r^2)).continuous
      (radialDensityWeight_hasCompactSupport (by positivity : 0 ≤ 2*r) (by positivity : 0 < 3*r^2)))
    (fun i ↦ Eventually.of_forall fun y ↦ ?_)
    (Eventually.of_forall fun y ↦ ((radialDensityWeight_tendsto a (a+normalGraph n g y) hr).comp heps).mul
      tendsto_const_nhds)
  · convert hh using 1
    rw [graphBallQuadraticArea, ← integral_indicator hm]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : a+normalGraph n g y ∈ Metric.ball a r <;> simp only [Set.indicator, Set.mem_ofPred_eq, hy, ite_true, ite_false, one_mul, zero_mul]
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (radialDensityWeight_nonneg _ _ _ _) (by positivity))]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    by_cases hy : a+normalGraph n g y ∈ Metric.closedBall a r
    · rw [radialHeightCutoff_one hr hy]
      exact radialDensityWeight_le_one _ _ _ _
    · have hd : r ≤ ‖(a+normalGraph n g y)-a‖ := le_of_lt (by
        simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using hy)
      rw [radialDensityWeight_zero hr.le (hε i) hd]
      exact Real.smoothTransition.nonneg _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma normalMeasure_radial_sublevel (μ : FiniteMeasure NormalBundle) {r : ℝ}
    (hr : 0 ≤ r) (hs : r ≤ 1/4) :
    (μ : Measure NormalBundle).real {z | radialSquared z.1 < r^2} =
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) r) := by
  rw [← cubeBall_eq_metricBall, ← sublevelRegion_radialSquared hr hs]
  change _ = (Measure.map normalProjection (μ : Measure NormalBundle)
    (sublevelRegion radialSquared (r^2))).toReal
  rw [Measure.map_apply normalProjection_continuous.measurable
    (measurableSet_sublevelRegion radialSquared_contDiff.continuous.measurable _)]
  congr 1
  ext z
  exact (mem_sublevelRegion_quotient radialSquared_periodic (r^2) z.1).symm

theorem isMinimizerAt_graph_replacement {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (n : Cover), ‖n‖ = 1 →
      ∀ (g : Plane → ℝ), ContDiff ℝ (⊤ : ℕ∞) g →
      ∀ r K d : ℝ, 0 < r → r < 1/4 → (∀ u, ‖deriv Real.smoothTransition u‖ ≤ K) →
      HasDerivAt (sublevelVolume (E ∆ torusGraphRegion cubeCenter n g) radialSquared) d (r^2) →
      sublevelVolume (E ∆ torusGraphRegion cubeCenter n g) radialSquared (r^2) < η →
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) r) ≤
        graphBallQuadraticArea cubeCenter n g r + K * (2*r) * d +
          C * sublevelVolume (E ∆ torusGraphRegion cubeCenter n g) radialSquared (r^2) := by
  obtain ⟨η, C, hη, hC, hc⟩ := isMinimizerAt_local_quasiminimal hV hmin
  refine ⟨η, C, hη, hC, ?_⟩
  intro n hn g hg r K d hr hs hK hd ht
  let F := torusGraphRegion cubeCenter n g
  have hF : MeasurableSet F := measurableSet_torusGraphRegion _ _ hg.continuous
  let ε : ℕ → ℝ := fun i ↦ 1 / ((i : ℝ)+1)
  have he : ∀ i, 0 < ε i := fun i ↦ by dsimp [ε]; positivity
  let L : ℕ → ℝ := fun i ↦ ∫ y : Plane, radialDensityWeight cubeCenter r (ε i)
    (cubeCenter+normalGraph n g y) * (1+‖fderiv ℝ g y‖^2/2)
  have hlocal (i : ℕ) (X : Cover → Cover) (hX : AdmissibleField X) :
      (∫ x in fundamentalCube, characteristic F (quotientMap x) *
        divergence (fun y ↦ sublevelCutoff radialSquared (r^2) (1/((i : ℝ)+1)) y • X y) x) ≤ L i := by
    rw [← radialDensityWeight_periodize hr.le hs (he i)]
    exact torusGraphRegion_cutoff_flux_le cubeCenter hn hg
      (radialDensityWeight_contDiff _ _ _) (radialDensityWeight_hasCompactSupport hr.le (he i))
      (radialDensityWeight_cell_support hr.le (by linarith) (he i))
      (fun x ↦ ⟨radialDensityWeight_nonneg _ _ _ _, radialDensityWeight_le_one _ _ _ _⟩) hX
  have hlim : Tendsto L atTop (𝓝 (graphBallQuadraticArea cubeCenter n g r)) :=
    graphBallQuadraticArea_tendsto cubeCenter hn hg hr he tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨hG, hb⟩ := perimeter_glued_local_flux_le hE hF hμ radialSquared_contDiff
    radialSquared_periodic hK (norm_gradient_radialSquared hr.le hs.le) hd hlim hlocal
  have hdist : regionDistance E (gluedRegion E F (sublevelRegion radialSquared (r^2))) =
      sublevelVolume (E ∆ F) radialSquared (r^2) :=
    regionDistance_gluedRegion hE.nullMeasurableSet hF.nullMeasurableSet
      (measurableSet_sublevelRegion radialSquared_contDiff.continuous.measurable _).nullMeasurableSet
  have hcomp := hc _ hG (hdist ▸ ht)
  rw [hdist] at hcomp
  rw [hμ.1, normalMeasure_radial_sublevel μ hr.le hs.le] at hb
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma lipschitz_probability_average_integrable {ν : Measure Plane} [IsProbabilityMeasure ν]
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {δ : ℝ} (_hδ : 0 ≤ δ) (hb : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) (x : Plane) :
    Integrable (fun y ↦ f (x-y)) ν := by
  apply (integrable_const (|f x|+(K : ℝ)*δ)).mono'
    (hf.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  filter_upwards [hb] with y hy
  have hh := hf.dist_le_mul (x-y) x
  rw [Real.dist_eq, dist_eq_norm, sub_sub_cancel_left, norm_neg] at hh
  rw [Real.norm_eq_abs]
  have ht := abs_add_le (f (x-y)-f x) (f x)
  rw [sub_add_cancel] at ht
  exact ht.trans (by nlinarith [mul_le_mul_of_nonneg_left hy K.coe_nonneg])

lemma lipschitz_probability_average_error {ν : Measure Plane} [IsProbabilityMeasure ν]
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {δ : ℝ} (hδ : 0 ≤ δ) (hb : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) (x : Plane) :
    |(∫ y, f (x-y) ∂ν)-f x| ≤ (K : ℝ)*δ := by
  have hi := lipschitz_probability_average_integrable hf hδ hb x
  have he : f x = ∫ _y : Plane, f x ∂ν := by simp
  rw [he, ← integral_sub hi (integrable_const _)]
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  change (∫ y, ‖f (x-y)-f x‖ ∂ν) ≤ _
  calc
    _ ≤ ∫ _y : Plane, (K : ℝ)*δ ∂ν := by
      apply integral_mono_ae (hi.sub (integrable_const _)).norm (integrable_const _)
      filter_upwards [hb] with y hy
      have hh := hf.dist_le_mul (x-y) x
      rw [Real.dist_eq, dist_eq_norm, sub_sub_cancel_left, norm_neg] at hh
      rw [Real.norm_eq_abs]
      exact hh.trans (mul_le_mul_of_nonneg_left hy K.coe_nonneg)
    _ = _ := by simp

lemma lipschitz_probability_average_hasFDerivAt {ν : Measure Plane} [IsProbabilityMeasure ν]
    (hν : ν ≪ (volume : Measure Plane)) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {δ : ℝ} (hδ : 0 ≤ δ) (hb : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) (x : Plane) :
    Integrable (fun y ↦ fderiv ℝ f (x-y)) ν ∧
      HasFDerivAt (fun z ↦ ∫ y, f (z-y) ∂ν) (∫ y, fderiv ℝ f (x-y) ∂ν) x := by
  refine hasFDerivAt_integral_of_dominated_loc_of_lip
    (F := fun z y : Plane ↦ f (z-y)) (F' := fun y ↦ fderiv ℝ f (x-y))
    (x₀ := x) (s := univ) (bound := fun _ ↦ (K : ℝ)) (Filter.univ_mem)
    (Eventually.of_forall fun z ↦ (hf.continuous.comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (lipschitz_probability_average_integrable hf hδ hb x)
    ((measurable_fderiv ℝ f).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    ?_ (integrable_const _) ?_
  · exact Eventually.of_forall fun y ↦ by
      have hl : LipschitzWith K (fun z : Plane ↦ f (z-y)) := by
        apply LipschitzWith.of_dist_le_mul
        intro z w
        simpa only [dist_sub_right] using hf.dist_le_mul (z-y) (w-y)
      simpa only [Real.nnabs_of_nonneg K.coe_nonneg, Real.toNNReal_coe] using hl.lipschitzOnWith
  · have hd : ∀ᵐ y ∂ν, DifferentiableAt ℝ f (x-y) := hν.ae_le
      ((volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae hf.ae_differentiableAt)
    filter_upwards [hd] with y hy
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
      hy.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const y)

lemma lipschitz_probability_average_gradient_sq {ν : Measure Plane} [IsProbabilityMeasure ν]
    (hν : ν ≪ (volume : Measure Plane)) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {δ : ℝ} (hδ : 0 ≤ δ) (hb : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) (x : Plane) :
    ‖fderiv ℝ (fun z ↦ ∫ y, f (z-y) ∂ν) x‖^2 ≤ ∫ y, ‖fderiv ℝ f (x-y)‖^2 ∂ν := by
  have hh := lipschitz_probability_average_hasFDerivAt hν hf hδ hb x
  rw [hh.2.fderiv]
  have hi : Integrable (fun y ↦ ‖fderiv ℝ f (x-y)‖^2) ν := by
    apply (integrable_const ((K : ℝ)^2)).mono'
      (((measurable_fderiv ℝ f).comp (measurable_const.sub measurable_id)).norm.pow_const 2).aestronglyMeasurable
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change ‖fderiv ℝ f (x-y)‖^2 ≤ (K : ℝ)^2
    have hb' := norm_fderiv_le_of_lipschitz ℝ hf (x₀ := x-y)
    nlinarith [norm_nonneg (fderiv ℝ f (x-y))]
  have hs := integral_square_le_mass hh.1.norm hi
  simp only [probReal_univ, one_mul] at hs
  have hn := norm_integral_le_integral_norm (μ := ν) (fun y ↦ fderiv ℝ f (x-y))
  have hi0 : 0 ≤ ∫ y, ‖fderiv ℝ f (x-y)‖ ∂ν := integral_nonneg (fun y ↦ norm_nonneg _)
  nlinarith [norm_nonneg (∫ y, fderiv ℝ f (x-y) ∂ν)]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma lipschitz_gradient_sq_integrable_ball {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (R : ℝ) :
    IntegrableOn (fun x ↦ ‖fderiv ℝ f x‖^2) (Metric.ball (0 : Plane) R) := by
  apply (integrableOn_const (C := (K : ℝ)^2) measure_ball_lt_top.ne).mono'
    ((measurable_fderiv ℝ f).norm.pow_const 2).aestronglyMeasurable.restrict
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hf) 2

lemma lipschitz_gradient_sq_shift_ball_le {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (R δ : ℝ) {y : Plane} (hy : ‖y‖ ≤ δ) :
    (∫ x in Metric.ball (0 : Plane) R, ‖fderiv ℝ f (x-y)‖^2) ≤
      ∫ x in Metric.ball (0 : Plane) (R+δ), ‖fderiv ℝ f x‖^2 := by
  let G : Plane → ℝ := (Metric.ball (0 : Plane) (R+δ)).indicator (fun x ↦ ‖fderiv ℝ f x‖^2)
  have hi : Integrable G := (lipschitz_gradient_sq_integrable_ball hf (R+δ)).integrable_indicator
    measurableSet_ball
  have hit : Integrable (fun x ↦ G (x-y)) := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      ((measurePreserving_add_right volume (-y)).integrable_comp hi.aestronglyMeasurable).mpr hi
  have hil : IntegrableOn (fun x ↦ ‖fderiv ℝ f (x-y)‖^2) (Metric.ball (0 : Plane) R) := by
    apply (integrableOn_const (C := (K : ℝ)^2) measure_ball_lt_top.ne).mono'
      (((measurable_fderiv ℝ f).comp (measurable_id.sub_const y)).norm.pow_const 2).aestronglyMeasurable.restrict
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change ‖fderiv ℝ f (x-y)‖^2 ≤ (K : ℝ)^2
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hf) 2
  rw [← integral_indicator measurableSet_ball]
  calc
    _ ≤ ∫ x : Plane, G (x-y) := by
      apply integral_mono (hil.integrable_indicator measurableSet_ball) hit
      intro x
      by_cases hx : x ∈ Metric.ball (0 : Plane) R
      · have hxy : x-y ∈ Metric.ball (0 : Plane) (R+δ) := by
          rw [Metric.mem_ball, dist_zero_right] at hx ⊢
          exact (norm_sub_le x y).trans_lt (add_lt_add_of_lt_of_le hx hy)
        simp only [indicator_of_mem hx, G, indicator_of_mem hxy, le_refl]
      · rw [indicator_of_notMem hx]
        exact indicator_nonneg (fun _ _ ↦ sq_nonneg _) _
    _ = _ := by
      rw [show (fun x : Plane ↦ G (x-y)) = (fun x ↦ G (x+(-y))) from rfl,
        integral_add_right_eq_self G (-y)]
      exact integral_indicator measurableSet_ball

theorem lipschitz_probability_average_local_energy {ν : Measure Plane} [IsProbabilityMeasure ν]
    (hν : ν ≪ (volume : Measure Plane)) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {δ : ℝ} (hδ : 0 ≤ δ) (hb : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) (R : ℝ) :
    IntegrableOn (fun x ↦ ‖fderiv ℝ (fun z ↦ ∫ y, f (z-y) ∂ν) x‖^2) (Metric.ball (0 : Plane) R) ∧
      (∫ x in Metric.ball (0 : Plane) R, ‖fderiv ℝ (fun z ↦ ∫ y, f (z-y) ∂ν) x‖^2) ≤
        ∫ x in Metric.ball (0 : Plane) (R+δ), ‖fderiv ℝ f x‖^2 := by
  let μ : Measure Plane := volume.restrict (Metric.ball (0 : Plane) R)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let H : Plane × Plane → ℝ := fun p ↦ ‖fderiv ℝ f (p.2-p.1)‖^2
  have hHm : Measurable H := ((measurable_fderiv ℝ f).comp (measurable_snd.sub measurable_fst)).norm.pow_const 2
  have hH : Integrable H (ν.prod μ) := by
    apply (integrable_const ((K : ℝ)^2)).mono' hHm.aestronglyMeasurable
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hf) 2
  have hpoint (x : Plane) : ‖fderiv ℝ (fun z ↦ ∫ y, f (z-y) ∂ν) x‖^2 ≤ ∫ y, H (y,x) ∂ν :=
    lipschitz_probability_average_gradient_sq hν hf hδ hb x
  have hI : Integrable (fun x ↦ ‖fderiv ℝ (fun z ↦ ∫ y, f (z-y) ∂ν) x‖^2) μ := by
    apply hH.integral_prod_right.mono'
      ((measurable_fderiv ℝ _).norm.pow_const 2).aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint x
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∫ x, ∫ y, H (y,x) ∂ν ∂μ := integral_mono hI hH.integral_prod_right hpoint
    _ = ∫ y, ∫ x, H (y,x) ∂μ ∂ν := integral_integral_swap hH.swap
    _ ≤ ∫ _y : Plane, (∫ x in Metric.ball (0 : Plane) (R+δ), ‖fderiv ℝ f x‖^2) ∂ν := by
      apply integral_mono_ae hH.integral_prod_left (integrable_const _)
      filter_upwards [hb] with y hy
      exact lipschitz_gradient_sq_shift_ball_le hf R δ hy
    _ = _ := by simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Convolution
namespace CubicTorus

def graphSmoothingMeasure (b : ContDiffBump (0 : Plane)) : Measure Plane :=
  volume.withDensity (fun y ↦ ENNReal.ofReal (b.normed volume y))

instance graphSmoothingMeasure_probability (b : ContDiffBump (0 : Plane)) :
    IsProbabilityMeasure (graphSmoothingMeasure b) := by
  constructor
  rw [graphSmoothingMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal b.integrable_normed
      (Eventually.of_forall b.nonneg_normed), b.integral_normed]
  norm_num

lemma graphSmoothingMeasure_ac (b : ContDiffBump (0 : Plane)) :
    graphSmoothingMeasure b ≪ volume := withDensity_absolutelyContinuous _ _

lemma graphSmoothingMeasure_radius (b : ContDiffBump (0 : Plane)) :
    ∀ᵐ y ∂graphSmoothingMeasure b, ‖y‖ ≤ b.rOut := by
  rw [graphSmoothingMeasure, ae_withDensity_iff b.continuous_normed.measurable.ennreal_ofReal]
  filter_upwards [] with y hy
  have hh : y ∈ Function.support (b.normed volume) := by
    change b.normed volume y ≠ 0
    intro he
    simp [he] at hy
  rw [b.support_normed_eq, Metric.mem_ball, dist_zero_right] at hh
  exact hh.le

def graphSmooth (b : ContDiffBump (0 : Plane)) (f : Plane → ℝ) : Plane → ℝ :=
  fun x ↦ ∫ y, f (x-y) ∂graphSmoothingMeasure b

lemma graphSmooth_eq_convolution (b : ContDiffBump (0 : Plane)) (f : Plane → ℝ) :
    graphSmooth b f = b.normed volume ⋆ f := by
  funext x
  rw [graphSmooth, graphSmoothingMeasure,
    integral_withDensity_eq_integral_toReal_smul b.continuous_normed.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (b.nonneg_normed _), convolution_def,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]

lemma graphSmooth_contDiff (b : ContDiffBump (0 : Plane)) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : ContDiff ℝ (⊤ : ℕ∞) (graphSmooth b f) := by
  rw [graphSmooth_eq_convolution]
  exact b.hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) b.contDiff_normed hf.continuous.locallyIntegrable

lemma graphSmooth_error (b : ContDiffBump (0 : Plane)) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (x : Plane) :
    |graphSmooth b f x-f x| ≤ (K : ℝ)*b.rOut :=
  lipschitz_probability_average_error hf b.rOut_pos.le (graphSmoothingMeasure_radius b) x

lemma graphSmooth_local_energy (b : ContDiffBump (0 : Plane)) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (R : ℝ) :
    IntegrableOn (fun x ↦ ‖fderiv ℝ (graphSmooth b f) x‖^2) (Metric.ball (0 : Plane) R) ∧
      (∫ x in Metric.ball (0 : Plane) R, ‖fderiv ℝ (graphSmooth b f) x‖^2) ≤
        ∫ x in Metric.ball (0 : Plane) (R+b.rOut), ‖fderiv ℝ f x‖^2 :=
  lipschitz_probability_average_local_energy (graphSmoothingMeasure_ac b) hf b.rOut_pos.le
    (graphSmoothingMeasure_radius b) R

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalGraph_norm_ge {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) (y : Plane) :
    ‖y‖ ≤ ‖normalGraph n g y‖ := by
  have hh := (normalPlaneCoordinates_lipschitz n).dist_le_mul (normalGraph n g y) 0
  simpa only [normalPlaneCoordinates_graph hn, map_zero, dist_zero_right,
    NNReal.coe_one, one_mul] using hh

lemma graphBallQuadraticArea_le_disk (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {g : Plane → ℝ} (hg : Continuous g) {r : ℝ} (hr : 0 ≤ r)
    (hi : IntegrableOn (fun y ↦ ‖fderiv ℝ g y‖^2) (Metric.ball (0 : Plane) r)) :
    graphBallQuadraticArea a n g r ≤ Real.pi*r^2 +
      (∫ y in Metric.ball (0 : Plane) r, ‖fderiv ℝ g y‖^2)/2 := by
  let S : Set Plane := {y | a+normalGraph n g y ∈ Metric.ball a r}
  have hS : MeasurableSet S := measurableSet_ball.preimage
    (graph_trace_continuous a n hg continuous_id).measurable
  have hsub : S ⊆ Metric.ball (0 : Plane) r := by
    intro y hy
    have hh : ‖normalGraph n g y‖ < r := by
      simpa only [S, mem_ofPred_eq, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] using hy
    simpa only [Metric.mem_ball, dist_zero_right] using (normalGraph_norm_ge hn g y).trans_lt hh
  have hii : IntegrableOn (fun y ↦ 1+‖fderiv ℝ g y‖^2/2) (Metric.ball (0 : Plane) r) :=
    (integrableOn_const (C := (1 : ℝ)) measure_ball_lt_top.ne).add (hi.div_const 2)
  calc
    _ ≤ ∫ y in Metric.ball (0 : Plane) r, 1+‖fderiv ℝ g y‖^2/2 := by
      apply setIntegral_mono_set hii
      · exact Eventually.of_forall fun y ↦ by positivity
      · exact hsub.eventuallyLE
    _ = _ := by
      rw [integral_add (integrableOn_const (C := (1 : ℝ)) measure_ball_lt_top.ne) (hi.div_const 2),
        integral_const, smul_eq_mul, mul_one, integral_div]
      rw [show (volume.restrict (Metric.ball (0 : Plane) r)).real univ = volume.real (Metric.ball (0 : Plane) r) by simp [Measure.real], plane_ball_real hr]

theorem graphSmooth_ball_area_le (b : ContDiffBump (0 : Plane))
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1) {r : ℝ} (hr : 0 ≤ r) :
    graphBallQuadraticArea a n (graphSmooth b f) r ≤ Real.pi*r^2 +
      (∫ y in Metric.ball (0 : Plane) (r+b.rOut), ‖fderiv ℝ f y‖^2)/2 := by
  have hh := graphSmooth_local_energy b hf r
  exact (graphBallQuadraticArea_le_disk a hn (graphSmooth_contDiff b hf).continuous hr hh.1).trans
    (add_le_add le_rfl (div_le_div_of_nonneg_right hh.2 (by norm_num : (0 : ℝ) ≤ 2)))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma smooth_graph_energy_integrable {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (r : ℝ) :
    IntegrableOn (fun y ↦ ‖fderiv ℝ g y‖ ^ 2) (Metric.ball (0 : Plane) r) := by
  apply (ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : Plane) r)
    (((hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.norm).pow 2).continuousOn).mono_set
    Metric.ball_subset_closedBall

theorem isMinimizerAt_graph_low_slice {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (n : Cover), ‖n‖ = 1 →
      ∀ (g : Plane → ℝ), ContDiff ℝ (⊤ : ℕ∞) g →
      ∀ a b B K : ℝ, 0 < a → a < b → b < 1/4 → B < η →
      (∀ u, ‖deriv Real.smoothTransition u‖ ≤ K) →
      torusVolume.real ((E ∆ torusGraphRegion cubeCenter n g) ∩
        Metric.ball (quotientMap cubeCenter) b) < B →
      ∃ ρ ∈ Ioo a b,
        (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap cubeCenter) ρ) ≤
          Real.pi*ρ^2 + (∫ y in Metric.ball (0 : Plane) b, ‖fderiv ℝ g y‖^2)/2 +
            (2*K*b/(b^2-a^2)+C)*B := by
  obtain ⟨η,C,hη,hC,hcomp⟩ := isMinimizerAt_graph_replacement hV hE hmin hμ
  refine ⟨η,C,hη,hC,?_⟩
  intro n hn g hg a b B K ha hab hbs hB hK he
  let m := sublevelVolume (E ∆ torusGraphRegion cubeCenter n g) radialSquared
  have hm : Monotone m := sublevelVolume_mono _ _
  have ha2b2 : a^2 < b^2 := by nlinarith
  have hmb : m (b^2) < B := by
    dsimp [m, sublevelVolume]
    rw [sublevelRegion_radialSquared (by linarith) hbs.le, cubeBall_eq_metricBall]
    exact he
  have hmb0 : 0 ≤ m (b^2) := measureReal_nonneg
  have hB0 : 0 < B := hmb0.trans_lt hmb
  have hden : 0 < b^2-a^2 := sub_pos.mpr ha2b2
  have hbound : m (b^2)-m (a^2) < (B/(b^2-a^2))*(b^2-a^2) := by
    rw [div_mul_cancel₀ _ hden.ne']
    have hh : 0 ≤ m (a^2) := measureReal_nonneg
    linarith
  obtain ⟨t,ht,hd,hder⟩ := monotone_exists_deriv_le hm ha2b2 hbound
  let ρ := Real.sqrt t
  have ht0 : 0 < t := (sq_nonneg a).trans_lt ht.1
  have hρ0 : 0 < ρ := Real.sqrt_pos.mpr ht0
  have hρsq : ρ^2 = t := Real.sq_sqrt ht0.le
  have hρa : a < ρ := (sq_lt_sq₀ ha.le hρ0.le).mp (by rw [hρsq]; exact ht.1)
  have hρb : ρ < b := (sq_lt_sq₀ hρ0.le (ha.trans hab).le).mp (by rw [hρsq]; exact ht.2)
  have hmt : m t < B := (hm ht.2.le).trans_lt hmb
  have hcompare := hcomp n hn g hg ρ K (deriv m t) hρ0 (hρb.trans hbs) hK
    (hρsq ▸ hd.hasDerivAt) (by simpa only [hρsq] using hmt.trans hB)
  have har := graphBallQuadraticArea_le_disk cubeCenter hn hg.continuous hρ0.le
    (smooth_graph_energy_integrable hg ρ)
  have henergy : (∫ y in Metric.ball (0 : Plane) ρ, ‖fderiv ℝ g y‖^2) ≤
      ∫ y in Metric.ball (0 : Plane) b, ‖fderiv ℝ g y‖^2 :=
    setIntegral_mono_set (smooth_graph_energy_integrable hg b)
      (Eventually.of_forall fun y ↦ sq_nonneg _) (Metric.ball_subset_ball hρb.le).eventuallyLE
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hd1 : K*(2*ρ)*deriv m t ≤ K*(2*ρ)*(B/(b^2-a^2)) :=
    mul_le_mul_of_nonneg_left hder (by positivity)
  have hd2 : K*(2*ρ)*(B/(b^2-a^2)) ≤ K*(2*b)*(B/(b^2-a^2)) := by
    gcongr
  have hc1 : C*m t ≤ C*B := mul_le_mul_of_nonneg_left hmt.le hC
  refine ⟨ρ,⟨hρa,hρb⟩,?_⟩
  change _ ≤ _ at hcompare
  rw [hρsq] at hcompare
  have heq : (2*K*b/(b^2-a^2)+C)*B = K*(2*b)*(B/(b^2-a^2))+C*B := by ring
  rw [heq]
  linarith

end CubicTorus

end
end

end

end OAI
