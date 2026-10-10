import Mathlib
import OAI.Geometry.CubicTorus.Estimates.BVGraphRescaling

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma columnGraphMismatch_disagreement_volume_le {U : Set Torus} (hU : IsOpen U)
    (σ : FiniteMeasure Torus) {R c₀ : ℝ} (hR : 0 < R) (hc₀ : 0 < c₀)
    (hl : ∀ x ∈ frontier U, ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      c₀*ρ^2 ≤ (σ : Measure Torus).real (Metric.ball x ρ))
    (a : Torus) {n : Cover} (hn : ‖n‖ = 1) {r α η : ℝ}
    (hr : 0 < r) (hrs : r < 1/2) (hα : α < 1/4) (hη : η ≤ 1/2)
    (htrap : normalCap a n r (α*r) ⊆ (closure U)ᶜ ∧ normalCap a (-n) r (α*r) ⊆ U)
    (S : Set Torus) (g : Plane → ℝ)
    (hS : ∀ x ∈ S, g (normalPlaneCoordinates n (shortestLift (x-a))) = ⟪n, shortestLift (x-a)⟫)
    (hcone : ∀ c ∈ S, ∀ x ∈ frontier U, dist x c ≤ r →
      |⟪n, shortestLift (x-c)⟫| ≤ η*dist x c) :
    (volume : Measure Plane) {y ∈ Metric.ball (0 : Plane) (r/4) | columnGraphMismatch U a n r g y ≠ 0} ≤
      ((planeAreaFactor : ℝ≥0∞)*ENNReal.ofReal (64/c₀)) *
        (σ : Measure Torus) ((frontier U ∩ Metric.ball a (r/2)) \ S) := by
  let Q : Torus → Plane := fun x ↦ normalPlaneCoordinates n (shortestLift (x-a))
  have hs : {y ∈ Metric.ball (0 : Plane) (r/4) | columnGraphMismatch U a n r g y ≠ 0} ⊆
      Q '' ((frontier U ∩ Metric.ball a (r/2)) \ S) := by
    intro y hy
    obtain ⟨x,hx,hxy⟩ := trapped_boundary_projects_disk hU a hn hr hrs hα htrap hy.1
    have hxS : x ∉ S := by
      intro hm
      apply hy.2
      rw [← hxy]
      exact columnGraphMismatch_eq_zero_good hU hn hr hrs hα hη htrap hx (hcone x hm)
        (by simpa only [hxy] using hy.1) g (hS x hm)
    exact ⟨x, ⟨hx,hxS⟩, hxy⟩
  apply (measure_mono hs).trans
  apply plane_projection_volume_le_perimeter σ (frontier U) hR hc₀ hl n a _ (fun x hx ↦ hx.1.1)
  intro x hx
  exact (Metric.ball_subset_ball (by linarith : r/2 ≤ 1/4)) hx.1.2

theorem columnGraphMismatch_L1_le {U : Set Torus} (hU : IsOpen U)
    (σ : FiniteMeasure Torus) {R c₀ : ℝ} (hR : 0 < R) (hc₀ : 0 < c₀)
    (hl : ∀ x ∈ frontier U, ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      c₀*ρ^2 ≤ (σ : Measure Torus).real (Metric.ball x ρ))
    (a : Torus) {n : Cover} (hn : ‖n‖ = 1) {r α η : ℝ}
    (hr : 0 < r) (hrs : r < 1/2) (hα0 : 0 ≤ α) (hα : α < 1/4) (hη : η ≤ 1/2)
    (htrap : normalCap a n r (α*r) ⊆ (closure U)ᶜ ∧ normalCap a (-n) r (α*r) ⊆ U)
    (S : Set Torus) (g : Plane → ℝ) (hg : Measurable g)
    (hheight : ∀ y ∈ Metric.ball (0 : Plane) (r/4), |g y| ≤ α*r)
    (hS : ∀ x ∈ S, g (normalPlaneCoordinates n (shortestLift (x-a))) = ⟪n, shortestLift (x-a)⟫)
    (hcone : ∀ c ∈ S, ∀ x ∈ frontier U, dist x c ≤ r →
      |⟪n, shortestLift (x-c)⟫| ≤ η*dist x c) :
    (∫⁻ y in Metric.ball (0 : Plane) (r/4), ENNReal.ofReal (columnGraphMismatch U a n r g y)) ≤
      ENNReal.ofReal (2*α*r) * (((planeAreaFactor : ℝ≥0∞)*ENNReal.ofReal (64/c₀)) *
        (σ : Measure Torus) ((frontier U ∩ Metric.ball a (r/2)) \ S)) := by
  let D : Set Plane := {y ∈ Metric.ball (0 : Plane) (r/4) | columnGraphMismatch U a n r g y ≠ 0}
  have hD : MeasurableSet D := measurableSet_ball.inter
    (measurableSet_eq_fun (measurable_columnGraphMismatch hU.measurableSet a n r hg) measurable_const).compl
  have hb : ∀ y ∈ Metric.ball (0 : Plane) (r/4), ENNReal.ofReal (columnGraphMismatch U a n r g y) ≤
      D.indicator (fun _ ↦ ENNReal.ofReal (2*α*r)) y := by
    intro y hy
    by_cases he : columnGraphMismatch U a n r g y = 0
    · simp [he]
    · rw [indicator_of_mem (show y ∈ D from ⟨hy,he⟩)]
      exact ENNReal.ofReal_le_ofReal (columnGraphMismatch_trapped_le hU.measurableSet hn hr hrs hα0 hα htrap g hy (hheight y hy))
  calc
    _ ≤ ∫⁻ y in Metric.ball (0 : Plane) (r/4), D.indicator (fun _ ↦ ENNReal.ofReal (2*α*r)) y :=
      setLIntegral_mono' measurableSet_ball hb
    _ = ENNReal.ofReal (2*α*r) * (volume : Measure Plane) D := by
      rw [lintegral_indicator hD, lintegral_const, Measure.restrict_restrict hD]
      simp only [Measure.restrict_apply_univ, inter_eq_left.mpr (show D ⊆ Metric.ball (0 : Plane) (r/4) from fun _ h ↦ h.1)]
    _ ≤ _ := mul_le_mul_right (columnGraphMismatch_disagreement_volume_le hU σ hR hc₀ hl a hn hr hrs hα hη htrap S g hS hcone) _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma characteristic_symmDiff_eq_abs (U F : Set Torus) (x : Torus) :
    characteristic (U ∆ F) x = |characteristic U x-characteristic F x| := by
  by_cases hU : x ∈ U <;> by_cases hF : x ∈ F <;>
    simp [characteristic, Set.mem_symmDiff, hU, hF]

lemma graphSublevelIndicator_column (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (t : ℝ) (y : Plane) :
    graphSublevelIndicator a n g (normalColumnChart a n (t,y)) = columnPhase (g y) t := by
  simp only [graphSublevelIndicator, graphHeightExtension, Set.indicator,
    Set.mem_ofPred_eq, normalColumnChart_height a hn, normalColumnChart_projection a hn,
    columnPhase, mem_Iio]

lemma cubeCenter_add_mem {x : Cover} (hx : ‖x‖ < 1/2) :
    cubeCenter+x ∈ fundamentalCube := by
  intro i
  have hi := (PiLp.norm_apply_le x i).trans_lt hx
  rw [Real.norm_eq_abs, abs_lt] at hi
  change 0 ≤ 1/2+x i ∧ 1/2+x i < 1
  constructor <;> linarith

lemma torusGraphRegion_symmDiff_ball_le {U : Set Torus} (hU : MeasurableSet U)
    {n : Cover} (hn : ‖n‖ = 1) {r s : ℝ} (hrs : r < 1) (hs : s ≤ r/4)
    {g : Plane → ℝ} (hg : Continuous g) :
    torusVolume ((U ∆ torusGraphRegion cubeCenter n g) ∩
      Metric.ball (quotientMap cubeCenter) s) ≤
      ∫⁻ y in Metric.ball (0 : Plane) (r/4),
        ENNReal.ofReal (columnGraphMismatch U (quotientMap cubeCenter) n r g y) := by
  let D := U ∆ torusGraphRegion cubeCenter n g
  have hD : MeasurableSet D := hU.symmDiff (measurableSet_torusGraphRegion _ _ hg)
  let f : Cover → ℝ≥0∞ := (Metric.ball (0 : Cover) s).indicator
    (fun x ↦ ENNReal.ofReal (characteristic D (quotientMap x+quotientMap cubeCenter)))
  have hf : Measurable f := (((measurable_characteristic hD).comp
    (measurable_quotientMap.add_const _)).ennreal_ofReal).indicator measurableSet_ball
  have he : torusVolume (D ∩ Metric.ball (quotientMap cubeCenter) s) = ∫⁻ x, f x := by
    have hm := lintegral_map (μ := volume.restrict (Metric.ball (0 : Cover) s))
      ((measurable_characteristic hD).ennreal_ofReal) (measurable_quotientMap.add_const (quotientMap cubeCenter))
    rw [torusVolume_chart_map_restrict _ (by linarith : s ≤ 1/2)] at hm
    rw [lintegral_indicator measurableSet_ball]
    rw [← hm]
    have hi : (fun x ↦ ENNReal.ofReal (characteristic D x)) = D.indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
      funext x
      by_cases hx : x ∈ D <;> simp [characteristic, hx]
    rw [hi, lintegral_indicator hD, lintegral_one, Measure.restrict_apply_univ, Measure.restrict_apply hD]
  rw [he, ← (normalColumnChart_measurePreserving 0 n).lintegral_comp hf]
  have hb (t : ℝ) (y : Plane) : f (normalColumnChart 0 n (t,y)) ≤
      (Metric.ball (0 : Plane) (r/4)).indicator (fun y ↦ (Icc (-r/4) (r/4)).indicator
        (fun t ↦ ENNReal.ofReal |characteristic U
          (quotientMap cubeCenter+quotientMap (normalPlaneEmbedding n y+t • n))-
            columnPhase (g y) t|) t) y := by
    let x := normalColumnChart (0 : Cover) n (t,y)
    by_cases hx : x ∈ Metric.ball (0 : Cover) s
    · have hxnorm : ‖x‖ < s := by simpa only [Metric.mem_ball, dist_zero_right] using hx
      have ht : |t| ≤ ‖x‖ := by
        have hh := abs_real_inner_le_norm n x
        rw [hn, one_mul] at hh
        have ht0 : ⟪n,x⟫ = t := by simpa only [x, sub_zero] using normalColumnChart_height 0 hn t y
        rwa [ht0] at hh
      have hy : ‖y‖ ≤ ‖x‖ := by
        have hh := (normalPlaneCoordinates_lipschitz n).dist_le_mul x 0
        have hy0 : normalPlaneCoordinates n x = y := by
          simpa only [x, sub_zero] using normalColumnChart_projection 0 hn t y
        simpa only [map_zero, hy0, dist_zero_right, one_mul, NNReal.coe_one] using hh
      rw [indicator_of_mem (show y ∈ Metric.ball (0 : Plane) (r/4) by
        simpa only [Metric.mem_ball, dist_zero_right] using hy.trans_lt (hxnorm.trans_le hs))]
      rw [indicator_of_mem (show t ∈ Icc (-r/4) (r/4) by
        have hh := abs_le.mp (ht.trans (hxnorm.le.trans hs)); constructor <;> linarith)]
      dsimp [f]
      rw [indicator_of_mem hx, characteristic_symmDiff_eq_abs]
      have hxc : cubeCenter+x ∈ fundamentalCube := cubeCenter_add_mem (by linarith)
      have heq : quotientMap x+quotientMap cubeCenter = quotientMap (cubeCenter+x) := by
        rw [quotientMap_add, add_comm]
      rw [heq, characteristic_torusGraphRegion hxc]
      have hc : cubeCenter+x = normalColumnChart cubeCenter n (t,y) := by
        simp only [x, normalColumnChart_apply _ hn, zero_add]
      rw [hc, graphSublevelIndicator_column _ hn]
      rw [normalColumnChart_apply _ hn, quotientMap_add]
    · change f x ≤ _
      dsimp [f]
      rw [indicator_of_notMem hx]
      exact zero_le
  calc
    _ ≤ ∫⁻ y : Plane, ∫⁻ t : ℝ, (Metric.ball (0 : Plane) (r/4)).indicator
        (fun y ↦ (Icc (-r/4) (r/4)).indicator
          (fun t ↦ ENNReal.ofReal |characteristic U
            (quotientMap cubeCenter+quotientMap (normalPlaneEmbedding n y+t • n))-
              columnPhase (g y) t|) t) y := by
      rw [Measure.volume_eq_prod]
      rw [lintegral_prod_symm (fun p : ℝ × Plane ↦ f (normalColumnChart 0 n p))
        (hf.comp (normalColumnChart 0 n).measurable).aemeasurable]
      exact lintegral_mono fun y ↦ lintegral_mono fun t ↦ hb t y
    _ = _ := by
      rw [← lintegral_indicator measurableSet_ball]
      apply lintegral_congr
      intro y
      by_cases hy : y ∈ Metric.ball (0 : Plane) (r/4)
      · simp only [indicator_of_mem hy]
        rw [lintegral_indicator measurableSet_Icc]
        exact (ofReal_integral_eq_lintegral_ofReal (columnGraphMismatch_integrable hU _ n r g y)
          (Eventually.of_forall fun _ ↦ abs_nonneg _)).symm
      · simp only [indicator_of_notMem hy, lintegral_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma columnPhase_abs_sub (p q t : ℝ) :
    |columnPhase p t-columnPhase q t| =
      (Ico (min p q) (max p q)).indicator (fun _ ↦ (1 : ℝ)) t := by
  by_cases hp : t < p <;> by_cases hq : t < q <;>
    simp only [columnPhase, Set.indicator, mem_Iio, mem_Ico, min_le_iff, lt_max_iff, hp, hq] <;>
      split_ifs <;> simp_all
  first | linarith | (rename_i hbound; rcases hbound with hbound | hbound <;> linarith)

lemma integral_abs_columnPhase_sub (p q : ℝ) :
    Integrable (fun t ↦ |columnPhase p t-columnPhase q t|) ∧
      (∫ t : ℝ, |columnPhase p t-columnPhase q t|) = |p-q| := by
  simp_rw [columnPhase_abs_sub]
  constructor
  · exact (integrableOn_const (ne_of_lt (show volume (Ico (min p q) (max p q)) < ⊤ by rw [Real.volume_Ico]; exact ENNReal.ofReal_lt_top))).integrable_indicator measurableSet_Ico
  · rw [integral_indicator measurableSet_Ico, integral_const, measureReal_restrict_apply_univ,
      smul_eq_mul, mul_one]
    simp only [Measure.real, Real.volume_Ico, ENNReal.toReal_ofReal (sub_nonneg.mpr min_le_max)]
    rw [abs_sub_comm]
    exact max_sub_min_eq_abs _ _

lemma columnGraphMismatch_change_le {U : Set Torus} (hU : MeasurableSet U)
    (a : Torus) (n : Cover) (r : ℝ) (f g : Plane → ℝ) (y : Plane) :
    columnGraphMismatch U a n r f y ≤ columnGraphMismatch U a n r g y + |f y-g y| := by
  have hp := integral_abs_columnPhase_sub (g y) (f y)
  have hpoint (t : ℝ) : |characteristic U (a+quotientMap (normalPlaneEmbedding n y+t • n))-columnPhase (f y) t| ≤
      |characteristic U (a+quotientMap (normalPlaneEmbedding n y+t • n))-columnPhase (g y) t|+
        |columnPhase (g y) t-columnPhase (f y) t| := abs_sub_le _ _ _
  have hi := integral_mono (columnGraphMismatch_integrable hU a n r f y)
    ((columnGraphMismatch_integrable hU a n r g y).add hp.1.integrableOn) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_add (columnGraphMismatch_integrable hU a n r g y) hp.1.integrableOn] at hi
  have hb : (∫ t in Icc (-r/4) (r/4), |columnPhase (g y) t-columnPhase (f y) t|) ≤ |f y-g y| := by
    rw [abs_sub_comm, ← hp.2]
    exact integral_mono_measure Measure.restrict_le_self (Eventually.of_forall fun _ ↦ abs_nonneg _) hp.1
  exact hi.trans (add_le_add le_rfl hb)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma torusGraphRegion_symmDiff_change_le {U : Set Torus} (hU : MeasurableSet U)
    {n : Cover} (hn : ‖n‖ = 1) {r s : ℝ} (hrs : r < 1) (hs : s ≤ r/4)
    {f g : Plane → ℝ} (hf : Continuous f) (hg : Measurable g) :
    torusVolume ((U ∆ torusGraphRegion cubeCenter n f) ∩
      Metric.ball (quotientMap cubeCenter) s) ≤
      (∫⁻ y in Metric.ball (0 : Plane) (r/4),
        ENNReal.ofReal (columnGraphMismatch U (quotientMap cubeCenter) n r g y)) +
      ∫⁻ y in Metric.ball (0 : Plane) (r/4), ENNReal.ofReal |f y-g y| := by
  apply (torusGraphRegion_symmDiff_ball_le hU hn hrs hs hf).trans
  calc
    _ ≤ ∫⁻ y in Metric.ball (0 : Plane) (r/4),
        ENNReal.ofReal (columnGraphMismatch U (quotientMap cubeCenter) n r g y) + ENNReal.ofReal |f y-g y| := by
      apply lintegral_mono
      intro y
      dsimp only
      rw [← ENNReal.ofReal_add (columnGraphMismatch_nonneg _ _ _ _ _ _) (abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (columnGraphMismatch_change_le hU _ n r f g y)
    _ = _ := lintegral_add_left
      (measurable_columnGraphMismatch hU _ n r hg).ennreal_ofReal _

lemma torusGraphRegion_graphSmooth_difference_le {U : Set Torus} (hU : MeasurableSet U)
    {n : Cover} (hn : ‖n‖ = 1) {r s : ℝ} (hrs : r < 1) (hs : s ≤ r/4)
    (b : ContDiffBump (0 : Plane)) {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    torusVolume ((U ∆ torusGraphRegion cubeCenter n (graphSmooth b g)) ∩
      Metric.ball (quotientMap cubeCenter) s) ≤
      (∫⁻ y in Metric.ball (0 : Plane) (r/4),
        ENNReal.ofReal (columnGraphMismatch U (quotientMap cubeCenter) n r g y)) +
      ENNReal.ofReal ((K : ℝ)*b.rOut) * (volume : Measure Plane) (Metric.ball 0 (r/4)) := by
  apply (torusGraphRegion_symmDiff_change_le hU hn hrs hs
    (graphSmooth_contDiff b hg).continuous hg.continuous.measurable).trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∫⁻ y in Metric.ball (0 : Plane) (r/4), ENNReal.ofReal ((K : ℝ)*b.rOut) :=
      lintegral_mono fun y ↦ ENNReal.ofReal_le_ofReal (graphSmooth_error b hg y)
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma columnPhase_integral {r q : ℝ} (hq : |q| ≤ r/4) :
    (∫ t in Icc (-r/4) (r/4), columnPhase q t) = q+r/4 := by
  have hset : Icc (-r/4) (r/4) ∩ Iio q = Ico (-r/4) q := by
    ext t
    simp only [mem_inter_iff,mem_Icc,mem_Iio,mem_Ico]
    constructor
    · exact fun h ↦ ⟨h.1.1,h.2⟩
    · exact fun h ↦ ⟨⟨h.1,h.2.le.trans (abs_le.mp hq).2⟩,h.2⟩
  unfold columnPhase
  rw [setIntegral_indicator measurableSet_Iio,hset,integral_const,smul_eq_mul,mul_one,
    measureReal_def,Measure.restrict_apply_univ,Real.volume_Ico,
    ENNReal.toReal_ofReal (by linarith [(abs_le.mp hq).1] : 0 ≤ q- -r/4)]
  ring

lemma normalColumnHeight_error_le_mismatch {U : Set Torus} (hU : MeasurableSet U)
    (a : Torus) (n : Cover) (r : ℝ) {g : Plane → ℝ} (y : Plane) (hg : |g y| ≤ r/4) :
    |g y-normalColumnHeight U a n r y| ≤ columnGraphMismatch U a n r g y := by
  have hi : IntegrableOn (columnPhase (g y)) (Icc (-r/4) (r/4)) :=
    (integrable_const (1:ℝ)).indicator measurableSet_Iio
  have heq : columnGraphMismatch U a n r g y = ∫ t in Icc (-r/4) (r/4),
      |characteristic U (a+quotientMap (normalPlaneEmbedding n y+t • n))-columnPhase (g y) t| := rfl
  rw [abs_sub_comm,normalColumnHeight]
  have he : (∫ t in Icc (-r/4) (r/4), characteristic U
      (a+quotientMap (normalPlaneEmbedding n y+t • n))) -r/4-g y =
      ∫ t in Icc (-r/4) (r/4), (characteristic U
        (a+quotientMap (normalPlaneEmbedding n y+t • n))-columnPhase (g y) t) := by
    rw [integral_sub (normalColumn_integrable hU a n r y) hi,columnPhase_integral hg]
    ring
  rw [he,heq]
  exact abs_integral_le_integral_abs

lemma columnGraphMismatch_bound {U : Set Torus} (hU : MeasurableSet U)
    (a : Torus) (n : Cover) {r : ℝ} (hr : 0 ≤ r) (g : Plane → ℝ) (y : Plane) :
    columnGraphMismatch U a n r g y ≤ r/2 := by
  have hh := integral_mono (columnGraphMismatch_integrable hU a n r g y)
    (integrable_const (1:ℝ)) (fun t ↦ columnPhase_difference_le U _ (g y) t)
  rw [integral_const,smul_eq_mul,mul_one,measureReal_def,Measure.restrict_apply_univ,
    Real.volume_Icc,ENNReal.toReal_ofReal (by linarith : 0 ≤ r/4- -r/4)] at hh
  exact hh.trans_eq (by ring)

lemma columnGraphMismatch_integrable_ball {U : Set Torus} (hU : MeasurableSet U)
    (a : Torus) (n : Cover) {r : ℝ} (hr : 0 ≤ r) {g : Plane → ℝ} (hg : Measurable g)
    (R : ℝ) : IntegrableOn (columnGraphMismatch U a n r g) (Metric.ball 0 R) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Plane) R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  apply (integrable_const (r/2)).mono'
  · exact (measurable_columnGraphMismatch hU a n r hg).aestronglyMeasurable
  · exact Eventually.of_forall fun y ↦ by
      rw [Real.norm_eq_abs,abs_of_nonneg (columnGraphMismatch_nonneg _ _ _ _ _ _)]
      exact columnGraphMismatch_bound hU a n hr g y

lemma columnGraphMismatch_integral_change_le {U : Set Torus} (hU : MeasurableSet U)
    (a : Torus) (n : Cover) {r : ℝ} (hr : 0 ≤ r) {f g : Plane → ℝ}
    (hf : Measurable f) (hg : Measurable g) {δ : ℝ} (he : ∀ y, |f y-g y| ≤ δ) (R : ℝ) :
    (∫ y in Metric.ball (0 : Plane) R, columnGraphMismatch U a n r f y) ≤
      (∫ y in Metric.ball (0 : Plane) R, columnGraphMismatch U a n r g y) +
        δ*(volume : Measure Plane).real (Metric.ball 0 R) := by
  have hfin : (volume : Measure Plane) (Metric.ball 0 R) ≠ ⊤ := measure_ball_lt_top.ne
  have hi := integral_mono (columnGraphMismatch_integrable_ball hU a n hr hf R)
    ((columnGraphMismatch_integrable_ball hU a n hr hg R).add (integrableOn_const hfin))
    (fun y ↦ (columnGraphMismatch_change_le hU a n r f g y).trans (add_le_add le_rfl (he y)))
  simp only [Pi.add_apply] at hi
  rw [integral_add (columnGraphMismatch_integrable_ball hU a n hr hg R)
    (integrableOn_const hfin),setIntegral_const] at hi
  simpa only [smul_eq_mul,mul_comm] using hi

lemma normalColumnHeight_integral_error_le {U : Set Torus} (hU : MeasurableSet U)
    (a : Torus) (n : Cover) {r : ℝ} (hr : 0 ≤ r) {g : Plane → ℝ}
    (hg : Measurable g) (hb : ∀ y, |g y| ≤ r/4) (R : ℝ) :
    (∫ y in Metric.ball (0 : Plane) R, |g y-normalColumnHeight U a n r y|) ≤
      ∫ y in Metric.ball (0 : Plane) R, columnGraphMismatch U a n r g y := by
  have hi := columnGraphMismatch_integrable_ball hU a n hr hg R
  have hb' := fun y ↦ normalColumnHeight_error_le_mismatch hU a n r y (hb y)
  have hi' : IntegrableOn (fun y ↦ |g y-normalColumnHeight U a n r y|) (Metric.ball 0 R) := by
    apply hi.mono'
    · exact (hg.sub (measurable_normalColumnHeight hU a n r)).abs.aestronglyMeasurable
    · exact Eventually.of_forall fun y ↦ by simpa only [Real.norm_eq_abs,abs_abs] using hb' y
  exact integral_mono hi' hi hb'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma plane_ball_real_volume_scale {r : ℝ} (hr : 0 < r) (b : ℝ) :
    (volume : Measure Plane).real (Metric.ball 0 (r*b)) =
      r^2*(volume : Measure Plane).real (Metric.ball 0 b) := by
  have hh := plane_integral_rescale_ball (fun _ ↦ (1:ℝ)) hr b
  simpa only [setIntegral_const,smul_eq_mul,mul_one] using hh

lemma torusGraphRegion_symmDiff_real_ball_le {U : Set Torus} (hU : MeasurableSet U)
    {n : Cover} (hn : ‖n‖ = 1) {r s : ℝ} (hr : 0 ≤ r) (hrs : r < 1) (hs : s ≤ r/4)
    {g : Plane → ℝ} (hg : Continuous g) :
    torusVolume.real ((U ∆ torusGraphRegion cubeCenter n g) ∩ Metric.ball (quotientMap cubeCenter) s) ≤
      ∫ y in Metric.ball (0 : Plane) (r/4), columnGraphMismatch U (quotientMap cubeCenter) n r g y := by
  have hh := torusGraphRegion_symmDiff_ball_le hU hn hrs hs hg
  rw [← ofReal_integral_eq_lintegral_ofReal
    (columnGraphMismatch_integrable_ball hU _ n hr hg.measurable (r/4))
    (Eventually.of_forall fun y ↦ columnGraphMismatch_nonneg _ _ _ _ _ _)] at hh
  have ht := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hh
  rw [ENNReal.toReal_ofReal (integral_nonneg fun y ↦ columnGraphMismatch_nonneg _ _ _ _ _ _)] at ht
  exact ht

theorem exists_physical_smooth_graph {U : Set Torus} (hU : MeasurableSet U)
    {n : Cover} (hn : ‖n‖ = 1) {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {r δ α : ℝ} (hr : 0 < r) (hrs : r < 1) (hδ : 0 < δ) (hδr : δ ≤ r/8)
    (hα : α ≤ 1/4) (hheight : ∀ y, |g y| ≤ α*r) :
    ∃ G : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) G ∧ LipschitzWith K G ∧
      (∀ y, |G y| ≤ α*r) ∧
      (∫ y in Metric.ball (0 : Plane) (r/8), ‖fderiv ℝ G y‖^2) ≤
        (∫ y in Metric.ball (0 : Plane) (r/4), ‖fderiv ℝ g y‖^2) ∧
      (let B := (∫ y in Metric.ball (0 : Plane) (r/4),
          columnGraphMismatch U (quotientMap cubeCenter) n r g y)+
            δ*r^2*(volume : Measure Plane).real (Metric.ball 0 (1/4))
       (∫ y in Metric.ball (0 : Plane) (r/4),
          |G y-normalColumnHeight U (quotientMap cubeCenter) n r y|) ≤ B ∧
       ∀ s : ℝ, s ≤ r/4 → torusVolume.real ((U ∆ torusGraphRegion cubeCenter n G) ∩
         Metric.ball (quotientMap cubeCenter) s) ≤ B) := by
  obtain ⟨G,hG,hGL,he,henergy,hH⟩ := exists_sharp_smooth_graph hg hδ
  have hh (y : Plane) : |G y| ≤ α*r := by
    simpa only [zero_add,one_mul] using hH 0 1 (α*r) (by simpa only [zero_add,one_mul] using hheight) y
  have hb (y : Plane) : |G y| ≤ r/4 := (hh y).trans (by nlinarith)
  refine ⟨G,hG,hGL,hh,?_,?_⟩
  · exact (henergy (r/8)).trans (setIntegral_mono_set
      (lipschitz_gradient_sq_integrable_ball hg (r/4))
      (Eventually.of_forall fun y ↦ sq_nonneg _) (Metric.ball_subset_ball (by linarith)).eventuallyLE)
  · have herr := columnGraphMismatch_integral_change_le hU (quotientMap cubeCenter) n hr.le
      hG.continuous.measurable hg.continuous.measurable he (r/4)
    have hv : (volume : Measure Plane).real (Metric.ball 0 (r/4)) =
        r^2*(volume : Measure Plane).real (Metric.ball 0 (1/4)) := by
      simpa only [mul_one_div] using plane_ball_real_volume_scale hr (1/4)
    rw [hv] at herr
    have herr' : (∫ y in Metric.ball (0 : Plane) (r/4), columnGraphMismatch U
        (quotientMap cubeCenter) n r G y) ≤
        (∫ y in Metric.ball (0 : Plane) (r/4), columnGraphMismatch U
          (quotientMap cubeCenter) n r g y)+δ*r^2*(volume : Measure Plane).real (Metric.ball 0 (1/4)) := by
      simpa only [mul_assoc] using herr
    exact ⟨(normalColumnHeight_integral_error_le hU _ n hr.le hG.continuous.measurable hb (r/4)).trans herr',
      fun s hs ↦ (torusGraphRegion_symmDiff_real_ball_le hU hn hr.le hrs hs hG.continuous).trans herr'⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem normalMeasure_lipschitz_approximation_with_cones {E B : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {N : Torus → Cover} (hN : Measurable N)
    (hpolar : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hn : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    {D δ R A : ℝ} (hδ : 0 < δ) (hA : 0 < A)
    (hd : ∀ a ∈ B, ∀ t : ℝ, 0 < t → t ≤ D →
      δ * t ^ 3 ≤ torusVolume.real (E ∩ Metric.ball a t) ∧
      δ * t ^ 3 ≤ torusVolume.real (Eᶜ ∩ Metric.ball a t))
    (hu : ∀ a : Torus, ∀ r : ℝ, 0 < r → r ≤ R →
      (spatialNormalMeasure μ : Measure Torus).real (Metric.ball a r) ≤ A * r ^ 2)
    {ρ ε β : ℝ} (hρ : 0 < ρ) (hρsmall : ρ ≤ 1 / 32) (hρD : 2 * ρ ≤ D) (hρR : 80 * ρ ≤ R)
    (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hβ : 0 < β)
    (hβsmall : (131072 : ℝ) ^ 2 * (4 * A) * β ≤ (δ ^ 2 * (ε / 8) ^ 6) ^ 2)
    (a : Torus) {n : Cover} (hnorm : ‖n‖ = 1) :
    ∃ S : Set Torus, S ⊆ B ∩ Metric.ball a (ρ / 2) ∧
      (spatialNormalMeasure μ : Measure Torus) ((B ∩ Metric.ball a (ρ / 2)) \ S) ≤
        ENNReal.ofReal (25 * A / β) *
          ENNReal.ofReal (∫ x in Metric.closedBall a (17 * ρ), ‖N x - n‖ ^ 2
            ∂(spatialNormalMeasure μ : Measure Torus)) ∧
      (∀ c ∈ S, ∀ x ∈ B, dist x c ≤ ρ →
        |⟪n, shortestLift (x - c)⟫| ≤ ε * dist x c) ∧
      ∃ g : Cover → ℝ, LipschitzWith ⟨2 * ε, by positivity⟩ g ∧
        ∀ x ∈ S, g (normalPlaneProjection n (shortestLift (x - a))) =
          ⟪n, shortestLift (x - a)⟫ := by
  let σ := spatialNormalMeasure μ
  let S := {c : Torus | c ∈ B ∩ Metric.ball a (ρ / 2) ∧
    ∀ s : ℝ, 0 < s → s ≤ 16 * ρ → normalExcess σ N c n s < β}
  have hS : S ⊆ B ∩ Metric.ball a (ρ / 2) := fun _ hc ↦ hc.1
  have hgood (c : Torus) (hc : c ∈ S) : ∀ y ∈ B, dist y c ≤ ρ →
      |⟪n, shortestLift (y - c)⟫| ≤ ε * dist y c := by
    apply good_scales_boundary_cone hE hμ hN hpolar hn hδ hd hc.1.1 hnorm hρsmall hρD hε (by linarith)
    intro s hs hs16
    have hmass := (measureReal_mono (Metric.closedBall_subset_ball (by linarith : s < 2 * s))).trans
      (hu c (2 * s) (by positivity) (by linarith))
    have hmass' : (σ : Measure Torus).real (Metric.closedBall c s) ≤ (4 * A) * s ^ 2 := by
      change (σ : Measure Torus).real (Metric.closedBall c s) ≤ A * (2 * s) ^ 2 at hmass
      nlinarith
    have ho := normalOscillation_sq_le_excess σ hN hn hnorm c hs hmass'
    have he := hc.2 s hs hs16
    have hh := ho.trans_lt (mul_lt_mul_of_pos_left he (by positivity : 0 < 4 * A))
    have hh' := mul_lt_mul_of_pos_left hh (by norm_num : (0 : ℝ) < 131072 ^ 2)
    have hT : 0 < δ ^ 2 * (ε / 8) ^ 6 := by positivity
    have hnosc := normalOscillation_nonneg σ N c n s
    nlinarith
  have hbad : ∀ c ∈ (B ∩ Metric.ball a (ρ / 2)) \ S, ∃ r : ℝ,
      0 < r ∧ r ≤ 16 * ρ ∧ β ≤ normalExcess σ N c n r := by
    intro c hc
    have hh : ¬ ∀ s : ℝ, 0 < s → s ≤ 16 * ρ → normalExcess σ N c n s < β := by
      intro hh
      exact hc.2 ⟨hc.1, hh⟩
    push Not at hh
    exact hh
  have hbadmass := normalExcess_bad_set_measure hN hn n hA hβ hρ hρR hu a
    ((B ∩ Metric.ball a (ρ / 2)) \ S)
    (fun c hc ↦ (Metric.ball_subset_ball (by linarith : ρ / 2 ≤ ρ)) hc.1.2) hbad
  have hSsmall : S ⊆ Metric.ball a (1 / 4) :=
    hS.trans (inter_subset_right.trans (Metric.ball_subset_ball (by linarith)))
  have hcone : ∀ x ∈ S, ∀ y ∈ S, |⟪n, shortestLift (x - y)⟫| ≤ ε * dist x y := by
    intro x hx y hy
    apply hgood y hy x hx.1.1
    have hxa : dist x a < ρ / 2 := hx.1.2
    have hya : dist y a < ρ / 2 := hy.1.2
    linarith [dist_triangle_right x y a]
  obtain ⟨g, hg, hgeq⟩ := exists_lipschitz_height_of_cone
    ((fun z ↦ shortestLift (z - a)) '' S) hnorm hε.le hεhalf (lifted_cone_of_torus_cone hSsmall hcone)
  exact ⟨S, hS, hbadmass, hgood, g, hg, fun x hx ↦ hgeq _ ⟨x, hx, rfl⟩⟩

theorem isMinimizerAt_lipschitz_approximation_with_cones {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    ∃ ρ₀ C : ℝ, 0 < ρ₀ ∧ 0 < C ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ (a : Torus) (n : Cover), ‖n‖ = 1 → ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ S : Set Torus, S ⊆ frontier (openRepresentative E) ∩ Metric.ball a (ρ / 2) ∧
        (spatialNormalMeasure μ : Measure Torus)
          ((frontier (openRepresentative E) ∩ Metric.ball a (ρ / 2)) \ S) ≤
          ENNReal.ofReal C * ENNReal.ofReal
            (∫ x in Metric.closedBall a (17 * ρ), ‖N x - n‖ ^ 2
              ∂(spatialNormalMeasure μ : Measure Torus)) ∧
        (∀ c ∈ S, ∀ x ∈ frontier (openRepresentative E), dist x c ≤ ρ →
          |⟪n, shortestLift (x - c)⟫| ≤ ε * dist x c) ∧
        ∃ g : Cover → ℝ, LipschitzWith ⟨2 * ε, by positivity⟩ g ∧
          ∀ x ∈ S, g (normalPlaneProjection n (shortestLift (x - a))) =
            ⟪n, shortestLift (x - a)⟫ := by
  obtain ⟨D, δ, hD, hδ, hd⟩ := isMinimizerAt_two_sided_density hV hE hmin
  obtain ⟨R, A, hR, hA, hu⟩ := isMinimizerAt_perimeter_upper_density hV hE hmin
  let β := (δ ^ 2 * (ε / 8) ^ 6) ^ 2 / ((131072 : ℝ) ^ 2 * (4 * A))
  have hβ : 0 < β := by dsimp [β]; positivity
  let ρ₀ := min (1 / 32 : ℝ) (min (D / 2) (R / 80))
  have hρ₀ : 0 < ρ₀ := by dsimp [ρ₀]; positivity
  refine ⟨ρ₀, 25 * A / β, hρ₀, by positivity, ?_⟩
  intro μ hμ N hN hp hn a n hnorm ρ hρ hρle
  have hd' : ∀ a ∈ frontier (openRepresentative E), ∀ t : ℝ, 0 < t → t ≤ D →
      δ * t ^ 3 ≤ torusVolume.real (E ∩ Metric.ball a t) ∧
      δ * t ^ 3 ≤ torusVolume.real (Eᶜ ∩ Metric.ball a t) := by
    rw [isMinimizerAt_frontier_openRepresentative hV hE hmin]
    exact hd
  apply normalMeasure_lipschitz_approximation_with_cones hE hμ hN hp hn hδ hA hd' (hu μ hμ)
    hρ (hρle.trans (min_le_left _ _))
    (by have := hρle.trans ((min_le_right _ _).trans (min_le_left _ _)); linarith)
    (by have := hρle.trans ((min_le_right _ _).trans (min_le_right _ _)); linarith)
    hε hεhalf hβ
  · dsimp [β]
    have hden : (131072 : ℝ) ^ 2 * (4 * A) ≠ 0 := by positivity
    rw [mul_div_cancel₀ _ hden]
  · exact hnorm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma clamp_height_bound (f : Plane → ℝ) {r : ℝ} (hr : 0 ≤ r) (x : Plane) :
    |max (-r) (min r (f x))| ≤ r := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem isMinimizerAt_trapped_graph_approximation {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {η : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2) :
    ∃ r₀ : ℝ, ∃ C : ℝ≥0∞, 0 < r₀ ∧ C < ⊤ ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ (a : Torus) (n : Cover), ‖n‖ = 1 → ∀ r α : ℝ, 0 < r → r ≤ r₀ → α < 1 / 4 →
        (normalCap a n r (α * r) ⊆ (closure (openRepresentative E))ᶜ ∧
          normalCap a (-n) r (α * r) ⊆ openRepresentative E) →
      ∃ (S : Set Torus) (g : Plane → ℝ),
        LipschitzWith ⟨2 * η, by positivity⟩ g ∧
        (∀ y, |g y| ≤ r / 4) ∧
        S ⊆ frontier (openRepresentative E) ∩ Metric.ball a (r / 2) ∧
        (∀ x ∈ S, g (normalPlaneCoordinates n (shortestLift (x - a))) =
          ⟪n, shortestLift (x - a)⟫) ∧
        (∀ c ∈ S, ∀ x ∈ frontier (openRepresentative E), dist x c ≤ r →
          |⟪n, shortestLift (x - c)⟫| ≤ η * dist x c) ∧
        let e := ENNReal.ofReal (∫ x in Metric.closedBall a (17 * r), ‖N x - n‖ ^ 2
          ∂(spatialNormalMeasure μ : Measure Torus))
        (spatialNormalMeasure μ : Measure Torus)
          ((frontier (openRepresentative E) ∩ Metric.ball a (r / 2)) \ S) ≤ C * e ∧
        (∫⁻ y in Metric.ball (0 : Plane) (r / 4), ENNReal.ofReal (‖fderiv ℝ g y‖ ^ 2)) ≤ C * e ∧
        (∫⁻ y in Metric.ball (0 : Plane) (r / 4),
          ENNReal.ofReal |normalColumnHeight (openRepresentative E) a n r y - g y|) ≤
            C * ENNReal.ofReal r * e := by
  obtain ⟨r₁, C₁, hr₁, hC₁, happ⟩ := isMinimizerAt_lipschitz_approximation_with_cones hV hE hmin hη hηhalf
  obtain ⟨C₂, hC₂, henergy⟩ := isMinimizerAt_normalGraph_full_energy hV hE hmin
  obtain ⟨R, c, hR, hc, hlower⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  let A : ℝ≥0∞ := (planeAreaFactor : ℝ≥0∞) * ENNReal.ofReal (64 / c)
  let C : ℝ≥0∞ := max (ENNReal.ofReal C₁) (max (C₂ * (1 + ENNReal.ofReal C₁)) (A * ENNReal.ofReal C₁))
  have hCt : C < ⊤ := by dsimp [C, A]; finiteness
  have hCbad : ENNReal.ofReal C₁ ≤ C := le_max_left _ _
  have hCgrad : C₂ * (1 + ENNReal.ofReal C₁) ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCheight : A * ENNReal.ofReal C₁ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨min r₁ (1 / 4), C, by positivity, hCt, ?_⟩
  intro μ hμ N hN hp hn a n hnorm r α hr hrr hα htrap
  have hrs : r < 1 / 2 := lt_of_le_of_lt (hrr.trans (min_le_right _ _)) (by norm_num)
  obtain ⟨S, hS, hbad, hcone, g₀, hg₀, heq₀⟩ := happ μ hμ N hN hp hn a n hnorm r hr
    (hrr.trans (min_le_left _ _))
  let K : NNReal := ⟨2 * η, by positivity⟩
  have hg₀x : LipschitzWith K g₀ := hg₀
  let g₁ : Plane → ℝ := fun y ↦ g₀ (normalPlaneEmbedding n y)
  have hg₁ : LipschitzWith K g₁ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hdist : dist (normalPlaneEmbedding n x) (normalPlaneEmbedding n y) = dist x y := by
      simp only [dist_eq_norm]
      change ‖(normalPlaneLinearIsometry n) x - (normalPlaneLinearIsometry n) y‖ = ‖x - y‖
      rw [← map_sub, (normalPlaneLinearIsometry n).norm_map]
    exact (hg₀x.dist_le_mul (normalPlaneEmbedding n x) (normalPlaneEmbedding n y)).trans_eq
      (congrArg (fun t : ℝ ↦ (K : ℝ) * t) hdist)
  let g : Plane → ℝ := fun y ↦ max (-(r / 4)) (min (r / 4) (g₁ y))
  have hg : LipschitzWith ⟨2 * η, by positivity⟩ g := (hg₁.const_min (r / 4)).const_max (-(r / 4))
  have hheight (y : Plane) : |g y| ≤ r / 4 := clamp_height_bound g₁ (by positivity) y
  have heq (x : Torus) (hx : x ∈ S) : g (normalPlaneCoordinates n (shortestLift (x - a))) =
      ⟪n, shortestLift (x - a)⟫ := by
    have hh := trapped_frontier_torus_height (isOpen_openRepresentative E) htrap
      ⟨(hS hx).1, (Metric.ball_subset_ball (by linarith : r / 2 ≤ r)) (hS hx).2⟩
    have hb : |⟪n, shortestLift (x - a)⟫| ≤ r / 4 := hh.trans (by nlinarith)
    dsimp [g, g₁]
    rw [normalPlaneEmbedding_coordinates hnorm, heq₀ x hx,
      min_eq_right (abs_le.mp hb).2, max_eq_right (abs_le.mp hb).1]
  let e := ENNReal.ofReal (∫ x in Metric.closedBall a (17 * r), ‖N x - n‖ ^ 2
    ∂(spatialNormalMeasure μ : Measure Torus))
  have hbad' : (spatialNormalMeasure μ : Measure Torus)
      ((frontier (openRepresentative E) ∩ Metric.ball a (r / 2)) \ S) ≤ ENNReal.ofReal C₁ * e := hbad
  have hlocal : (∫⁻ x in Metric.ball a (r / 2), ENNReal.ofReal (‖N x - n‖ ^ 2)
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ e := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_sq_norm_sub_normal hN hn n).integrableOn (Eventually.of_forall fun _ ↦ sq_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    apply integral_mono_measure
      (Measure.restrict_mono (Metric.ball_subset_closedBall.trans
        (Metric.closedBall_subset_closedBall (by linarith : r / 2 ≤ 17 * r))) le_rfl)
      (Eventually.of_forall fun _ ↦ sq_nonneg _)
      (integrable_sq_norm_sub_normal hN hn n).integrableOn
  have he := henergy μ hμ N hN hp hn n hnorm g ⟨2 * η, by positivity⟩ hg
    (by exact_mod_cast (show 2 * η ≤ 1 by linarith)) a r α hr hrs hα htrap
    (fun y _ ↦ hheight y) S heq
  have hh := normalColumnHeight_graph_L1_le (isOpen_openRepresentative E)
    (spatialNormalMeasure μ) hR hc
    (by rw [isMinimizerAt_frontier_openRepresentative hV hE hmin]; exact hlower μ hμ)
    a hnorm hr hrs hα hηhalf htrap S g hg.continuous.measurable (fun y _ ↦ hheight y) heq hcone
  refine ⟨S, g, hg, hheight, hS, heq, hcone, hbad'.trans (mul_le_mul_left hCbad _), ?_, ?_⟩
  · calc
      _ ≤ C₂ * (e + ENNReal.ofReal C₁ * e) := he.trans (mul_le_mul_right (add_le_add hlocal hbad') _)
      _ = (C₂ * (1 + ENNReal.ofReal C₁)) * e := by simp only [mul_add, add_mul, mul_one, mul_assoc]
      _ ≤ C * e := mul_le_mul_left hCgrad _
  · calc
      _ ≤ ENNReal.ofReal (r / 2) * (A * (ENNReal.ofReal C₁ * e)) :=
        hh.trans (mul_le_mul_right (mul_le_mul_right hbad' A) _)
      _ ≤ ENNReal.ofReal r * (A * (ENNReal.ofReal C₁ * e)) :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith)) _
      _ = (A * ENNReal.ofReal C₁) * ENNReal.ofReal r * e := by ac_rfl
      _ ≤ C * ENNReal.ofReal r * e := mul_le_mul_left (mul_le_mul_left hCheight _) _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_tightly_trapped_graph_approximation {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {η : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2) :
    ∃ r₀ : ℝ, ∃ C : ℝ≥0∞, 0 < r₀ ∧ C < ⊤ ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ (a : Torus) (n : Cover), ‖n‖ = 1 → ∀ r α : ℝ, 0 < r → r ≤ r₀ → 0 ≤ α → α < 1 / 4 →
        (normalCap a n r (α * r) ⊆ (closure (openRepresentative E))ᶜ ∧
          normalCap a (-n) r (α * r) ⊆ openRepresentative E) →
      ∃ (S : Set Torus) (g : Plane → ℝ),
        LipschitzWith ⟨2 * η, by positivity⟩ g ∧
        (∀ y, |g y| ≤ α * r) ∧
        S ⊆ frontier (openRepresentative E) ∩ Metric.ball a (r / 2) ∧
        (∀ x ∈ S, g (normalPlaneCoordinates n (shortestLift (x - a))) =
          ⟪n, shortestLift (x - a)⟫) ∧
        (∀ c ∈ S, ∀ x ∈ frontier (openRepresentative E), dist x c ≤ r →
          |⟪n, shortestLift (x - c)⟫| ≤ η * dist x c) ∧
        let e := ENNReal.ofReal (∫ x in Metric.closedBall a (17 * r), ‖N x - n‖ ^ 2
          ∂(spatialNormalMeasure μ : Measure Torus))
        (spatialNormalMeasure μ : Measure Torus)
          ((frontier (openRepresentative E) ∩ Metric.ball a (r / 2)) \ S) ≤ C * e ∧
        (∫⁻ y in Metric.ball (0 : Plane) (r / 4), ENNReal.ofReal (‖fderiv ℝ g y‖ ^ 2)) ≤ C * e ∧
        (∫⁻ y in Metric.ball (0 : Plane) (r / 4),
          ENNReal.ofReal (columnGraphMismatch (openRepresentative E) a n r g y)) ≤
            C * ENNReal.ofReal α * ENNReal.ofReal r * e := by
  obtain ⟨r₁, C₁, hr₁, hC₁, happ⟩ := isMinimizerAt_lipschitz_approximation_with_cones hV hE hmin hη hηhalf
  obtain ⟨C₂, hC₂, henergy⟩ := isMinimizerAt_normalGraph_full_energy hV hE hmin
  obtain ⟨R, c, hR, hc, hlower⟩ := isMinimizerAt_perimeter_lower_density hV hE hmin
  let A : ℝ≥0∞ := (planeAreaFactor : ℝ≥0∞) * ENNReal.ofReal (64 / c)
  let C : ℝ≥0∞ := max (ENNReal.ofReal C₁) (max (C₂ * (1 + ENNReal.ofReal C₁)) (2 * A * ENNReal.ofReal C₁))
  have hCt : C < ⊤ := by dsimp [C, A]; finiteness
  have hCbad : ENNReal.ofReal C₁ ≤ C := le_max_left _ _
  have hCgrad : C₂ * (1 + ENNReal.ofReal C₁) ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCheight : 2 * A * ENNReal.ofReal C₁ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨min r₁ (1 / 4), C, by positivity, hCt, ?_⟩
  intro μ hμ N hN hp hn a n hnorm r α hr hrr hα0 hα htrap
  have hrs : r < 1 / 2 := lt_of_le_of_lt (hrr.trans (min_le_right _ _)) (by norm_num)
  obtain ⟨S, hS, hbad, hcone, g₀, hg₀, heq₀⟩ := happ μ hμ N hN hp hn a n hnorm r hr
    (hrr.trans (min_le_left _ _))
  let K : NNReal := ⟨2 * η, by positivity⟩
  have hg₀x : LipschitzWith K g₀ := hg₀
  let g₁ : Plane → ℝ := fun y ↦ g₀ (normalPlaneEmbedding n y)
  have hg₁ : LipschitzWith K g₁ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hdist : dist (normalPlaneEmbedding n x) (normalPlaneEmbedding n y) = dist x y := by
      simp only [dist_eq_norm]
      change ‖(normalPlaneLinearIsometry n) x - (normalPlaneLinearIsometry n) y‖ = ‖x - y‖
      rw [← map_sub, (normalPlaneLinearIsometry n).norm_map]
    exact (hg₀x.dist_le_mul (normalPlaneEmbedding n x) (normalPlaneEmbedding n y)).trans_eq
      (congrArg (fun t : ℝ ↦ (K : ℝ) * t) hdist)
  let g : Plane → ℝ := fun y ↦ max (-(α*r)) (min (α*r) (g₁ y))
  have hg : LipschitzWith ⟨2 * η, by positivity⟩ g := (hg₁.const_min (α*r)).const_max (-(α*r))
  have hheight (y : Plane) : |g y| ≤ α*r := clamp_height_bound g₁ (by positivity) y
  have heq (x : Torus) (hx : x ∈ S) : g (normalPlaneCoordinates n (shortestLift (x - a))) =
      ⟪n, shortestLift (x - a)⟫ := by
    have hh := trapped_frontier_torus_height (isOpen_openRepresentative E) htrap
      ⟨(hS hx).1, (Metric.ball_subset_ball (by linarith : r / 2 ≤ r)) (hS hx).2⟩
    have hb : |⟪n, shortestLift (x - a)⟫| ≤ α*r := hh
    dsimp [g, g₁]
    rw [normalPlaneEmbedding_coordinates hnorm, heq₀ x hx,
      min_eq_right (abs_le.mp hb).2, max_eq_right (abs_le.mp hb).1]
  let e := ENNReal.ofReal (∫ x in Metric.closedBall a (17 * r), ‖N x - n‖ ^ 2
    ∂(spatialNormalMeasure μ : Measure Torus))
  have hbad' : (spatialNormalMeasure μ : Measure Torus)
      ((frontier (openRepresentative E) ∩ Metric.ball a (r / 2)) \ S) ≤ ENNReal.ofReal C₁ * e := hbad
  have hlocal : (∫⁻ x in Metric.ball a (r / 2), ENNReal.ofReal (‖N x - n‖ ^ 2)
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ e := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_sq_norm_sub_normal hN hn n).integrableOn (Eventually.of_forall fun _ ↦ sq_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    apply integral_mono_measure
      (Measure.restrict_mono (Metric.ball_subset_closedBall.trans
        (Metric.closedBall_subset_closedBall (by linarith : r / 2 ≤ 17 * r))) le_rfl)
      (Eventually.of_forall fun _ ↦ sq_nonneg _)
      (integrable_sq_norm_sub_normal hN hn n).integrableOn
  have he := henergy μ hμ N hN hp hn n hnorm g ⟨2 * η, by positivity⟩ hg
    (by exact_mod_cast (show 2 * η ≤ 1 by linarith)) a r α hr hrs hα htrap
    (fun y _ ↦ (hheight y).trans (by nlinarith)) S heq
  have hh := columnGraphMismatch_L1_le (isOpen_openRepresentative E)
    (spatialNormalMeasure μ) hR hc
    (by rw [isMinimizerAt_frontier_openRepresentative hV hE hmin]; exact hlower μ hμ)
    a hnorm hr hrs hα0 hα hηhalf htrap S g hg.continuous.measurable (fun y _ ↦ hheight y) heq hcone
  refine ⟨S, g, hg, hheight, hS, heq, hcone, hbad'.trans (mul_le_mul_left hCbad _), ?_, ?_⟩
  · calc
      _ ≤ C₂ * (e + ENNReal.ofReal C₁ * e) := he.trans (mul_le_mul_right (add_le_add hlocal hbad') _)
      _ = (C₂ * (1 + ENNReal.ofReal C₁)) * e := by simp only [mul_add, add_mul, mul_one, mul_assoc]
      _ ≤ C * e := mul_le_mul_left hCgrad _
  · calc
      _ ≤ ENNReal.ofReal (2*α*r) * (A * (ENNReal.ofReal C₁ * e)) :=
        hh.trans (mul_le_mul_right (mul_le_mul_right hbad' A) _)
      _ = (2 * A * ENNReal.ofReal C₁) * ENNReal.ofReal α * ENNReal.ofReal r * e := by
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2*α), ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
        ac_rfl
      _ ≤ C * ENNReal.ofReal α * ENNReal.ofReal r * e :=
        mul_le_mul_left (mul_le_mul_left (mul_le_mul_left hCheight _) _) _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem isMinimizerAt_smooth_trapped_approximation {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ r₀ D : ℝ, 0 < r₀ ∧ 0 ≤ D ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ n : Cover, ‖n‖ = 1 → ∀ r α e : ℝ, 0 < r → r ≤ r₀ → 0 ≤ α → α < 1/4 →
        0 < e → e ≤ 1/2 →
        (normalCap (quotientMap cubeCenter) n r (α*r) ⊆ (closure (openRepresentative E))ᶜ ∧
          normalCap (quotientMap cubeCenter) (-n) r (α*r) ⊆ openRepresentative E) →
        (∫ x in Metric.closedBall (quotientMap cubeCenter) (17*r), ‖N x-n‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 →
      ∃ G : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) G ∧ LipschitzWith 1 G ∧
        (∀ y, |G y| ≤ α*r) ∧
        (∫ y in Metric.ball (0 : Plane) (r/8), ‖fderiv ℝ G y‖^2) ≤ r^2*e^2*D ∧
        (let B := r^3*e^2*(D*α+e*(volume : Measure Plane).real (Metric.ball 0 (1/4)))
         (∫ y in Metric.ball (0 : Plane) (r/4),
            |G y-normalColumnHeight (openRepresentative E) (quotientMap cubeCenter) n r y|) ≤ B ∧
         ∀ s : ℝ, s ≤ r/4 → torusVolume.real
           (((openRepresentative E) ∆ torusGraphRegion cubeCenter n G) ∩
             Metric.ball (quotientMap cubeCenter) s) ≤ B) := by
  obtain ⟨R,C,hR,hC,happ⟩ := isMinimizerAt_tightly_trapped_graph_approximation
    hV hE hmin (by norm_num : (0:ℝ)<1/2) le_rfl
  refine ⟨min R (1/4),C.toReal,by positivity,ENNReal.toReal_nonneg,?_⟩
  intro μ hμ N hN hp hunit n hn r α e hr hrr hα0 hα he hes htrap htilt
  have hrs : r < 1 := lt_of_le_of_lt (hrr.trans (min_le_right _ _)) (by norm_num)
  obtain ⟨S,g,hg,hh,hS,hgood,hcone,hbad,henergy,hmismatch⟩ :=
    happ μ hμ N hN hp hunit (quotientMap cubeCenter) n hn r α hr
      (hrr.trans (min_le_left _ _)) hα0 hα htrap
  have hg1 : LipschitzWith 1 g := hg.weaken (by
    change (2:ℝ)*(1/2) ≤ 1
    norm_num)
  let T := ∫ x in Metric.closedBall (quotientMap cubeCenter) (17*r), ‖N x-n‖^2
    ∂(spatialNormalMeasure μ : Measure Torus)
  have hT : 0 ≤ T := integral_nonneg fun x ↦ sq_nonneg _
  have hgE : (∫ y in Metric.ball (0 : Plane) (r/4), ‖fderiv ℝ g y‖^2) ≤ C.toReal*T := by
    rw [← ofReal_integral_eq_lintegral_ofReal (lipschitz_gradient_sq_integrable_ball hg1 (r/4))
      (Eventually.of_forall fun y ↦ sq_nonneg _)] at henergy
    have ht := ENNReal.toReal_mono (by finiteness) henergy
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (integral_nonneg fun y ↦ sq_nonneg _)] using ht
  have hgM : (∫ y in Metric.ball (0 : Plane) (r/4),
      columnGraphMismatch (openRepresentative E) (quotientMap cubeCenter) n r g y) ≤
        C.toReal*α*r*T := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (columnGraphMismatch_integrable_ball (isOpen_openRepresentative E).measurableSet
        _ n hr.le hg1.continuous.measurable (r/4))
      (Eventually.of_forall fun y ↦ columnGraphMismatch_nonneg _ _ _ _ _ _)] at hmismatch
    have ht := ENNReal.toReal_mono (by finiteness) hmismatch
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (integral_nonneg fun x ↦ sq_nonneg _),ENNReal.toReal_ofReal hα0,
      ENNReal.toReal_ofReal hr.le,ENNReal.toReal_ofReal
        (integral_nonneg fun y ↦ columnGraphMismatch_nonneg _ _ _ _ _ _)] using ht
  have hδ : 0 < r*e^3 := by positivity
  have he3 : e^3 ≤ 1/8 := by nlinarith [mul_le_mul_of_nonneg_left hes he.le, sq_nonneg (e-1/2)]
  have hδr : r*e^3 ≤ r/8 := by nlinarith
  obtain ⟨G,hG,hGL,hheight,hGE,hGM⟩ := exists_physical_smooth_graph
    (isOpen_openRepresentative E).measurableSet hn hg1 hr hrs hδ hδr hα.le hh
  have hB : (∫ y in Metric.ball (0 : Plane) (r/4), columnGraphMismatch
      (openRepresentative E) (quotientMap cubeCenter) n r g y)+
      (r*e^3)*r^2*(volume : Measure Plane).real (Metric.ball 0 (1/4)) ≤
      r^3*e^2*(C.toReal*α+e*(volume : Measure Plane).real (Metric.ball 0 (1/4))) := by
    have hx := hgM.trans (mul_le_mul_of_nonneg_left htilt (by positivity : 0 ≤ C.toReal*α*r))
    calc
      _ ≤ C.toReal*α*r*(r^2*e^2)+(r*e^3)*r^2*(volume : Measure Plane).real (Metric.ball 0 (1/4)) := add_le_add hx le_rfl
      _ = _ := by ring
  refine ⟨G,hG,hGL,hheight,?_,hGM.1.trans hB,fun s hs ↦ (hGM.2 s hs).trans hB⟩
  exact hGE.trans (hgE.trans ((mul_le_mul_of_nonneg_left htilt ENNReal.toReal_nonneg).trans_eq (by ring)))

end CubicTorus

end
end

end

end OAI
