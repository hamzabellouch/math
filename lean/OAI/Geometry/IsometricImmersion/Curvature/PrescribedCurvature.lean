import OAI.Geometry.IsometricImmersion.Volterra.VolterraGlue
import OAI.Geometry.IsometricImmersion.Metrics.WarpedMetric

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.ODE
open SmoothLocal.Geometry

theorem coordinatePoint_eta (p : Coord) : coordinatePoint (p 0) (p 1) = p := by
  ext i
  fin_cases i <;> simp [coordinatePoint]

theorem coordinatePoint_hasDerivAt_x (x y : ℝ) :
    HasDerivAt (fun t => coordinatePoint t y) (Pi.single 0 (1 : ℝ) : Coord) x := by
  simpa [coordinatePoint] using
    ((hasDerivAt_id x).smul_const (Pi.single 0 (1 : ℝ) : Coord)).add_const
      (y • (Pi.single 1 (1 : ℝ) : Coord))

theorem globalPrescribedState_hasDerivAt {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    {x y : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hy : y ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => globalPrescribedState K (t, y))
      (curvatureField (fun t => K (coordinatePoint t y)) x
        (globalPrescribedState K (x, y))) x := by
  let r := interiorRadius x
  have hr : 0 < r := interiorRadius_pos x
  have hr1 : r < 1 := interiorRadius_lt_one (abs_lt.mpr hx)
  have hxr : x ∈ Ioo (-r) r := abs_lt.mp (abs_lt_interiorRadius (abs_lt.mpr hx))
  have hev : (fun t => globalPrescribedState K (t, y)) =ᶠ[𝓝 x]
      prescribedLocalState K r hr y := by
    filter_upwards [isOpen_Ioo.mem_nhds hxr] with t ht
    exact globalPrescribedState_eq_local hK hbound r hr hr1 ⟨ht, hy⟩
  have hd := (prescribedLocalState_hasDerivAt hK hbound r hr hr1 hy hxr).congr_of_eventuallyEq hev
  rw [globalPrescribedState_eq_local hK hbound r hr hr1 ⟨hxr, hy⟩]
  exact hd

theorem globalPrescribedState_initial {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    globalPrescribedState K (0, y) = (1, 0) :=
  prescribedLocalState_initial hK hbound (interiorRadius 0) (interiorRadius_pos 0)
    (by norm_num [interiorRadius]) hy

theorem coordinateSlice_hasDerivAt_x {f : Coord → ℝ}
    (hf : ContDiffOn ℝ ∞ f square) {p : Coord} (hp : p ∈ square) :
    HasDerivAt (fun t => f (coordinatePoint t (p 1))) (coordPartial 0 f p) (p 0) := by
  have hd : DifferentiableAt ℝ f (coordinatePoint (p 0) (p 1)) := by
    rw [coordinatePoint_eta]
    exact (hf.contDiffAt (coordinate_square_isOpen.mem_nhds hp)).differentiableAt (by simp)
  have hh := hd.hasFDerivAt.comp_hasDerivAt (p 0)
    (coordinatePoint_hasDerivAt_x (p 0) (p 1))
  simpa only [coordinatePoint_eta, Function.comp_def, coordPartial] using hh

theorem prescribedFactor_firstPartial {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    {p : Coord} (hp : p ∈ square) :
    coordPartial 0 (prescribedFactor K) p = (globalPrescribedState K (p 0, p 1)).2 := by
  have hd := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt (p 0)
    (globalPrescribedState_hasDerivAt hK hbound (hp 0) (hp 1))
  have hd' : HasDerivAt (fun t => prescribedFactor K (coordinatePoint t (p 1)))
      (globalPrescribedState K (p 0, p 1)).2 (p 0) := by
    simpa [Function.comp_def, prescribedFactor, globalPrescribedScalar, coordinatePoint,
      curvatureField] using hd
  exact (coordinateSlice_hasDerivAt_x (prescribedFactor_contDiffOn hK hbound) hp).unique hd'

theorem prescribedFactor_secondPartial {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    {p : Coord} (hp : p ∈ square) :
    coordPartial 0 (coordPartial 0 (prescribedFactor K)) p = -K p * prescribedFactor K p := by
  have hd := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt (p 0)
    (globalPrescribedState_hasDerivAt hK hbound (hp 0) (hp 1))
  have hd' : HasDerivAt (fun t => (globalPrescribedState K (t, p 1)).2)
      (-K p * prescribedFactor K p) (p 0) := by
    simpa [Function.comp_def, curvatureField, coordinatePoint_eta, prescribedFactor,
      globalPrescribedScalar] using hd
  have hev : (fun t => coordPartial 0 (prescribedFactor K) (coordinatePoint t (p 1)))
      =ᶠ[𝓝 (p 0)] (fun t => (globalPrescribedState K (t, p 1)).2) := by
    filter_upwards [isOpen_Ioo.mem_nhds (hp 0)] with t ht
    simpa [coordinatePoint] using prescribedFactor_firstPartial hK hbound
      (coordinatePoint_mem_square ht (hp 1))
  have hpartial : ContDiffOn ℝ ∞ (coordPartial 0 (prescribedFactor K)) square :=
    partial_contDiffOn (prescribedFactor_contDiffOn hK hbound) coordinate_square_isOpen 0
  exact (coordinateSlice_hasDerivAt_x hpartial hp).unique (hd'.congr_of_eventuallyEq hev)

theorem prescribedFactor_initial {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    {y : ℝ} (hy : y ∈ Ioo (-1 : ℝ) 1) :
    prescribedFactor K (coordinatePoint 0 y) = 1 ∧
      coordPartial 0 (prescribedFactor K) (coordinatePoint 0 y) = 0 := by
  have hz : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  have hs := globalPrescribedState_initial hK hbound hy
  constructor
  · simpa [prescribedFactor, globalPrescribedScalar, coordinatePoint] using congrArg Prod.fst hs
  · rw [prescribedFactor_firstPartial hK hbound (coordinatePoint_mem_square hz hy)]
    simpa [coordinatePoint] using congrArg Prod.snd hs

def prescribedCurvatureMetric (K : Coord → ℝ) : MetricField := warpedMetric (prescribedFactor K)

theorem prescribedCurvatureMetric_smoothPositiveOn {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000) :
    SmoothPositiveOn (prescribedCurvatureMetric K) square :=
  warpedMetric_smoothPositiveOn (prescribedFactor_contDiffOn hK hbound)
    (fun _ hp => ne_of_gt (prescribedFactor_bounds hK hbound hp).2.2)

theorem prescribedCurvatureMetric_gaussianCurvature {K : Coord → ℝ}
    (hK : ContDiffOn ℝ ∞ K square)
    (hbound : ∀ p ∈ square, |K p| ≤ (1 : ℝ) / 1000)
    {p : Coord} (hp : p ∈ square) :
    gaussianCurvature (prescribedCurvatureMetric K) p = K p := by
  have hne : ∀ q ∈ square, prescribedFactor K q ≠ 0 :=
    fun q hq => ne_of_gt (prescribedFactor_bounds hK hbound hq).2.2
  rw [prescribedCurvatureMetric,
    gaussianCurvature_warpedMetric (prescribedFactor_contDiffOn hK hbound)
      coordinate_square_isOpen hne hp,
    prescribedFactor_secondPartial hK hbound hp]
  field_simp [hne p hp]

end SmoothLocal.ODE

end

end OAI
