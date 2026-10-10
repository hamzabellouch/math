import Mathlib
import OAI.Geometry.BallPacking.Continuation.CompatibleHomotopy

namespace OAI

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity.HolderCompletion
open scoped ContDiff Topology
open Filter
open scoped BoundedContinuousFunction
open Set Function
section
variable {T X Y : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

lemma initial_implicit_branch (F : T × X → Y) (hF : ContDiff ℝ ∞ F)
    (L : X ≃L[ℝ] Y) (h0 : ∀ x, F (0,x)=L x) :
    ∃ U : T → X, U 0=0 ∧ ContinuousAt U 0 ∧ ∀ᶠ t in 𝓝 (0:T), F (t,U t)=0 := by
  let D := fderiv ℝ F (0,0)
  have hd : HasStrictFDerivAt F D (0,0) := hF.hasStrictFDerivAt (by simp)
  have hdi : HasFDerivAt (fun x : X => F (0,x)) (D.comp (ContinuousLinearMap.inr ℝ T X)) 0 :=
    hd.hasFDerivAt.comp 0 (ContinuousLinearMap.inr ℝ T X).hasFDerivAt
  have hL : HasFDerivAt (fun x : X => F (0,x)) L.toContinuousLinearMap 0 := by
    have he : (fun x : X => F (0,x)) = L := funext h0
    rw [he]
    exact L.hasFDerivAt
  have hDL : D.comp (ContinuousLinearMap.inr ℝ T X) = L.toContinuousLinearMap := hdi.unique hL
  have hi : (D.comp (ContinuousLinearMap.inr ℝ T X)).IsInvertible := by
    rw [hDL]
    exact ⟨L,rfl⟩
  let U := hd.implicitFunctionOfProdDomain hi
  have hU0 : U 0=0 :=
    (hd.eventually_apply_eq_iff_implicitFunctionOfProdDomain hi).self_of_nhds.mp rfl
  have hU : ContinuousAt U 0 := by
    have ht := hd.tendsto_implicitFunctionOfProdDomain hi
    change Tendsto U (𝓝 0) (𝓝 (U 0))
    rw [hU0]
    exact ht
  refine ⟨U,hU0,hU,?_⟩
  have hz : F (0,0)=0 := (h0 0).trans (map_zero L)
  simpa only [hz] using hd.eventually_apply_implicitFunctionOfProdDomain hi

end
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance gmChartInst1 : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance gmChartInst2 : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance gmChartInst3 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance gmChartInst4 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance gmChartInst5 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance gmChartInst6 : NormedSpace ℝ (HMap ℂ E) := inferInstance
local instance gmChartInst7 : NormedAddCommGroup (HMap ℂ (E →L[ℝ] E)) := inferInstance
local instance gmChartInst8 : NormedSpace ℝ (HMap ℂ (E →L[ℝ] E)) := inferInstance
variable (b b₁ : ContDiffBump (0:ℂ)) (p q : E)
local instance gmChartInst9 : NormedAddCommGroup (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gmChartInst10 : NormedSpace ℝ (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gmChartInst11 : AddCommGroup (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst9 b).toAddCommGroup
local instance gmChartInst12 : Module ℝ (markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst10 b).toModule
local instance gmChartInst13 : NormedAddCommGroup (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gmChartInst14 : NormedSpace ℝ (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gmChartInst15 : AddCommGroup (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst13 b).toAddCommGroup
local instance gmChartInst16 : Module ℝ (supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst14 b).toModule
local instance gmChartInst17 : NormedAddCommGroup (ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gmChartInst18 : NormedSpace ℝ (ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gmChartInst19 : AddCommGroup (ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst17 b).toAddCommGroup
local instance gmChartInst20 : Module ℝ (ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) := (gmChartInst18 b).toModule
variable {P : ℝ × E → E →L[ℝ] E} (hP : BoundedCThree P)

def globalNonlinearity (v : ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) : HMap ℂ E :=
  bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip
    (globalCoefficient b₁ p q hP (v.1,v.2.val)) (markedDX p q 0 v.2.val)

def globalChart (v : ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) :
    supportedHolder (E := E) (Metric.closedBall (0:ℂ) b.rOut) :=
  (markedCR (E := E) (K := Metric.closedBall (0:ℂ) b.rOut)) v.2-
    supportedSourceCutoff b (globalNonlinearity b b₁ p q hP v)

lemma globalChart_contDiff (hPc : HasCompactSupport P) : ContDiff ℝ ∞ (globalChart b b₁ p q hP) := by
  have hv : ContDiff ℝ ∞ (fun v : ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut) => (v.1,v.2.val)) :=
    contDiff_fst.prodMk ((markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)).subtypeL.contDiff.comp contDiff_snd)
  have hc := (globalCoefficient_contDiff b₁ p q hP hPc).comp hv
  have hd : ContDiff ℝ ∞ (fun v : ℝ × markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut) => markedDX p q 0 v.2.val) :=
    (markedDX_contDiff p q 0).comp ((markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)).subtypeL.contDiff.comp contDiff_snd)
  have hN : ContDiff ℝ ∞ (globalNonlinearity b b₁ p q hP) :=
    (((bilinCLM (X := ℂ) (α := (1:ℝ)/3) (ContinuousLinearMap.apply (E := E) ℝ E).flip).contDiff.comp hc).clm_apply hd)
  exact ((markedCR (E := E) (K := Metric.closedBall (0:ℂ) b.rOut)).contDiff.comp contDiff_snd).sub
    ((supportedSourceCutoff (E := E) b).contDiff.comp hN)

lemma globalChart_value (t : ℝ) (w : markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) (z : ℂ) :
    valueCLM _ (globalChart b b₁ p q hP (t,w)).val z=valueCLM _ (standardJetCR w.val) z-
      b z • P (t,cValue (globalMarkedJet b₁ p q w.val) z) (fderiv ℝ (markedCurve p q w.val) z 1) := by
  change valueCLM _ (standardJetCR w.val) z-b z • valueCLM _ (globalNonlinearity b b₁ p q hP (t,w)) z=_
  simp only [globalNonlinearity,bilinCLM_value,globalCoefficient_value,markedDX_value,zero_add]
  rfl

lemma globalChart_at_zero (hP0 : ∀ x,P (0,x)=0)
    (w : markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut)) :
    globalChart b b₁ p q hP (0,w)=markedCR (E := E) (K := Metric.closedBall (0:ℂ) b.rOut) w := by
  apply Subtype.ext
  apply value_ext
  intro z
  have hV := globalChart_value b b₁ p q hP 0 w z
  have hz := hP0 (cValue (globalMarkedJet b₁ p q w.val) z)
  have hzero : P (0,cValue (globalMarkedJet b₁ p q w.val) z)
      (fderiv ℝ (markedCurve p q w.val) z 1)=0 := by
    rw [hz,zero_apply]
  rw [hzero,smul_zero,sub_zero] at hV
  exact hV

lemma globalChart_actual_value
    (hb₁ : Metric.closedBall (0:ℂ) b.rOut⊆Metric.closedBall (0:ℂ) b₁.rIn)
    {B : ℝ} (hPB : ∀ t x,B<‖x‖ → P (t,x)=0) (t : ℝ)
    (w : markedModel (E := E) (Metric.closedBall (0:ℂ) b.rOut))
    (he : ∀ z,b.rIn≤‖z‖ → B<‖markedCurve p q w.val z‖) (z : ℂ) :
    valueCLM _ (globalChart b b₁ p q hP (t,w)).val z=
      fderiv ℝ (markedCurve p q w.val) z Complex.I-
        (Complex.I • fderiv ℝ (markedCurve p q w.val) z 1+
          P (t,markedCurve p q w.val z) (fderiv ℝ (markedCurve p q w.val) z 1)) := by
  have hz0 : z∉Metric.closedBall (0:ℂ) b.rIn → P (t,markedCurve p q w.val z)=0 := by
    intro hz
    apply hPB
    apply he
    exact (lt_of_not_ge (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)).le
  have hN : b z • P (t,cValue (globalMarkedJet b₁ p q w.val) z)
      (fderiv ℝ (markedCurve p q w.val) z 1)=
      P (t,markedCurve p q w.val z) (fderiv ℝ (markedCurve p q w.val) z 1) := by
    by_cases hz : z∈Metric.closedBall (0:ℂ) b.rOut
    · apply cutoff_action_eq b _ hz0
      rw [globalMarkedJet_eq_marked b₁ p q w.val (hb₁ hz)]
    · have hb0 : b z=0 := image_eq_zero_of_notMem_tsupport (by rwa [b.tsupport_eq])
      have hz' : z∉Metric.closedBall (0:ℂ) b.rIn :=
        fun h => hz (Metric.closedBall_subset_closedBall b.rIn_lt_rOut.le h)
      rw [hb0,hz0 hz',zero_apply,zero_smul]
  have hS := markedCurve_standardResidual p q w.val z
  calc
    _ = valueCLM _ (standardJetCR w.val) z-b z •
        P (t,cValue (globalMarkedJet b₁ p q w.val) z) (fderiv ℝ (markedCurve p q w.val) z 1) :=
      globalChart_value b b₁ p q hP t w z
    _ = (fderiv ℝ (markedCurve p q w.val) z Complex.I-
        Complex.I • fderiv ℝ (markedCurve p q w.val) z 1)-
        P (t,markedCurve p q w.val z) (fderiv ℝ (markedCurve p q w.val) z 1) :=
      congrArg₂ (· - ·) hS.symm hN
    _ = _ := sub_sub _ _ _

end
section
variable {n : ℕ}
local instance gle1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance gle2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance gle3 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance gle4 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance gle5 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance gle6 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
  (hJc : HasCompactSupport (fun x => J x-standardJ n))
include hJs hJ hJc in
theorem fullCoefficientBound : BoundedCThree (fullCoefficient J) :=
  boundedCThree_of_compactSupport (fullCoefficient_smooth hJs hJ) (fullCoefficient_compact hJc)
variable (b b₁ : ContDiffBump (0:ℂ)) (p q : Phase n)
local instance gle7 : NormedAddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gle8 : NormedSpace ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gle9 : NormedAddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gle10 : NormedSpace ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gle11 : AddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (gle7 (n := n) b).toAddCommGroup
local instance gle12 : Module ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (gle8 (n := n) b).toModule
local instance gle13 : AddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (gle9 (n := n) b).toAddCommGroup
local instance gle14 : Module ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (gle10 (n := n) b).toModule

def fullLineEquation := globalChart b b₁ p q (fullCoefficientBound hJs hJ hJc)

lemma fullLineEquation_contDiff : ContDiff ℝ ∞ (fullLineEquation hJs hJ hJc b b₁ p q) :=
  globalChart_contDiff b b₁ p q (fullCoefficientBound hJs hJ hJc) (fullCoefficient_compact hJc)

lemma fullLineEquation_initial
    (w : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) :
    fullLineEquation hJs hJ hJc b b₁ p q (0,w)=
      markedCR (E := Phase n) (K := Metric.closedBall (0:ℂ) b.rOut) w :=
  globalChart_at_zero b b₁ p q (fullCoefficientBound hJs hJ hJc) (fullCoefficient_zero hJ) w

variable (hb₁ : Metric.closedBall (0:ℂ) b.rOut⊆Metric.closedBall (0:ℂ) b₁.rIn)
  {B : ℝ} (hstd : ∀ x,B<‖x‖ → J x=standardJ n)
  {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
  (w : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
  (he : ∀ z,b.rIn≤‖z‖ → B<‖markedCurve p q w.val z‖)

include hb₁ hstd ht he in
lemma fullLineEquation_value (z : ℂ) :
    valueCLM _ (fullLineEquation hJs hJ hJc b b₁ p q (t,w)).val z=
      fderiv ℝ (markedCurve p q w.val) z Complex.I-
        lineHomotopy J (fullTime t) (markedCurve p q w.val z)
          (fderiv ℝ (markedCurve p q w.val) z 1) := by
  have hx := globalChart_actual_value b b₁ p q (fullCoefficientBound hJs hJ hJc)
    hb₁ (fullCoefficient_outside hstd) t w he z
  have hc := congrArg (fun A : End n => A (fderiv ℝ (markedCurve p q w.val) z 1))
    (fullCoefficient_exact (J := J) ht (markedCurve p q w.val z))
  change Complex.I • fderiv ℝ (markedCurve p q w.val) z 1+
    fullCoefficient J (t,markedCurve p q w.val z) (fderiv ℝ (markedCurve p q w.val) z 1)=_ at hc
  exact hx.trans (congrArg (fun v : Phase n => fderiv ℝ (markedCurve p q w.val) z Complex.I-v) hc)

include hb₁ hstd ht he in
lemma fullLineEquation_zero_iff
    (ha : markedSlope p q w.val≠0) :
    fullLineEquation hJs hJ hJc b b₁ p q (t,w)=0 ↔
      AffineLineCurve (lineHomotopy J (fullTime t)) p q (markedCurve p q w.val) := by
  have hc := lineHomotopy_compatible hJ (fullTime_range t)
  have hs := lineHomotopy_slice_contDiff hJs hJ (fullTime_range t)
  have hstd' : ∀ x,B<‖x‖ → lineHomotopy J (fullTime t) x=standardJ n := by
    intro x hx
    change interpolateJ (J x) (fullTime t)=standardJ n
    rw [hstd x hx]
    exact interpolateJ_standard_initial
      ⟨lt_of_lt_of_le (by norm_num) (fullTime_range t).1,(fullTime_range t).2⟩
  constructor
  · intro hz
    have hcr (z : ℂ) : fderiv ℝ (markedCurve p q w.val) z Complex.I=
        lineHomotopy J (fullTime t) (markedCurve p q w.val z)
          (fderiv ℝ (markedCurve p q w.val) z 1) := by
      have hv := fullLineEquation_value hJs hJ hJc b b₁ p q hb₁ hstd ht w he z
      have hzero : valueCLM _ (fullLineEquation hJs hJ hJc b b₁ p q (t,w)).val z=0 := by
        rw [hz]; rfl
      exact sub_eq_zero.mp (hv.symm.trans hzero)
    refine ⟨completed_markedCurve_contDiff hs hc hstd' p q w.val ha hcr,?_,
      markedCurve_zero p q w.property.1,markedCurve_one p q w.val,
      markedSlope p q w.val,ha,markedCurve_asymptote p q w.val⟩
    intro z
    exact ⟨(markedCurve_hasFDerivAt p q w.val z).differentiableAt,
      realCR_axis_implies_all _ (hc _).1 _ (hcr z)⟩
  · intro hu
    apply Subtype.ext
    apply value_ext
    intro z
    have hv := fullLineEquation_value hJs hJ hJc b b₁ p q hb₁ hstd ht w he z
    have hcr := (hu.2.1 z).2 1
    simp only [mul_one] at hcr
    exact hv.trans (sub_eq_zero.mpr hcr)

end
section

section Translation
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
lemma spatial_derivative_translation {f : X → Y} (hf : ContDiff ℝ ∞ f) (w : X) :
    fderiv ℝ (fun h => f (w+h)) 0=fderiv ℝ f w := by
  have hdw : HasFDerivAt f (fderiv ℝ f w) (w+0) := by
    simpa only [add_zero] using (hf.differentiable (by simp) w).hasFDerivAt
  have hh := hdw.comp 0 ((hasFDerivAt_id (0:X)).const_add w)
  simpa only [Function.comp_def,ContinuousLinearMap.comp_id] using hh.fderiv
end Translation
variable {n : ℕ}
local instance glf1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance glf2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance glf3 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance glf4 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
  (hJc : HasCompactSupport (fun x => J x-standardJ n))
  (b b₁ : ContDiffBump (0:ℂ)) (p q : Phase n)
local instance glf5 : NormedAddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance glf6 : NormedSpace ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance glf7 : NormedAddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance glf8 : NormedSpace ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance glf9 : AddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (glf5 (n := n) b).toAddCommGroup
local instance glf10 : Module ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (glf6 (n := n) b).toModule
local instance glf11 : AddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (glf7 (n := n) b).toAddCommGroup
local instance glf12 : Module ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (glf8 (n := n) b).toModule
local instance glf13 : TopologicalSpace (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) :=
  (glf5 (n := n) b).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
local instance glf14 : TopologicalSpace (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) :=
  (glf7 (n := n) b).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
variable (hb₁ : Metric.closedBall (0:ℂ) b.rOut⊆Metric.closedBall (0:ℂ) b₁.rIn)
  {B : ℝ} (hstd : ∀ x,B<‖x‖ →J x=standardJ n)
  {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
  (w : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
  (he : MarkedEscapeNeighborhood b p q w.val B)

include hstd in
lemma fullTime_slice_outside : ∀ x,B<‖x‖ →lineHomotopy J (fullTime t) x=standardJ n := by
  intro x hx
  change interpolateJ (J x) (fullTime t)=standardJ n
  rw [hstd x hx]
  exact interpolateJ_standard (fullTime_range t)

include hb₁ hstd ht he in
lemma fullLineEquation_local_chart_eq :
    (fun h => fullLineEquation hJs hJ hJc b b₁ p q (t,w+h)) =ᶠ[𝓝 0]
      actualMarkedChart (lineHomotopy_slice_contDiff hJs hJ (fullTime_range t))
        (fullTime_slice_outside hstd (t := t)) b p q w := by
  filter_upwards [he] with h hh
  apply Subtype.ext
  apply value_ext
  intro z
  have hv := fullLineEquation_value hJs hJ hJc b b₁ p q hb₁ hstd ht (w+h)
    (fun z hz => (hh z hz).1) z
  have ha := actualMarkedChart_value (lineHomotopy_slice_contDiff hJs hJ (fullTime_range t))
    (fullTime_slice_outside hstd (t := t)) b p q w h hh z
  exact hv.trans ha.symm

include hb₁ hstd ht he in
lemma fullLineEquation_spatial_fredholm : IsIndexZeroFredholm
    (fderiv ℝ (fun v => fullLineEquation hJs hJ hJc b b₁ p q (t,v)) w) := by
  let f := fun v => fullLineEquation hJs hJ hJc b b₁ p q (t,v)
  have hf : ContDiff ℝ ∞ f := (fullLineEquation_contDiff hJs hJ hJc b b₁ p q).comp
    (contDiff_const.prodMk contDiff_id)
  have hs := lineHomotopy_slice_contDiff hJs hJ (fullTime_range t)
  have ho := fullTime_slice_outside hstd (t := t)
  have hEq := fullLineEquation_local_chart_eq hJs hJ hJc b b₁ p q hb₁ hstd ht w he
  have hder := (spatial_derivative_translation hf w).symm.trans hEq.fderiv_eq
  have hfred := actualMarkedChart_derivative_fredholm hs
    (lineHomotopy_compatible hJ (fullTime_range t)) ho b p q w he
  change IsIndexZeroFredholm (fderiv ℝ f w)
  rw [hder]
  exact hfred

end

variable {n : ℕ}
local instance gid1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance gid2 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
variable (b : ContDiffBump (0:ℂ))
local instance gid3 : NormedAddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gid4 : NormedSpace ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gid5 : NormedAddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance gid6 : NormedSpace ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance

def fullLineDomain (p q : Phase n) (M δ : ℝ) :
    Set (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) :=
  {w | w.val∈markedBoundedDomain p q M δ}

lemma fullLineDomain_open (p q : Phase n) (M δ : ℝ) : IsOpen (fullLineDomain b p q M δ) :=
  (markedBoundedDomain_open p q M δ).preimage continuous_subtype_val

lemma marked_pair_closedEmbedding : Topology.IsClosedEmbedding
    (fun v : ℝ × markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut) => (v.1,v.2.val)) := by
  exact Topology.IsClosedEmbedding.id.prodMap
    ((markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)).isClosedEmbedding_subtypeL (markedModel_closed _))

variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
  (hJc : HasCompactSupport (fun x => J x-standardJ n))
  (b₁ : ContDiffBump (0:ℂ)) (p q : Phase n)
  (hb₁ : Metric.closedBall (0:ℂ) b.rOut⊆Metric.closedBall (0:ℂ) b₁.rIn)
  {B M δ : ℝ} (hstd : ∀ x,B<‖x‖ →J x=standardJ n) (hδ : 0<δ)
  (he : ∀ w∈markedBoundedDomain p q M δ,MarkedEscapeNeighborhood b p q w B)
  (hbound : ∀ v∈exactMarkedZeroSet J p q,v.2∈markedBoundedDomain p q M δ)

def isolatedFullLineZeros : Set (ℝ × markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) :=
  {v | v.1∈Icc (0:ℝ) 1 ∧ v.2∈fullLineDomain b p q M δ ∧
    fullLineEquation hJs hJ hJc b b₁ p q v=0}

include hb₁ hstd hδ he hbound in
lemma isolatedFullLineZeros_eq_preimage :
    isolatedFullLineZeros b hJs hJ hJc b₁ p q (M := M) (δ := δ)=
      (fun v : ℝ × markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut) => (v.1,v.2.val)) ⁻¹'
        fullMarkedZeroSet J p q := by
  ext v
  constructor
  · intro hv
    have hesc := marked_escape_neighborhood_base b p q (he v.2.val hv.2.1)
    have hline := (fullLineEquation_zero_iff hJs hJ hJc b b₁ p q hb₁ hstd hv.1 v.2 hesc
      (markedBoundedDomain_slope hδ hv.2.1)).mp hv.2.2
    exact ⟨hv.1,fullTime_range v.1,v.2.property.1,hline⟩
  · intro hv
    have hw : v.2∈fullLineDomain b p q M δ := hbound (fullTime v.1,v.2.val) hv.2
    have hesc := marked_escape_neighborhood_base b p q (he v.2.val hw)
    exact ⟨hv.1,hw,(fullLineEquation_zero_iff hJs hJ hJc b b₁ p q hb₁ hstd hv.1 v.2 hesc
      (markedBoundedDomain_slope hδ hw)).mpr hv.2.2.2⟩

include hb₁ hstd hδ he hbound in
lemma isolatedFullLineZeros_compact
    (hc : IsCompact (fullMarkedZeroSet J p q)) :
    IsCompact (isolatedFullLineZeros b hJs hJ hJc b₁ p q (M := M) (δ := δ)) := by
  rw [isolatedFullLineZeros_eq_preimage b hJs hJ hJc b₁ p q hb₁ hstd hδ he hbound]
  exact (marked_pair_closedEmbedding b).isCompact_preimage hc

include hb₁ hstd he in
lemma fullLineEquation_fredholm_on_domain {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (w : markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
    (hw : w∈fullLineDomain b p q M δ) : IsIndexZeroFredholm
      (fderiv ℝ (fun v => fullLineEquation hJs hJ hJc b b₁ p q (t,v)) w) :=
  fullLineEquation_spatial_fredholm hJs hJ hJc b b₁ p q hb₁ hstd ht w (he w.val hw)

end HigherDimensionalBallPacking.Rigidity.HolderCompletion

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter
open HolderCompletion
section

structure ProperIndexZeroPath {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (F : ℝ × X → Y) (U : Set X) : Prop where
  domain_open : IsOpen U
  origin_mem : (0:X)∈U
  smooth : ContDiff ℝ ∞ F
  initial : ∃ L : X ≃L[ℝ] Y,∀ x,F (0,x)=L x
  zeroSet_compact : IsCompact {v : ℝ × X | v.1∈Icc (0:ℝ) 1 ∧ v.2∈U ∧ F v=0}
  fredholm : ∀ t∈Icc (0:ℝ) 1,∀ x∈U,IsIndexZeroFredholm (fderiv ℝ (fun y => F (t,y)) x)

variable {n : ℕ}
local instance lcdEnd1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance lcdEnd2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance lcd1 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance lcd2 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance

lemma markedCurve_zero_correction (p q : Phase n) :
    markedCurve p q (0:COne ℂ (Phase n))=(fun z : ℂ => p+z • (q-p)) := by
  funext z
  have hz (z : ℂ) : cValue (0:COne ℂ (Phase n)) z=0 := rfl
  simp only [markedCurve,markedSlope,hz,sub_zero,add_zero]

lemma exact_marked_initial {J : Phase n → End n} (hJ : ∀ x,Compatible (J x))
    {p q : Phase n} (hpq : p≠q) : (0,0)∈exactMarkedZeroSet J p q := by
  refine ⟨by constructor <;> norm_num,?_,?_⟩
  · change cValue (0:COne ℂ (Phase n)) 0=0
    rfl
  · rw [markedCurve_zero_correction]
    have he : lineHomotopy J 0=(fun _ => standardJ n) := funext (lineHomotopy_zero hJ)
    rw [he]
    exact standard_affine_line p q hpq

variable (b : ContDiffBump (0:ℂ))
local instance lcd3 : NormedAddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance lcd4 : NormedSpace ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance lcd5 : NormedAddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance lcd6 : NormedSpace ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance

local instance lcd7 : AddCommGroup (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (lcd3 (n := n) b).toAddCommGroup
local instance lcd8 : Module ℝ (markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (lcd4 (n := n) b).toModule
local instance lcd9 : AddCommGroup (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (lcd5 (n := n) b).toAddCommGroup
local instance lcd10 : Module ℝ (supportedHolder (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (lcd6 (n := n) b).toModule
local instance lcd11 : NormedAddCommGroup (ℝ × markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance lcd12 : NormedSpace ℝ (ℝ × markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance

variable {J : Phase n → End n} (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
  (hJc : HasCompactSupport (fun x => J x-standardJ n)) (b₁ : ContDiffBump (0:ℂ)) (p q : Phase n)
  (hb₁ : Metric.closedBall (0:ℂ) b.rOut⊆Metric.closedBall (0:ℂ) b₁.rIn)
  {B M δ : ℝ} (hstd : ∀ x,B<‖x‖ →J x=standardJ n) (hδ : 0<δ)
  (he : ∀ w∈markedBoundedDomain p q M δ,MarkedEscapeNeighborhood b p q w B)

include hb₁ hstd hδ he in
lemma fullLineEndpointMap : ∀ w∈fullLineDomain b p q M δ,
    fullLineEquation hJs hJ hJc b b₁ p q (1,w)=0 →
      AffineLineCurve J p q (markedCurve p q w.val) := by
  intro w hw hz
  have hesc := marked_escape_neighborhood_base b p q (he w.val hw)
  have hl := (fullLineEquation_zero_iff hJs hJ hJc b b₁ p q hb₁ hstd (t := 1)
    (by constructor <;> norm_num) w hesc (markedBoundedDomain_slope hδ hw)).mp hz
  have ht : lineHomotopy J (fullTime 1)=J := by
    funext x
    rw [fullTime_one,lineHomotopy_one hJ]
  rwa [ht] at hl

include hb₁ hstd hδ he in
lemma fullLineProperPath
    (hbound : ∀ v∈exactMarkedZeroSet J p q,v.2∈markedBoundedDomain p q M δ)
    (hc : IsCompact (fullMarkedZeroSet J p q)) (hpq : p≠q) :
    ProperIndexZeroPath (fullLineEquation hJs hJ hJc b b₁ p q) (fullLineDomain b p q M δ) := by
  have h0 : (0:markedModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))∈fullLineDomain b p q M δ :=
    hbound (0,0) (exact_marked_initial hJ hpq)
  refine ⟨fullLineDomain_open b p q M δ,h0,
    fullLineEquation_contDiff hJs hJ hJc b b₁ p q,?_,?_,?_⟩
  · exact ⟨markedCREquiv (E := Phase n) (isCompact_closedBall (0:ℂ) b.rOut),
      fullLineEquation_initial hJs hJ hJc b b₁ p q⟩
  · exact isolatedFullLineZeros_compact b hJs hJ hJc b₁ p q hb₁ hstd hδ he hbound hc
  · intro t ht w hw
    exact fullLineEquation_fredholm_on_domain b hJs hJ hJc b₁ p q hb₁ hstd he ht w hw

end
section

variable {n : ℕ} {J : Phase n → End n}
local instance lcdFinal1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance lcdFinal2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance lcdFinal3 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance lcdFinal4 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
variable (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
  (hJc : HasCompactSupport (fun x => J x-standardJ n)) (p q : Phase n)
def FullLineReady (b b₁ : ContDiffBump (0:ℂ)) (M δ : ℝ) : Prop :=
  ProperIndexZeroPath (fullLineEquation hJs hJ hJc b b₁ p q) (fullLineDomain b p q M δ) ∧
    (∀ w∈fullLineDomain b p q M δ,fullLineEquation hJs hJ hJc b b₁ p q (1,w)=0 →
      AffineLineCurve J p q (markedCurve p q w.val))

variable {S T : ℝ} (hST : S<T) (hT : T<1) (hout : ∀ x,S<capacity x →J x=standardJ n)
  (hpq : p≠q)
include hJs hJ hJc hST hT hout hpq in

theorem full_line_continuation_data :
    ∃ (b b₁ : ContDiffBump (0:ℂ)) (M δ : ℝ),
      FullLineReady hJs hJ hJc p q b b₁ M δ := by
  obtain ⟨B,M,δ,b,hB,hM,hδ,hstd,hbound,he⟩ :=
    exact_marked_common_neighborhood (J := J) (p := p) (q := q) hJs hJ hJc hST hT hout hpq
  obtain ⟨b₁,hb₁⟩ := compact_subset_bump_inner (K := Metric.closedBall (0:ℂ) b.rOut)
    (isCompact_closedBall (0:ℂ) b.rOut)
  have hbound' : ∀ v∈exactMarkedZeroSet J p q,v.2∈markedBoundedDomain p q M δ :=
    fun v hv => (hbound v hv).1
  refine ⟨b,b₁,M,δ,?_,?_⟩
  · exact fullLineProperPath b hJs hJ hJc b₁ p q hb₁ hstd hδ he hbound'
      (full_marked_zeroSet_compact hJs hJ hJc hST hT hout hpq) hpq
  · exact fullLineEndpointMap b hJs hJ hJc b₁ p q hb₁ hstd hδ he

end
variable {n : ℕ} {J : Phase n → End n}
local instance alc1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance alc2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace

lemma adapted_structure_capacity_bound
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    (hinside : tsupport (fun x => J x-standardJ n)⊆openBall n 1) :
    ∃ S T : ℝ,S<T ∧ T<1 ∧ ∀ x,S<capacity x →J x=standardJ n := by
  let K := tsupport (fun x => J x-standardJ n) ∪ {(0:Phase n)}
  have hK : IsCompact K := hJc.union (isCompact_singleton)
  have hne : K.Nonempty := ⟨0,Or.inr (by rfl)⟩
  have hKi : K⊆openBall n 1 := by
    intro x hx
    rcases hx with hx|hx
    · exact hinside hx
    · have hx0 : x=0 := hx
      subst x
      simp [openBall,capacity]
  obtain ⟨x,hx,hmax⟩ := hK.exists_isMaxOn hne (capacity_smooth n).continuous.continuousOn
  have hS : capacity x<1 := hKi hx
  refine ⟨capacity x,(capacity x+1)/2,by linarith,by linarith,?_⟩
  intro y hy
  have hn : y∉tsupport (fun z => J z-standardJ n) := by
    intro hh
    exact (not_le_of_gt hy) (hmax (Or.inl hh))
  exact sub_eq_zero.mp (image_eq_zero_of_notMem_tsupport (f := fun z => J z-standardJ n) hn)

lemma adapted_line_continuation_data (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x,Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    (hinside : tsupport (fun x => J x-standardJ n)⊆openBall n 1) (p q : Phase n) (hpq : p≠q) :
    ∃ (b b₁ : ContDiffBump (0:ℂ)) (M δ : ℝ),
      FullLineReady hJs hJ hJc p q b b₁ M δ := by
  obtain ⟨S,T,hST,hT,hout⟩ := adapted_structure_capacity_bound hJc hinside
  exact full_line_continuation_data hJs hJ hJc p q hST hT hout hpq

end HigherDimensionalBallPacking.Rigidity
end

end OAI
