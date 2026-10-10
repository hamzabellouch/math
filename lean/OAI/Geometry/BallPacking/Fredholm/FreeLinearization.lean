import Mathlib
import OAI.Geometry.BallPacking.Compactness.AffineCorrectionInfinity
import OAI.Geometry.BallPacking.Fredholm.PointwiseMarkedCR

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HolderCompletion
variable {n : ℕ}
local instance afInst1 : NormedAddCommGroup (End n) := ContinuousLinearMap.toNormedAddCommGroup
local instance afInst2 : NormedSpace ℝ (End n) := ContinuousLinearMap.toNormedSpace
local instance afInst3 : NormedAddCommGroup (COne ℂ (Phase n)) := inferInstance
local instance afInst4 : NormedSpace ℝ (COne ℂ (Phase n)) := inferInstance
local instance afInst5 : NormedAddCommGroup (HMap ℂ (Phase n)) := inferInstance
local instance afInst6 : NormedSpace ℝ (HMap ℂ (Phase n)) := inferInstance
variable {J : Phase n → End n} (hJ : ContDiff ℝ ∞ J) (hc : ∀ x, Compatible (J x)) {B : ℝ}
  (hstd : ∀ x, B < ‖x‖ → J x=standardJ n) (p q : Phase n) (u : COne ℂ (Phase n))
  {K : Set ℂ} (hK : IsCompact K) (he : ∀ z ∉ K, B < ‖markedCurve p q u z‖)
local instance afInst7 : NormedAddCommGroup (freeModel (E := Phase n) K) := inferInstance
local instance afInst8 : NormedSpace ℝ (freeModel (E := Phase n) K) := inferInstance
local instance afInst9 : AddCommGroup (freeModel (E := Phase n) K) := (afInst7 (n := n) (K := K)).toAddCommGroup
local instance afInst10 : Module ℝ (freeModel (E := Phase n) K) := (afInst8 (n := n) (K := K)).toModule
local instance afInst11 : NormedAddCommGroup (markedModel (E := Phase n) K) := inferInstance
local instance afInst12 : NormedSpace ℝ (markedModel (E := Phase n) K) := inferInstance
local instance afInst13 : AddCommGroup (markedModel (E := Phase n) K) := (afInst11 (n := n) (K := K)).toAddCommGroup
local instance afInst14 : Module ℝ (markedModel (E := Phase n) K) := (afInst12 (n := n) (K := K)).toModule
local instance afInst15 : NormedAddCommGroup (supportedHolder (E := Phase n) K) := inferInstance
local instance afInst16 : NormedSpace ℝ (supportedHolder (E := Phase n) K) := inferInstance
local instance afInst17 : AddCommGroup (supportedHolder (E := Phase n) K) := (afInst15 (n := n) (K := K)).toAddCommGroup
local instance afInst18 : Module ℝ (supportedHolder (E := Phase n) K) := (afInst16 (n := n) (K := K)).toModule

def completedFreePrincipal : freeModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K :=
  freePrincipal (jetValueCLM _ (completedStructureJet hJ hstd p q u))
    (fun z hz => hstd _ (he z hz))

def completedFreeLinearized : freeModel (E := Phase n) K →L[ℝ] supportedHolder (E := Phase n) K :=
  freeLinearized (jetValueCLM _ (completedStructureJet hJ hstd p q u)) (completedQ hJ hstd p q u)
    (fun z hz => hstd _ (he z hz)) (completedQ_zero_outside hJ hstd p q u he)

include hc hK in
lemma completedFreePrincipal_fredholm : (completedFreePrincipal hJ hstd p q u he).IsFredholm := by
  have hP := (completedPrincipal_add_compact_fredholm hJ hc hstd p q u hK he 0 isCompactOperator_zero).1
  have hP' : (completedPrincipal hJ hstd p q u he).IsFredholm := by
    simpa only [add_zero] using hP
  exact freePrincipal_fredholm (E := Phase n) (K := K) (jetValueCLM _ (completedStructureJet hJ hstd p q u))
    (fun z hz => hstd _ (he z hz)) hP'

include hc hK in
lemma completedFreeLinearized_fredholm : (completedFreeLinearized hJ hstd p q u he).IsFredholm := by
  have hP := (completedPrincipal_add_compact_fredholm hJ hc hstd p q u hK he
    (-completedZeroOrder hJ hstd p q u he) (completedZeroOrder_compact hJ hstd p q u hK he).neg).1
  have hP' : (completedPrincipal hJ hstd p q u he-completedZeroOrder hJ hstd p q u he).IsFredholm := by
    simpa only [sub_eq_add_neg] using hP
  exact freeLinearized_fredholm (E := Phase n) (K := K) (jetValueCLM _ (completedStructureJet hJ hstd p q u))
    (completedQ hJ hstd p q u) (fun z hz => hstd _ (he z hz))
    (completedQ_zero_outside hJ hstd p q u he) hP'

lemma completedFreeLinearized_value (v : freeModel (E := Phase n) K) (z : ℂ) :
    valueCLM _ (completedFreeLinearized hJ hstd p q u he v).val z =
      cDeriv v.val z Complex.I-J (markedCurve p q u z) (cDeriv v.val z 1)-
      fderiv ℝ J (markedCurve p q u z) (cValue v.val z) (fderiv ℝ (markedCurve p q u) z 1) := by
  have hp := freePrincipal_value (E := Phase n) (K := K) (jetValueCLM _ (completedStructureJet hJ hstd p q u))
    (fun z hz => hstd _ (he z hz)) v z
  have hq := freeZeroOrder_value (E := Phase n) (K := K) (completedQ hJ hstd p q u)
    (completedQ_zero_outside hJ hstd p q u he) v z
  have hq' := hq.trans (completedQ_value hJ hstd p q u z (cValue v.val z))
  exact congrArg₂ (fun x y : Phase n => x-y) hp hq'

include hJ hstd in
theorem actualStructureBound : BoundedCThree J :=
  boundedCThree_of_compactPerturbation hJ (standardJ n) (compactPerturbation_of_outside_constant _ hstd)

variable (b : ContDiffBump (0:ℂ))
local instance afInst19 : NormedAddCommGroup (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance afInst20 : NormedSpace ℝ (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := inferInstance
local instance afInst21 : AddCommGroup (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (afInst19 (n := n) b).toAddCommGroup
local instance afInst22 : Module ℝ (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (afInst20 (n := n) b).toModule
local instance afInst23 : TopologicalSpace (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) := (afInst19 (n := n) b).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
local instance afInst24 : ContinuousSMul ℝ
    (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)) :=
  IsBoundedSMul.continuousSMul
variable (w : freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut))
  (hesc : ∀ᶠ v in 𝓝 (0 : freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)),
    ∀ z, b.rIn ≤ ‖z‖ → B < ‖affineCurve p (complexSlope (markedSlope p q w.val)) (w.val+v.val) z‖)

def actualFreeChart := freeChart (actualStructureBound hJ hstd) b p (markedSlope p q w.val) w

lemma actualFreeChart_contDiff : ContDiff ℝ ∞ (actualFreeChart hJ hstd p q b w) :=
  freeChart_contDiff (actualStructureBound hJ hstd) b p (markedSlope p q w.val) w
    (compactPerturbation_of_outside_constant _ hstd)

include hesc in
lemma free_escape_base : ∀ z ∉ Metric.closedBall (0:ℂ) b.rOut, B < ‖markedCurve p q w.val z‖ := by
  intro z hz
  have hz' : b.rIn ≤ ‖z‖ := by
    have ht : b.rOut < ‖z‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz
    exact (b.rIn_lt_rOut.trans ht).le
  have hh := hesc.self_of_nhds z hz'
  simpa only [Submodule.coe_zero,add_zero,affineCurve,affine,complexSlope_apply,markedCurve] using hh

include hesc in
lemma actualFreeChart_crSection_fderiv_eval (z : ℂ) :
    (supportedEval (E := Phase n) (K := Metric.closedBall (0:ℂ) b.rOut) z).comp
      (fderiv ℝ (actualFreeChart hJ hstd p q b w) 0) =
    (((BoundedContinuousFunction.evalCLM ℝ z).comp (valueCLM _)).comp
      ((crSectionDeriv (actualStructureBound hJ hstd) p (complexSlope (markedSlope p q w.val)) w.val).comp
        (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)).subtypeL)) := by
  have hd := ((actualFreeChart_contDiff hJ hstd p q b w).differentiable (by simp) 0).hasFDerivAt
  have hdE := (supportedEval (E := Phase n) (K := Metric.closedBall (0:ℂ) b.rOut) z).hasFDerivAt.comp 0 hd
  have hdP := freeChart_hasFDerivAt_eval (actualStructureBound hJ hstd) b p (markedSlope p q w.val) w hstd hesc z
  exact hdE.unique hdP

lemma completedFreeLinearized_crSection (z : ℂ) :
    (((BoundedContinuousFunction.evalCLM ℝ z).comp (valueCLM _)).comp
      ((crSectionDeriv (actualStructureBound hJ hstd) p (complexSlope (markedSlope p q w.val)) w.val).comp
        (freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut)).subtypeL)) =
    (supportedEval (E := Phase n) (K := Metric.closedBall (0:ℂ) b.rOut) z).comp
      (completedFreeLinearized hJ hstd p q w.val (free_escape_base p q b w hesc)) := by
  apply ContinuousLinearMap.ext
  intro v
  have hval := crSectionDeriv_value (actualStructureBound hJ hstd) p (complexSlope (markedSlope p q w.val)) w.val v.val z
  have hh := congrArg (fun d : ℂ →L[ℝ] Phase n =>
    d Complex.I-J (markedCurve p q w.val z) (d 1)-
      fderiv ℝ J (markedCurve p q w.val z) (cValue v.val z) (fderiv ℝ (markedCurve p q w.val) z 1))
    (c_fderiv v.val z)
  exact hval.trans (hh.trans (completedFreeLinearized_value hJ hstd p q w.val (free_escape_base p q b w hesc) v z).symm)

lemma actualFreeChart_fderiv_eval (z : ℂ) :
    (supportedEval (E := Phase n) (K := Metric.closedBall (0:ℂ) b.rOut) z).comp
      (fderiv ℝ (actualFreeChart hJ hstd p q b w) 0) =
    (supportedEval (E := Phase n) (K := Metric.closedBall (0:ℂ) b.rOut) z).comp
      (completedFreeLinearized hJ hstd p q w.val (free_escape_base p q b w hesc)) :=
  (actualFreeChart_crSection_fderiv_eval hJ hstd p q b w hesc z).trans
    (completedFreeLinearized_crSection hJ hstd p q b w hesc z)

lemma actualFreeChart_fderiv_eq : fderiv ℝ (actualFreeChart hJ hstd p q b w) 0 =
    completedFreeLinearized hJ hstd p q w.val (free_escape_base p q b w hesc) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  apply value_ext
  intro z
  exact congrArg (fun L : freeModel (E := Phase n) (Metric.closedBall (0:ℂ) b.rOut) →L[ℝ] Phase n => L v)
    (actualFreeChart_fderiv_eval hJ hstd p q b w hesc z)

include hc hesc in
lemma actualFreeChart_fderiv_fredholm : (fderiv ℝ (actualFreeChart hJ hstd p q b w) 0).IsFredholm := by
  rw [actualFreeChart_fderiv_eq hJ hstd p q b w hesc]
  exact completedFreeLinearized_fredholm hJ hc hstd p q w.val (isCompact_closedBall (0:ℂ) b.rOut)
    (free_escape_base p q b w hesc)

end HolderCompletion

end
section
open scoped Topology BoundedContinuousFunction ContDiff
open Set Function Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 theorem compact_test_translation_smooth {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) {v : ℂ → E} (hv : LocallyIntegrable v) :
    ContDiff ℝ ∞ (fun t : ℂ => ∫ z : ℂ, g z • v (z+t)) := by
  let L : ℝ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℝ
  have hs : ContDiff ℝ ∞ (fun z : ℂ => g (-z)) := hg.comp contDiff_neg
  have hc : HasCompactSupport (fun z : ℂ => g (-z)) := hgc.comp_homeomorph (Homeomorph.neg ℂ)
  have hh := hc.contDiff_convolution_left (𝕜 := ℝ) (μ := (volume : Measure ℂ)) L hs hv
  convert hh using 1
  funext t
  rw [convolution_def,←integral_neg_eq_self]
  congr 1
  funext z
  change g (-z) • v (-z+t)=g (-z) • v (t-z)
  rw [neg_add_eq_sub]


end
section
open Set Function
variable {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

 theorem finite_separating_family (L : I → E →L[ℝ] F)
    (hL : ∀ v : E, (∀ i, L i v=0) → v=0) :
    ∃ s : Finset I, ∀ v : E, (∀ i ∈ s, L i v=0) → v=0 := by
  classical
  let U : I → Set E := fun i => {v | L i v≠0}
  have hU : ∀ i, IsOpen (U i) := fun i =>
    (isClosed_singleton.preimage (L i).continuous).isOpen_compl
  have hcov : Metric.sphere (0:E) 1 ⊆ ⋃ i, U i := by
    intro v hv
    by_contra hn
    have hz : ∀ i, L i v=0 := by
      intro i
      by_contra hi
      exact hn (mem_iUnion.mpr ⟨i,hi⟩)
    have hv0 := hL v hz
    simp [hv0] at hv
  obtain ⟨s,hs⟩ := (isCompact_sphere (0:E) 1).elim_finite_subcover U hU hcov
  refine ⟨s,fun v hv => ?_⟩
  by_contra hne
  have hn : ‖v‖≠0 := norm_ne_zero_iff.mpr hne
  have hw : ‖v‖⁻¹ • v ∈ Metric.sphere (0:E) 1 := by
    rw [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),inv_mul_cancel₀ hn]
  obtain ⟨i,hi⟩ := mem_iUnion.mp (hs hw)
  obtain ⟨his,hh⟩ := mem_iUnion.mp hi
  have hzi : L i (‖v‖⁻¹ • v)=0 := by rw [map_smul,hv i his,smul_zero]
  exact hh hzi


end
section
open Set Function
variable {E F D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]

 theorem fredholm_stabilized_leftInverse (P : E →L[ℝ] F) (hP : P.IsFredholm)
    (Q : E →L[ℝ] D) (hQ : Injective (Q.comp P.ker.subtypeL)) :
    (P.prod Q).HasLeftInverse := by
  obtain ⟨pkg⟩ := hP.nonempty_fredholmPackage
  let S : F →L[ℝ] E := pkg.quasiInverse
  have hPSP (v : E) : P (S (P v))=P v := by
    rw [pkg.eq_equiv]
    simp [S,ContinuousLinearMap.FredholmPackage.quasiInverse,Submodule.projectionOnto_projection]
  let QK : P.ker →L[ℝ] D := Q.comp P.ker.subtypeL
  obtain ⟨U,hU⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hQ
  let T : F × D →L[ℝ] E := S.comp (ContinuousLinearMap.fst ℝ F D)
  let L : F × D →L[ℝ] E := T + P.ker.subtypeL.comp
    (U.comp (ContinuousLinearMap.snd ℝ F D-Q.comp T))
  refine ⟨L,fun v => ?_⟩
  have hr : v-S (P v)∈P.ker := by
    change P (v-S (P v))=0
    rw [map_sub,hPSP,sub_self]
  have hu := congrArg (fun z : P.ker => (z:E)) (hU ⟨v-S (P v),hr⟩)
  change (U (Q (v-S (P v))) : E)=v-S (P v) at hu
  change S (P v)+(U (Q v-Q (S (P v))) : E)=v
  rw [←map_sub,hu]
  abel


end
section
open scoped Topology BoundedContinuousFunction ContDiff
open Set Function Filter MeasureTheory
namespace HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

abbrev PlaneTest := {g : ℂ → ℝ // ContDiff ℝ ∞ g ∧ HasCompactSupport g}

omit [CompleteSpace E] in
lemma planeTest_integrable [CompleteSpace E] (g : PlaneTest) (v : ℂ →ᵇ E) :
    Integrable (fun z => g.val z • v z) :=
  v.continuous.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
    g.property.1.continuous g.property.2

lemma planeTest_norm_bound (g : PlaneTest) (v : ℂ →ᵇ E) :
    ‖∫ z, g.val z • v z‖ ≤ (∫ z, ‖g.val z‖)*‖v‖ := by
  have hi : Integrable g.val := g.property.1.continuous.integrable_of_hasCompactSupport g.property.2
  calc
    _ ≤ ∫ z, ‖g.val z • v z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, ‖g.val z‖*‖v‖ := by
      apply integral_mono (planeTest_integrable g v).norm (hi.norm.mul_const _)
      intro z
      change ‖g.val z • v z‖ ≤ ‖g.val z‖*‖v‖
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (BoundedContinuousFunction.norm_coe_le_norm v z) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

def planeTestCLM (g : PlaneTest) : (ℂ →ᵇ E) →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun v => ∫ z, g.val z • v z
      map_add' := fun u v => by
        simp only [BoundedContinuousFunction.add_apply,smul_add]
        exact integral_add (planeTest_integrable g u) (planeTest_integrable g v)
      map_smul' := fun c v => by
        simp only [BoundedContinuousFunction.smul_apply]
        simp_rw [smul_comm (g.val _) c]
        exact integral_smul c _ }
    (∫ z, ‖g.val z‖) (planeTest_norm_bound g)

lemma planeTest_separates (v : ℂ →ᵇ E) (hv : ∀ g : PlaneTest, planeTestCLM g v=0) : v=0 := by
  have hz := isOpen_univ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := (volume : Measure ℂ))
    (v.continuous.locallyIntegrable.locallyIntegrableOn univ)
    (fun g hg hgc _ => hv ⟨g,hg,hgc⟩)
  have he : EqOn v (fun _ => 0) univ :=
    Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' MeasurableSet.univ).mpr hz)
      isOpen_univ v.continuous.continuousOn continuousOn_const
  ext z
  exact he (mem_univ z)

local instance testInst1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance testInst2 : NormedSpace ℝ (COne ℂ E) := inferInstance

def jetTestCLM (g : PlaneTest) : COne ℂ E →L[ℝ] E :=
  (planeTestCLM g).comp ((valueCLM _).comp (jetValueCLM _))

@[simp] lemma jetTest_value (g : PlaneTest) (u : COne ℂ E) :
    jetTestCLM g u = ∫ z, g.val z • cValue u z := rfl

lemma jetTest_separates (u : COne ℂ E) (hu : ∀ g : PlaneTest, jetTestCLM g u=0) : u=0 := by
  have hv : cValue u = 0 := planeTest_separates _ hu
  apply cValue_ext
  intro z
  exact congrArg (fun v : ℂ →ᵇ E => v z) hv

lemma jetTest_translation_smooth (g : PlaneTest) (u : COne ℂ E) :
    ContDiff ℝ ∞ (fun t => jetTestCLM g (jetTranslate t u)) := by
  simp only [jetTest_value,jetTranslate_value]
  exact compact_test_translation_smooth g.property.1 g.property.2 (cValue u).continuous.locallyIntegrable

lemma jetTest_translation_difference_smooth (g : PlaneTest) (u : COne ℂ E) :
    ContDiff ℝ ∞ (fun t => jetTestCLM g (jetTranslate t u-u)) := by
  simp_rw [map_sub]
  exact (jetTest_translation_smooth g u).sub contDiff_const

lemma finite_jet_tests {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (L : V →L[ℝ] COne ℂ E) (hL : Injective L) :
    ∃ s : Finset PlaneTest, ∀ v : V, (∀ g ∈ s, jetTestCLM g (L v)=0) → v=0 := by
  apply finite_separating_family (fun g : PlaneTest => (jetTestCLM g).comp L)
  intro v hv
  apply hL
  rw [map_zero]
  exact jetTest_separates _ hv

end HolderCompletion

end
section
open scoped Topology BoundedContinuousFunction ContDiff
open Set Function Filter
namespace HolderCompletion
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
section Generic
variable {X I : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
omit [CompleteSpace E] in
lemma observed_fredholm_leftInverse [CompleteSpace E] (P : X →L[ℝ] F) (hP : P.IsFredholm)
    (O : I → X →L[ℝ] E) (hO : ∀ x, (∀ i, O i x=0) → x=0) :
    ∃ (s : Finset I) (L : F × (s → E) →L[ℝ] X),
      LeftInverse L (P.prod (ContinuousLinearMap.pi (fun i : s => O i.val))) := by
  let := hP.finite_ker
  obtain ⟨s,hs⟩ := finite_separating_family (fun i => (O i).comp P.ker.subtypeL)
    (by
      intro v hv
      apply Subtype.ext
      exact hO v.val hv)
  let Q : X →L[ℝ] (s → E) := ContinuousLinearMap.pi (fun i : s => O i.val)
  have hQ : Injective (Q.comp P.ker.subtypeL) := by
    intro u v huv
    apply sub_eq_zero.mp
    apply hs (u-v)
    intro i hi
    have hh := congrArg (fun f : s → E => f ⟨i,hi⟩) huv
    change O i u.val=O i v.val at hh
    change O i (u.val-v.val)=0
    rw [map_sub,hh,sub_self]
  obtain ⟨L,hL⟩ := fredholm_stabilized_leftInverse P hP Q hQ
  exact ⟨s,L,hL⟩
end Generic

local instance jetObsInst1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance jetObsInst2 : NormedSpace ℝ (COne ℂ E) := inferInstance

def jetObservations (s : Finset PlaneTest) : COne ℂ E →L[ℝ] (s → E) :=
  ContinuousLinearMap.pi (fun g => jetTestCLM g.val)

omit [FiniteDimensional ℝ E] in
lemma jetObservations_translation_smooth [FiniteDimensional ℝ E] (s : Finset PlaneTest) (u : COne ℂ E) :
    ContDiff ℝ ∞ (fun t => jetObservations s (jetTranslate t u-u)) :=
  contDiff_pi.mpr (fun g => jetTest_translation_difference_smooth g.val u)

variable (S : Submodule ℝ (COne ℂ E))
local instance jetObsInst3 : NormedAddCommGroup S := inferInstance
local instance jetObsInst4 : NormedSpace ℝ S := inferInstance
local instance jetObsInst5 : AddCommGroup S := (jetObsInst3 S).toAddCommGroup
local instance jetObsInst6 : Module ℝ S := (jetObsInst4 S).toModule

def subspaceObservations (s : Finset PlaneTest) : S →L[ℝ] (s → E) :=
  (jetObservations s).comp S.subtypeL

lemma exists_jet_fredholm_observations (P : S →L[ℝ] F) (hP : P.IsFredholm) :
    ∃ (s : Finset PlaneTest) (L : F × (s → E) →L[ℝ] S),
      LeftInverse L (P.prod (subspaceObservations S s)) := by
  let O : PlaneTest → S →L[ℝ] E := fun g => (jetTestCLM g).comp S.subtypeL
  have hO : ∀ u : S, (∀ g, O g u=0) → u=0 := by
    intro u hu
    apply Subtype.ext
    exact jetTest_separates u.val hu
  have hh := observed_fredholm_leftInverse P hP O hO
  obtain ⟨s,L,hL⟩ := hh
  exact ⟨s,L,hL⟩

end HolderCompletion

end
section
open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HolderCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance freeTransInst1 : NormedAddCommGroup (COne ℂ E) := inferInstance
local instance freeTransInst2 : NormedSpace ℝ (COne ℂ E) := inferInstance
local instance freeTransInst3 : NormedAddCommGroup (HMap ℂ E) := inferInstance
local instance freeTransInst4 : NormedSpace ℝ (HMap ℂ E) := inferInstance

def translationVariation (a : E) (u : COne ℂ E) (t : ℂ) : COne ℂ E :=
  constJet (t • a)+jetTranslate t u-u

omit [CompleteSpace E] in
@[simp] lemma translationVariation_value [CompleteSpace E] (a : E) (u : COne ℂ E) (t z : ℂ) :
    cValue (translationVariation a u t) z = t • a+cValue u (z+t)-cValue u z := rfl

omit [CompleteSpace E] in
@[simp] lemma translationVariation_deriv [CompleteSpace E] (a : E) (u : COne ℂ E) (t z : ℂ) :
    cDeriv (translationVariation a u t) z = cDeriv u (z+t)-cDeriv u z := by
  change (0 + cDeriv u (z+t))-cDeriv u z = _
  rw [zero_add]

omit [CompleteSpace E] in
lemma translationVariation_zero [CompleteSpace E] (a : E) (u : COne ℂ E) : translationVariation a u 0=0 := by
  apply cValue_ext
  intro z
  simp only [translationVariation_value,zero_smul,zero_add,add_zero,sub_self]
  rfl

lemma translationVariation_CR (a : E) (u : COne ℂ E) (t z : ℂ) :
    valueCLM _ (standardJetCR (translationVariation a u t)) z =
      valueCLM _ (standardJetCR u) (z+t)-valueCLM _ (standardJetCR u) z := by
  simp only [standardJetCR_value,translationVariation_deriv,sub_apply,smul_sub]
  abel

lemma translationVariation_mem {R S : ℝ} (hRS : R+1 ≤ S)
    (a : E) (u : freeModel (E := E) (Metric.closedBall (0:ℂ) R))
    {t : ℂ} (ht : ‖t‖≤1) : translationVariation a u.val t∈freeModel (E := E) (Metric.closedBall (0:ℂ) S) := by
  apply (mem_supportedHolder _ _).mpr
  intro z hz
  have hzS : S < ‖z‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz
  have hzR : z∉Metric.closedBall (0:ℂ) R := by
    simp only [Metric.mem_closedBall,dist_zero_right,not_le]
    linarith
  have hztR : z+t∉Metric.closedBall (0:ℂ) R := by
    simp only [Metric.mem_closedBall,dist_zero_right,not_le]
    have hnorm : ‖z‖ ≤ ‖z+t‖+‖t‖ := by
      simpa only [add_sub_cancel_right] using norm_sub_le (z+t) t
    linarith
  change valueCLM _ (standardJetCR (translationVariation a u.val t)) z = 0
  have h0 : valueCLM _ (standardJetCR u.val) z=0 := (mem_supportedHolder _ _).mp u.property z hzR
  have h1 : valueCLM _ (standardJetCR u.val) (z+t)=0 := (mem_supportedHolder _ _).mp u.property (z+t) hztR
  rw [translationVariation_CR,h1,h0,sub_self]

variable {R S : ℝ} (hRS : R+1 ≤ S) (a : E)
  (u : freeModel (E := E) (Metric.closedBall (0:ℂ) R))
local instance freeTransInst5 : NormedAddCommGroup (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) := inferInstance
local instance freeTransInst6 : NormedSpace ℝ (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) := inferInstance

def freeTranslation (t : ℂ) : freeModel (E := E) (Metric.closedBall (0:ℂ) S) :=
  if ht : ‖t‖≤1 then ⟨translationVariation a u.val t,translationVariation_mem hRS a u ht⟩ else 0

lemma freeTranslation_near : ∀ᶠ t in 𝓝 (0:ℂ), (freeTranslation hRS a u t).val=translationVariation a u.val t := by
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) (show (0:ℝ)<1 by norm_num)] with t ht
  have ht' : ‖t‖≤1 := (show ‖t‖<1 by simpa only [Metric.mem_ball,dist_zero_right] using ht).le
  simp only [freeTranslation,dite_eq_left ht']

@[simp] lemma freeTranslation_zero : freeTranslation hRS a u 0=0 := by
  apply Subtype.ext
  exact freeTranslation_near hRS a u |>.self_of_nhds |>.trans (translationVariation_zero a u.val)

variable [FiniteDimensional ℝ E]

lemma translationVariation_observation_smooth (s : Finset PlaneTest) :
    ContDiff ℝ ∞ (fun t => jetObservations s (translationVariation a u.val t)) := by
  have he : (fun t => jetObservations s (translationVariation a u.val t)) =
      (fun t => jetObservations s (constJetCLM (complexSlope a t))+
        jetObservations s (jetTranslate t u.val-u.val)) := by
    funext t
    rw [←map_add]
    apply congrArg (jetObservations s)
    change constJet (t • a)+jetTranslate t u.val-u.val = constJet (t • a)+(jetTranslate t u.val-u.val)
    abel
  rw [he]
  exact ((jetObservations s).contDiff.comp ((constJetCLM (E := E)).contDiff.comp
    (complexSlope a).contDiff)).add (jetObservations_translation_smooth s u.val)

lemma freeTranslation_observation_smoothAt (s : Finset PlaneTest) :
    ContDiffAt ℝ ∞ (fun t => subspaceObservations (freeModel (E := E) (Metric.closedBall (0:ℂ) S)) s
      (freeTranslation hRS a u t)) 0 := by
  apply (translationVariation_observation_smooth a u s).contDiffAt.congr_of_eventuallyEq
  filter_upwards [freeTranslation_near hRS a u] with t ht
  exact congrArg (jetObservations s) ht

end HolderCompletion

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
