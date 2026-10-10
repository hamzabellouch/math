import Mathlib
import OAI.Geometry.BallPacking.Annuli.SurfaceSuspensionCoefficients

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def annularCoverDomain
    (D : AnnularHandleData E M) : Set Plane :=
  cylinderCover ⁻¹' D.chart.source

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem annularCoverDomain_open
    (D : AnnularHandleData E M) :
    IsOpen (D.annularCoverDomain) :=
  D.chart.open_source.preimage cylinderCover_smooth.continuous

theorem annularCover_pullback_smoothAt
    (D : AnnularHandleData E M)
    {γ : ManifoldOneForm E M} {q : Plane} (hq : q∈D.annularCoverDomain)
    (hγ : ContDiffAt ℝ ∞ (chartOneForm γ (D.handleAnnularCover q))
      (extChartAt 𝓘(ℝ,E) (D.handleAnnularCover q) (D.handleAnnularCover q))) :
    ContDiffAt ℝ ∞ (fun y => euclideanPullbackOneForm (fun _ => γ) (D.handleAnnularCover) (0,y)) q := by
  have hf := hγ.comp ((0:ℝ),extChartAt 𝓘(ℝ,E) (D.handleAnnularCover q)
    (D.handleAnnularCover q)) contDiffAt_snd
  have hs := parameterEuclideanPullbackOneForm_contDiffAt (α := fun _ : ℝ => γ)
    (p := (0,q)) hf (D.handleAnnularCover_smoothAt hq)
  exact hs.comp q (contDiffAt_const.prodMk contDiffAt_id)

theorem annularCover_coefficients_smooth
    (D : AnnularHandleData E M)
    {γ : ManifoldOneForm E M}
    (hγ : ∀ x∈D.chart.target,ContDiffAt ℝ ∞
      (chartOneForm γ x) (extChartAt 𝓘(ℝ,E) x x)) :
    ContDiffOn ℝ ∞ (D.annularCoverA γ) (D.annularCoverDomain) ∧
    ContDiffOn ℝ ∞ (D.annularCoverB γ) (D.annularCoverDomain) := by
  constructor <;> intro q hq
  · exact ((D.annularCover_pullback_smoothAt hq
      (hγ _ (D.chart.map_source hq))).clm_apply contDiffAt_const).contDiffWithinAt
  · exact ((D.annularCover_pullback_smoothAt hq
      (hγ _ (D.chart.map_source hq))).clm_apply contDiffAt_const).contDiffWithinAt

theorem annularCover_curl
    (D : AnnularHandleData E M)
    {γ : ManifoldOneForm E M} {q : Plane} (hq : q∈D.annularCoverDomain)
    (hγ : ContDiffAt ℝ ∞ (chartOneForm γ (D.handleAnnularCover q))
      (extChartAt 𝓘(ℝ,E) (D.handleAnnularCover q) (D.handleAnnularCover q))) :
    fderiv ℝ (D.annularCoverB γ) q (1,0)-fderiv ℝ (D.annularCoverA γ) q (0,1)=
      manifoldExteriorOneForm γ (D.handleAnnularCover q)
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) q (1,0))
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) q (0,1)) := by
  have hs := D.annularCover_pullback_smoothAt hq hγ
  have he : (fun y => euclideanPullbackOneForm (fun _ => γ) (D.handleAnnularCover) (0,y))=
      (fun y => planarCovector (D.annularCoverA γ y) (D.annularCoverB γ y)) := by
    funext y
    apply ContinuousLinearMap.ext
    intro v
    exact D.annularCover_form_rep γ y v
  have hd := euclidean_manifold_pullback_exterior_at (D.handleAnnularCover_smoothAt hq) hγ
  have hA : ContDiffAt ℝ ∞ (D.annularCoverA γ) q := hs.clm_apply contDiffAt_const
  have hB : ContDiffAt ℝ ∞ (D.annularCoverB γ) q := hs.clm_apply contDiffAt_const
  rw [he,planarCovector_exterior_at hA hB] at hd
  have hv := congrArg (fun Ω : Plane →L[ℝ] Plane →L[ℝ] ℝ => Ω (1,0) (0,1)) hd
  simp only [smul_apply,smul_eq_mul,planarArea_apply,mul_one,mul_zero,sub_zero,
    manifoldMapDifferential] at hv
  exact hv

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
section

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

 def handleAnnularCover
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) : Plane → M := (handleAnnularChart e a) ∘ cylinderCover

 theorem handleAnnularCover_smoothAt
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) {q : Plane} (hq : cylinderCover q∈(handleAnnularChart e a).source) :
    ContMDiffAt 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ (handleAnnularCover e a) q :=
  ((handleAnnularChart e a).contMDiffOn.contMDiffAt
    ((handleAnnularChart e a).open_source.mem_nhds hq)).comp q cylinderCover_smooth.contMDiffAt

 theorem handleAnnularCover_derivative
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) {q : Plane} (hq : cylinderCover q∈(handleAnnularChart e a).source) :
    mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (handleAnnularCover e a) q=
      (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) (handleAnnularChart e a) (cylinderCover q)).comp
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q) :=
  mfderiv_comp q ((handleAnnularChart e a).mdifferentiableAt (by simp) hq)
    (cylinderCover_smooth.mdifferentiableAt (by simp))

 theorem globalHandleForm_cover
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) (f : Circle → ℝ) {q : Plane}
    (hq : cylinderCover q∈(handleAnnularChart e a).source) (v : Plane) :
    globalHandleForm e f (handleAnnularCover e a q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (handleAnnularCover e a) q v)=f (circleTurn q.2)*v.2 := by
  rw [handleAnnularCover_derivative e a hq]
  change globalHandleForm e f (handleAnnularChart e a (cylinderCover q))
    (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) (handleAnnularChart e a) (cylinderCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q v))=_
  erw [handleAnnularChart_pullback e a f hq,cylinderCover_derivative]
  exact congrArg (f (circleTurn q.2)*·) (circleAngular_unit_pullback q.2 v.2)

 theorem globalHandleRadialForm_annular
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a b : ℝ) {z : HandleCylinder} (hz : z∈(handleAnnularChart e a).source)
    (v : CylinderModel) :
    globalHandleRadialForm e b (handleAnnularChart e a z)
      (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) (handleAnnularChart e a) z v)=
      deriv (intervalClock (-b) b) z.1*v.1 := by
  change globalHandleRadialForm e b (e (torusAnnulusMap z))
    (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) (e ∘ torusAnnulusMap) z v)=_
  rw [mfderiv_comp z (f := torusAnnulusMap) (g := (e : HandleTorus → M))
    (e.mdifferentiableAt (by simp) hz.1.2)
    (torusAnnulusMap_smooth.mdifferentiableAt (by simp))]
  have he := congrArg (fun L : TorusModel →L[ℝ] ℝ =>
    L (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,TorusModel) torusAnnulusMap z v))
    (handlePushforwardOneForm_pullback e (torusFirstForm (circleClockDensity b)) hz.1.2)
  change globalHandleRadialForm e b (e (torusAnnulusMap z)) _= _ at he
  apply he.trans
  change torusFirstForm (circleClockDensity b) (torusAnnulusMap z)
    (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,TorusModel) torusAnnulusMap z v)=_
  rw [torusAnnulusMap_derivative]
  erw [torusFirstForm_apply]
  change weightedCircleAngular (circleClockDensity b) (circleTurn z.1)
    (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,CircleModel) circleTurn z.1 v.1) = _
  erw [weightedCircleAngular_pullback, circleClockDensity_turn hz.1.1.1]

 theorem globalHandleRadialForm_cover
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a b : ℝ) {q : Plane} (hq : cylinderCover q∈(handleAnnularChart e a).source)
    (v : Plane) :
    globalHandleRadialForm e b (handleAnnularCover e a q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (handleAnnularCover e a) q v)=
      deriv (intervalClock (-b) b) q.1*v.1 := by
  rw [handleAnnularCover_derivative e a hq]
  change globalHandleRadialForm e b (handleAnnularChart e a (cylinderCover q))
    (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) (handleAnnularChart e a) (cylinderCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q v))=_
  erw [globalHandleRadialForm_annular e a b hq,cylinderCover_derivative]
  rfl

 theorem handleAnnularCover_inverse
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) {q : Plane} (hq : cylinderCover q∈(handleAnnularChart e a).source) :
    (handleAnnularChart e a).symm (handleAnnularCover e a q)=cylinderCover q :=
  (handleAnnularChart e a).left_inv hq

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem cylinderCover_derivative_bijective (q : Plane) :
    Bijective (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q) := by
  constructor
  · intro v w h
    change (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q : Plane →L[ℝ] CylinderModel) v =
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) cylinderCover q : Plane →L[ℝ] CylinderModel) w at h
    erw [cylinderCover_derivative,cylinderCover_derivative] at h
    have hx := congrArg (fun z : CylinderModel => z.1) h
    refine Prod.ext hx ?_
    have he := congrArg (fun z : CylinderModel => circleAngular (circleTurn q.2) z.2) h
    simpa only [circleAngular_unit_pullback] using he
  · intro v
    exact ⟨(v.1,circleAngular (circleTurn q.2) v.2),cylinderCover_derivative_right_inverse q v⟩

theorem handleAnnularCover_derivative_bijective
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) {q : Plane} (hq : cylinderCover q∈(handleAnnularChart e a).source) :
    Bijective (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (handleAnnularCover e a) q) := by
  let c := handleAnnularChart e a
  let A : CylinderModel →L[ℝ] E := mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) c (cylinderCover q)
  let B : E →L[ℝ] CylinderModel := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) c.symm (c (cylinderCover q))
  have hBA : B.comp A=ContinuousLinearMap.id ℝ CylinderModel := handle_mfderiv_symm_comp c hq
  have hAB : A.comp B=ContinuousLinearMap.id ℝ E := by
    have h := handle_mfderiv_symm_comp c.symm (c.map_source hq)
    change (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) c (c.symm (c (cylinderCover q)))).comp B=
      ContinuousLinearMap.id ℝ E at h
    erw [c.left_inv hq] at h
    exact h
  have hA : Bijective A := by
    constructor
    · intro v w h
      have he := congrArg B h
      have hv := congrArg (fun L : CylinderModel →L[ℝ] CylinderModel => L v) hBA
      have hw := congrArg (fun L : CylinderModel →L[ℝ] CylinderModel => L w) hBA
      exact hv.symm.trans (he.trans hw)
    · intro v
      exact ⟨B v,congrArg (fun L : E →L[ℝ] E => L v) hAB⟩
  rw [handleAnnularCover_derivative e a hq]
  exact hA.comp (cylinderCover_derivative_bijective q)

def handleAnnularCoverLinearEquiv
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) {q : Plane} (hq : cylinderCover q∈(handleAnnularChart e a).source) : Plane ≃L[ℝ] E :=
  (LinearEquiv.ofBijective
    (show Plane →L[ℝ] E from mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (handleAnnularCover e a) q).toLinearMap
    (handleAnnularCover_derivative_bijective e a hq)).toContinuousLinearEquiv

@[simp] theorem handleAnnularCoverLinearEquiv_apply
    (e : PartialDiffeomorph 𝓘(ℝ,TorusModel) 𝓘(ℝ,E) HandleTorus M ∞)
    (a : ℝ) {q : Plane} (hq : cylinderCover q∈(handleAnnularChart e a).source) (v : Plane) :
    handleAnnularCoverLinearEquiv e a hq v=
      mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (handleAnnularCover e a) q v := rfl

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem handleAnnularCover_derivative_bijective
    (D : AnnularHandleData E M)
    {q : Plane} (hq : cylinderCover q∈D.chart.source) :
    Bijective (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) q) := by
  let c := D.chart
  let A : CylinderModel →L[ℝ] E := mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) c (cylinderCover q)
  let B : E →L[ℝ] CylinderModel := mfderiv 𝓘(ℝ,E) 𝓘(ℝ,CylinderModel) c.symm (c (cylinderCover q))
  have hBA : B.comp A=ContinuousLinearMap.id ℝ CylinderModel := handle_mfderiv_symm_comp c hq
  have hAB : A.comp B=ContinuousLinearMap.id ℝ E := by
    have h := handle_mfderiv_symm_comp c.symm (c.map_source hq)
    change (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,E) c (c.symm (c (cylinderCover q)))).comp B=
      ContinuousLinearMap.id ℝ E at h
    erw [c.left_inv hq] at h
    exact h
  have hA : Bijective A := by
    constructor
    · intro v w h
      have he := congrArg B h
      have hv := congrArg (fun L : CylinderModel →L[ℝ] CylinderModel => L v) hBA
      have hw := congrArg (fun L : CylinderModel →L[ℝ] CylinderModel => L w) hBA
      exact hv.symm.trans (he.trans hw)
    · intro v
      exact ⟨B v,congrArg (fun L : E →L[ℝ] E => L v) hAB⟩
  rw [D.handleAnnularCover_derivative hq]
  exact hA.comp (cylinderCover_derivative_bijective q)

def handleAnnularCoverLinearEquiv
    (D : AnnularHandleData E M)
    {q : Plane} (hq : cylinderCover q∈D.chart.source) : Plane ≃L[ℝ] E :=
  (LinearEquiv.ofBijective
    (show Plane →L[ℝ] E from mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) q).toLinearMap
    (D.handleAnnularCover_derivative_bijective hq)).toContinuousLinearEquiv

@[simp] theorem handleAnnularCoverLinearEquiv_apply
    (D : AnnularHandleData E M)
    {q : Plane} (hq : cylinderCover q∈D.chart.source) (v : Plane) :
    D.handleAnnularCoverLinearEquiv hq v=
      mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) (D.handleAnnularCover) q v := rfl

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def parameterEuclideanPullbackTwoForm (α : P → ManifoldTwoForm E M) (g : F → M)
    (p : P × F) : F →L[ℝ] F →L[ℝ] ℝ :=
  (α p.1 (g p.2)).bilinearComp (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)
    (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)

theorem parameterEuclideanPullbackTwoForm_contDiffAt
    {α : P → ManifoldTwoForm E M} {g : F → M} {p : P × F}
    (hα : ContDiffAt ℝ ∞
      (fun q : P × E => chartTwoForm (α q.1) (g p.2) q.2)
      (p.1,extChartAt 𝓘(ℝ,E) (g p.2) (g p.2)))
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g p.2) :
    ContDiffAt ℝ ∞ (parameterEuclideanPullbackTwoForm α g) p := by
  let c := g p.2
  have hc : g p.2 ∈ (extChartAt 𝓘(ℝ,E) c).source := mem_extChartAt_source c
  have hch := (contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞)
    (x := c) (by simpa only [extChartAt_source] using hc)).comp p.2 hg
  have hs : ContDiffAt ℝ ∞ (extChartAt 𝓘(ℝ,E) c ∘ g) p.2 := hch.contDiffAt
  have hcoord : ContDiffAt ℝ ∞ (fun q : P × F => (q.1,extChartAt 𝓘(ℝ,E) c (g q.2))) p :=
    contDiffAt_fst.prodMk (hs.comp p contDiffAt_snd)
  have hform := hα.comp p hcoord
  have hder := (hs.fderiv_right (m := ∞) (by simp)).comp p contDiffAt_snd
  have hsm := smooth_bilinear_flip ((smooth_bilinear_flip (hform.clm_comp hder)).clm_comp hder)
  apply hsm.congr_of_eventuallyEq
  have hg' := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hg.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
  have hc' := hg.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)
  filter_upwards [continuousAt_snd.preimage_mem_nhds hg',
    continuousAt_snd.preimage_mem_nhds hc'] with q hq hqc
  exact euclideanPullbackTwoForm_chart (Ω := fun _ => α q.1) (p := (0,q.2))
    (hq.mdifferentiableAt (by simp)) hqc

variable {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem chartTwoForm_manifoldPullback_at {α : ℝ → ManifoldTwoForm E M} {e : N → M}
    {b : N} {p : ℝ × F}
    (hp : p.2 ∈ (extChartAt 𝓘(ℝ,F) b).target)
    (he : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) e ((extChartAt 𝓘(ℝ,F) b).symm p.2)) :
    chartTwoForm (manifoldPullbackTwoForm α e p.1) b p.2 =
      euclideanPullbackTwoForm α (e ∘ (extChartAt 𝓘(ℝ,F) b).symm) p := by
  have hc := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp)).mdifferentiableAt (by simp)
  have hd := (he.hasMFDerivAt.comp p.2 hc.hasMFDerivAt).mfderiv
  simp only [euclideanPullbackTwoForm,hd,chartTwoForm,manifoldPullbackTwoForm,
    manifoldMapDifferential,chartDifferential_inverse hp,Function.comp_apply]
  ext v w
  rfl

def parameterManifoldPullbackTwoForm (α : P → ManifoldTwoForm E M) (g : N → M)
    (p : P) : ManifoldTwoForm F N :=
  manifoldPullbackTwoForm (fun _ => α p) g 0

omit [NormedSpace ℝ P] in

theorem parameterManifoldPullbackTwoForm_chart_germ
    (α : P → ManifoldTwoForm E M) {g : N → M} (p : P) {b : N}
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g b) :
    (fun q : P × F => chartTwoForm (parameterManifoldPullbackTwoForm α g q.1) b q.2)
      =ᶠ[𝓝 (p,extChartAt 𝓘(ℝ,F) b b)]
    parameterEuclideanPullbackTwoForm α (g ∘ (extChartAt 𝓘(ℝ,F) b).symm) := by
  have hb := mem_extChartAt_source (I := 𝓘(ℝ,F)) b
  have hy := (extChartAt 𝓘(ℝ,F) b).map_source hb
  have he := (extChartAt 𝓘(ℝ,F) b).left_inv hb
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy)
  have hn := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
    (hg.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
  have hn₁ : {x | ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) 1 g x} ∈
      𝓝 ((extChartAt 𝓘(ℝ,F) b).symm (extChartAt 𝓘(ℝ,F) b b)) := by
    rw [he]; exact hn
  have hn' := (hi.continuousAt.comp (f := Prod.snd) (continuousAt_snd (p := (p,extChartAt 𝓘(ℝ,F) b b)))).preimage_mem_nhds hn₁
  filter_upwards [hn',continuousAt_snd.preimage_mem_nhds
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy)] with q hq hqt
  exact chartTwoForm_manifoldPullback_at (α := fun _ => α q.1) (p := (0,q.2)) hqt
    (hq.mdifferentiableAt (by simp))

theorem parameterManifoldPullbackTwoForm_contDiffAt
    {α : P → ManifoldTwoForm E M} {g : N → M} {p : P} {b : N}
    (hα : ContDiffAt ℝ ∞
      (fun q : P × E => chartTwoForm (α q.1) (g b) q.2)
      (p,extChartAt 𝓘(ℝ,E) (g b) (g b)))
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g b) :
    ContDiffAt ℝ ∞
      (fun q : P × F => chartTwoForm (parameterManifoldPullbackTwoForm α g q.1) b q.2)
      (p,extChartAt 𝓘(ℝ,F) b b) := by
  let y := extChartAt 𝓘(ℝ,F) b b
  have hb := mem_extChartAt_source (I := 𝓘(ℝ,F)) b
  have hy : y∈(extChartAt 𝓘(ℝ,F) b).target := (extChartAt 𝓘(ℝ,F) b).map_source hb
  have he : (extChartAt 𝓘(ℝ,F) b).symm y=b := (extChartAt 𝓘(ℝ,F) b).left_inv hb
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hy)
  have hg' : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g ((extChartAt 𝓘(ℝ,F) b).symm y) := by
    rw [he]; exact hg
  have hα' : ContDiffAt ℝ ∞
      (fun q : P × E => chartTwoForm (α q.1) ((g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y) q.2)
      (p,extChartAt 𝓘(ℝ,E) ((g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y)
        ((g ∘ (extChartAt 𝓘(ℝ,F) b).symm) y)) := by
    simpa only [Function.comp_apply,he] using hα
  have hs := parameterEuclideanPullbackTwoForm_contDiffAt
    (α := α) (g := g ∘ (extChartAt 𝓘(ℝ,F) b).symm) (p := (p,y)) hα' (hg'.comp y hi)
  exact hs.congr_of_eventuallyEq (parameterManifoldPullbackTwoForm_chart_germ α p hg)

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

 def annularCoverTwoCoefficient
    (D : AnnularHandleData Plane M)
    (Λ : ManifoldTwoForm Plane M) (q : Plane) : ℝ :=
  euclideanPullbackTwoForm (fun _ => Λ) (D.handleAnnularCover) (0,q) (1,0) (0,1)

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
 theorem annularCoverDomain_eq
    (D : AnnularHandleData Plane M)
    :
    D.annularCoverDomain=Ioo (-D.width) D.width ×ˢ univ := by
  rw [annularCoverDomain,D.source_eq]
  rfl

 theorem annularCoverTwoCoefficient_smooth
    (D : AnnularHandleData Plane M)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ) :
    ContDiffOn ℝ ∞ (D.annularCoverTwoCoefficient Λ) (D.annularCoverDomain) := by
  intro q hq
  have hs := euclideanPullbackTwoForm_contDiffAt (Ω := fun _ : ℝ => Λ)
    (g := D.handleAnnularCover) (p := (0,q))
    (SmoothTwoFormFamily.const (P := ℝ) hΛ) (D.handleAnnularCover_smoothAt hq)
  exact (((hs.clm_apply contDiffAt_const).clm_apply contDiffAt_const).comp q
    (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
 theorem annularCoverTwoCoefficient_ne_zero
    (D : AnnularHandleData Plane M)
    {Λ : ManifoldTwoForm Plane M}
    (hs : ∀ x u v,Λ x u v= -Λ x v u)
    (hp : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0<chartTwoForm Λ c y (1,0) (0,1))
    {q : Plane} (hq : q∈D.annularCoverDomain) :
    D.annularCoverTwoCoefficient Λ q≠0 := by
  intro hz
  let L := D.handleAnnularCoverLinearEquiv hq
  let B := (Λ (D.handleAnnularCover q)).bilinearComp (L : Plane →L[ℝ] Plane) (L : Plane →L[ℝ] Plane)
  have hB : ∀ u v,B u v= -B v u := fun u v => hs _ _ _
  have hB0 : B (1,0) (0,1)=0 := hz
  have hzero : Λ (D.handleAnnularCover q)=0 := by
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    have hv := planar_skew_coefficient B hB (L.symm u) (L.symm v)
    simpa only [B,ContinuousLinearMap.bilinearComp_apply,ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply,hB0,zero_mul,zero_apply] using hv
  let c := D.handleAnnularCover q
  have hc := mem_extChartAt_source (I := 𝓘(ℝ,Plane)) c
  have hi := hp c (extChartAt 𝓘(ℝ,Plane) c c) ((extChartAt 𝓘(ℝ,Plane) c).map_source hc)
  have hcc : (extChartAt 𝓘(ℝ,Plane) c).symm (extChartAt 𝓘(ℝ,Plane) c c)=c :=
    (extChartAt 𝓘(ℝ,Plane) c).left_inv hc
  simp only [chartTwoForm,hcc,ContinuousLinearMap.bilinearComp_apply] at hi
  change 0<Λ (D.handleAnnularCover q) _ _ at hi
  rw [hzero] at hi
  exact (lt_irrefl 0) hi

 theorem annularCoverTwoCoefficient_positive
    (D : AnnularHandleData Plane M)
    (hor : PositivePartialChart D.densityChart)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hs : ∀ x u v,Λ x u v= -Λ x v u)
    (hp : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0<chartTwoForm Λ c y (1,0) (0,1))
    {q : Plane} (hq : q∈D.annularCoverDomain) :
    0<D.annularCoverTwoCoefficient Λ q := by
  let z : Plane := (q.1,1/2)
  have hsdom : q.1∈Ioo (-D.width) D.width := by
    rw [D.annularCoverDomain_eq] at hq
    exact hq.1
  have hz : z∈D.densityChart.source := by
    rw [D.densityChart_source]
    exact ⟨hsdom,by norm_num [z]⟩
  have hzd : z∈D.annularCoverDomain := by
    rw [D.annularCoverDomain_eq]
    exact ⟨hsdom,mem_univ _⟩
  let c := D.densityChart z
  have hc : D.densityChart z∈(extChartAt 𝓘(ℝ,Plane) c).source := mem_extChartAt_source c
  have hpz : 0<D.annularCoverTwoCoefficient Λ z := by
    change 0<partialChartCoefficient D.densityChart Λ z
    rw [partialChartCoefficient_change _ hs hz hc]
    exact mul_pos (hor c z hz hc) (hp c _ ((extChartAt 𝓘(ℝ,Plane) c).map_source hc))
  by_contra hn
  have hn' : D.annularCoverTwoCoefficient Λ q≤0 := le_of_not_gt hn
  have hconn : IsPreconnected (D.annularCoverDomain) := by
    rw [D.annularCoverDomain_eq]
    exact isPreconnected_Ioo.prod isPreconnected_univ
  obtain ⟨y,hy,hy0⟩ := hconn.intermediate_value hq hzd
    (D.annularCoverTwoCoefficient_smooth hΛ).continuousOn ⟨hn',hpz.le⟩
  exact D.annularCoverTwoCoefficient_ne_zero hs hp hy hy0

theorem annularCover_positive_exterior
    (D : AnnularHandleData Plane M)
    (hor : PositivePartialChart D.densityChart)
    {Λ : ManifoldTwoForm Plane M} (hΛ : SmoothTwoForm Λ)
    (hs : ∀ x u v,Λ x u v= -Λ x v u)
    (hp : ∀ c y,y∈(extChartAt 𝓘(ℝ,Plane) c).target→
      0<chartTwoForm Λ c y (1,0) (0,1))
    {γ : ManifoldOneForm Plane M} {r : ℝ} (hr : 0<r)
    (hγ : ∀ x∈D.chart.target,manifoldExteriorOneForm γ x=r • Λ x)
    {q : Plane} (hq : q∈D.annularCoverDomain) :
    0 < manifoldExteriorOneForm γ (D.handleAnnularCover q)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (D.handleAnnularCover) q (1,0))
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (D.handleAnnularCover) q (0,1)) := by
  have heq := hγ (D.handleAnnularCover q) (D.chart.map_source hq)
  have hv := congrArg (fun B : Plane →L[ℝ] Plane →L[ℝ] ℝ =>
    B (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (D.handleAnnularCover) q (1,0))
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (D.handleAnnularCover) q (0,1))) heq
  have hp' := mul_pos hr (D.annularCoverTwoCoefficient_positive hor hΛ hs hp hq)
  exact lt_of_lt_of_eq hp' hv.symm

omit [IsManifold 𝓘(ℝ,Plane) ∞ M] in
theorem handleAnnularCover_surjOn
    (D : AnnularHandleData Plane M) :
    SurjOn (D.handleAnnularCover) (D.annularCoverDomain) D.chart.target := by
  intro x hx
  let z := D.chart.symm x
  let q : Plane := (z.1,shortCircleArgument z.2)
  have heq : cylinderCover q=z := by
    exact Prod.ext rfl (circleTurn_shortCircleArgument z.2)
  refine ⟨q,?_,?_⟩
  · change cylinderCover q∈D.chart.source
    rw [heq]
    exact D.chart.map_target hx
  · change D.chart (cylinderCover q)=x
    rw [heq]
    exact D.chart.right_inv hx

end PackingSufficiencySupport.Hamiltonian.AnnularHandleData
end

end OAI
