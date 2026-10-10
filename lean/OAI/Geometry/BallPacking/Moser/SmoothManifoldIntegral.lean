import Mathlib
import OAI.Geometry.BallPacking.Moser.AnnularFinalPacking

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem contMDiff_fixed_integral {f : ℝ × M → F}
    (hf : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,F) ∞ f) :
    ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ (fun x => ∫ s in (0:ℝ)..1, f (s,x)) := by
  intro x
  let c := extChartAt 𝓘(ℝ,E) x
  let g : ℝ × E → F := fun q => f (q.1,c.symm q.2)
  have hg : ContDiffOn ℝ ∞ g (univ ×ˢ c.target) := by
    intro p hp
    have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) x).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x).mem_nhds hp.2)
    exact ((hf.contMDiffAt.comp p
      (contDiffAt_fst.contMDiffAt.prodMk (hi.comp p contDiffAt_snd.contMDiffAt))).contDiffAt).contDiffWithinAt
  have hs := (contDiffOn_fixed_integral (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x) hg).contDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x).mem_nhds (mem_extChartAt_target x))
  have hh := hs.contMDiffAt.comp x (contMDiffAt_extChartAt (I := 𝓘(ℝ,E)) (n := ∞))
  apply hh.congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_source (I := 𝓘(ℝ,E)) x).mem_nhds (mem_extChartAt_source x)] with y hy
  change (∫ s in (0:ℝ)..1, f (s,y)) = ∫ s in (0:ℝ)..1, f (s,c.symm (c y))
  rw [c.left_inv hy]


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable (E : Type) (M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

structure SmoothCircleAction where
  toFun : ℝ × M → M
  smooth : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ toFun
  zero : ∀ x, toFun (0,x) = x
  add : ∀ s t x, toFun (s+t,x) = toFun (s,toFun (t,x))
  period : ∀ s x, toFun (s+1,x) = toFun (s,x)

variable {E M}
namespace SmoothCircleAction
variable (A : SmoothCircleAction E M)

def slice (s : ℝ) (x : M) : M := A.toFun (s,x)

theorem slice_smooth (s : ℝ) : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (A.slice s) :=
  A.smooth.comp (contMDiff_const.prodMk contMDiff_id)

def differential (s : ℝ) (x : M) : E →L[ℝ] E :=
  manifoldMapDifferential (A.slice s) x

theorem differential_add (s t : ℝ) (x : M) :
    A.differential (s+t) x = (A.differential s (A.slice t x)).comp (A.differential t x) := by
  have he : A.slice (s+t) = A.slice s ∘ A.slice t := funext (A.add s t)
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (A.slice (s+t)) x = _
  rw [he]
  exact ((A.slice_smooth s).mdifferentiable (by simp) _).hasMFDerivAt.comp x
    ((A.slice_smooth t).mdifferentiable (by simp) x).hasMFDerivAt |>.mfderiv

@[simp] theorem differential_zero (x : M) : A.differential 0 x = ContinuousLinearMap.id ℝ E := by
  have he : A.slice 0 = id := funext A.zero
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (A.slice 0) x = _
  rw [he]
  exact mfderiv_id

@[simp] theorem differential_period (s : ℝ) (x : M) :
    A.differential (s+1) x = A.differential s x := by
  have he : A.slice (s+1) = A.slice s := funext (A.period s)
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (A.slice (s+1)) x = _
  rw [he]
  rfl

theorem slice_inverse (s : ℝ) (x : M) : A.slice (-s) (A.slice s x) = x := by
  change A.toFun (-s,A.toFun (s,x)) = x
  rw [←A.add,neg_add_cancel,A.zero]

theorem differential_invertible (s : ℝ) (x : M) : (A.differential s x).IsInvertible := by
  refine ContinuousLinearMap.IsInvertible.of_inverse (g := A.differential (-s) (A.slice s x)) ?_ ?_
  · have h := A.differential_add s (-s) (A.slice s x)
    rw [add_neg_cancel,A.differential_zero,A.slice_inverse] at h
    exact h.symm
  · rw [←A.differential_add,neg_add_cancel,A.differential_zero]

def average (f : ℝ × M → ℝ) (p : ℝ × M) : ℝ :=
  ∫ s in (0:ℝ)..1, f (p.1,A.slice s p.2)

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem average_smooth {f : ℝ × M → ℝ}
    (hf : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ f) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ (A.average f) := by
  have hprod : IsManifold ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) ∞ (ℝ × M) := inferInstance
  let instProd : ChartedSpace (ℝ × E) (ℝ × M) := prodChartedSpace ℝ ℝ E M
  have : IsManifold 𝓘(ℝ,ℝ × E) ∞ (ℝ × M) := by
    simpa only [modelWithCornersSelf_prod,instProd] using hprod
  have hg : ContMDiff ((𝓘(ℝ,ℝ)).prod ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E))) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × (ℝ × M) => f (q.2.1,A.slice q.1 q.2.2)) :=
    hf.comp (contMDiff_snd.fst.prodMk
      (A.smooth.comp (contMDiff_fst.prodMk contMDiff_snd.snd)))
  have hg' : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ℝ × E)) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × (ℝ × M) => f (q.2.1,A.slice q.1 q.2.2)) := by
    simpa only [modelWithCornersSelf_prod,instProd] using hg
  convert! contMDiff_fixed_integral hg' using 1
  ·
    simp only [modelWithCornersSelf_prod]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem average_invariant (f : ℝ × M → ℝ) (t s : ℝ) (x : M) :
    A.average f (t,A.slice s x) = A.average f (t,x) := by
  have hp : Function.Periodic (fun r => f (t,A.slice r x)) 1 := by
    intro r
    change f (t,A.toFun (r+1,x)) = f (t,A.toFun (r,x))
    rw [A.period]
  change (∫ r in (0:ℝ)..1, f (t,A.toFun (r,A.toFun (s,x)))) = _
  simp_rw [←A.add]
  rw [intervalIntegral.integral_comp_add_right (fun r => f (t,A.toFun (r,x))) s]
  simpa only [zero_add,add_comm (1:ℝ) s,average,slice] using hp.intervalIntegral_add_eq s 0

end SmoothCircleAction

end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chartOneForm_reconstruct (α : ManifoldOneForm E M) {c x : M}
    (hc : x ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    (chartOneForm α c (extChartAt 𝓘(ℝ,E) c x)).comp (chartDifferential c x) = α x := by
  have hC : (chartDifferential (E := E) c x).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E)) hc using 1
  unfold chartOneForm
  rw [(extChartAt 𝓘(ℝ,E) c).left_inv hc]
  ext v
  exact congrArg (α x) (hC.inverse_apply_self v)

namespace SmoothCircleAction
variable (A : SmoothCircleAction E M)

def averageOneForm (α : ℝ → ManifoldOneForm E M) (t : ℝ) (x : M) : E →L[ℝ] ℝ :=
  ∫ s in (0:ℝ)..1, parameterPullbackOneForm (E := E) (F := E) α A.toFun s t x

theorem pullbackOneForm_continuous {α : ℝ → ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) (t : ℝ) (x : M) :
    Continuous (fun s => parameterPullbackOneForm (E := E) (F := E) α A.toFun s t x) := by
  have hs := parameterPullbackOneForm_smooth (E := E) (F := E) A.smooth hα x
  have hc : Continuous (fun s : ℝ => chartOneForm
      (parameterPullbackOneForm (E := E) (F := E) α A.toFun s t) x (extChartAt 𝓘(ℝ,E) x x)) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    have hfull : ContinuousAt (fun q : ℝ × (ℝ × E) => chartOneForm
        (parameterPullbackOneForm (E := E) (F := E) α A.toFun q.1 q.2.1) x q.2.2)
        (s,(t,extChartAt 𝓘(ℝ,E) x x)) :=
      (hs.contDiffAt ((isOpen_univ.prod (isOpen_univ.prod
        (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x))).mem_nhds
          ⟨mem_univ _,mem_univ _,mem_extChartAt_target x⟩)).continuousAt
    have hmap : ContinuousAt (fun r : ℝ => (r,(t,extChartAt 𝓘(ℝ,E) x x))) s :=
      continuousAt_id.prodMk continuousAt_const
    exact hfull.comp (f := fun r : ℝ => (r,(t,extChartAt 𝓘(ℝ,E) x x))) hmap
  have hh := hc.clm_comp (continuous_const (y := chartDifferential (E := E) x x))
  convert! hh using 1
  funext s
  exact (chartOneForm_reconstruct _ (mem_extChartAt_source x)).symm

theorem chart_averageOneForm {α : ℝ → ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) (t : ℝ) (c : M) (y : E) :
    chartOneForm (A.averageOneForm α t) c y =
      ∫ s in (0:ℝ)..1, chartOneForm (parameterPullbackOneForm (E := E) (F := E) α A.toFun s t) c y := by
  let x := (extChartAt 𝓘(ℝ,E) c).symm y
  let L := (ContinuousLinearMap.compL ℝ E E ℝ).flip (chartDifferential (E := E) c x).inverse
  exact (L.intervalIntegral_comp_comm ((A.pullbackOneForm_continuous hα t x).intervalIntegrable 0 1)).symm

variable [FiniteDimensional ℝ E]

theorem averageOneForm_smooth {α : ℝ → ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) (c : M) :
    ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (A.averageOneForm α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) := by
  have hs := contDiffOn_fixed_integral (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c))
    (parameterPullbackOneForm_smooth (E := E) (F := E) A.smooth hα c)
  apply hs.congr
  intro p _
  exact A.chart_averageOneForm hα p.1 c p.2

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem pullbackOneForm_add (α : ℝ → ManifoldOneForm E M) (s r t : ℝ) (x : M) :
    parameterPullbackOneForm (E := E) (F := E) α A.toFun (r+s) t x =
      (parameterPullbackOneForm (E := E) (F := E) α A.toFun r t (A.slice s x)).comp (A.differential s x) := by
  change (α t (A.slice (r+s) x)).comp (A.differential (r+s) x) = _
  rw [A.differential_add]
  have he : A.slice (r+s) x = A.slice r (A.slice s x) := A.add r s x
  rw [he]
  rfl

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem pullbackOneForm_periodic (α : ℝ → ManifoldOneForm E M) (t : ℝ) (x : M) :
    Function.Periodic (fun r => parameterPullbackOneForm (E := E) (F := E) α A.toFun r t x) 1 := by
  intro r
  change (α t (A.slice (r+1) x)).comp (A.differential (r+1) x) = _
  rw [A.differential_period]
  change (α t (A.toFun (r+1,x))).comp _ = _
  rw [A.period]
  rfl

omit [FiniteDimensional ℝ E] in

theorem averageOneForm_invariant {α : ℝ → ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) (s t : ℝ) (x : M) :
    (A.averageOneForm α t (A.slice s x)).comp (A.differential s x) = A.averageOneForm α t x := by
  let L := (ContinuousLinearMap.compL ℝ E E ℝ).flip (A.differential s x)
  have hi : IntervalIntegrable (fun r => parameterPullbackOneForm (E := E) (F := E) α A.toFun r t (A.slice s x)) volume 0 1 :=
    (A.pullbackOneForm_continuous hα t (A.slice s x)).intervalIntegrable 0 1
  change L (∫ r in (0:ℝ)..1, parameterPullbackOneForm (E := E) (F := E) α A.toFun r t (A.slice s x)) = _
  rw [←L.intervalIntegral_comp_comm hi]
  change (∫ r in (0:ℝ)..1,
    (parameterPullbackOneForm (E := E) (F := E) α A.toFun r t (A.slice s x)).comp (A.differential s x)) = _
  simp_rw [←A.pullbackOneForm_add]
  rw [intervalIntegral.integral_comp_add_right
    (fun r => parameterPullbackOneForm (E := E) (F := E) α A.toFun r t x) s]
  simpa only [zero_add,add_comm (1:ℝ) s,averageOneForm] using
    (A.pullbackOneForm_periodic α t x).intervalIntegral_add_eq s 0

end SmoothCircleAction

end

section
open scoped ContDiff Topology
open Set Function
variable {S P F : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffOn_fiber_derivative {U : Set P} (hU : IsOpen U) {f : S × P → F}
    (hf : ContDiffOn ℝ ∞ f (univ ×ˢ U)) :
    ContDiffOn ℝ ∞ (fun q : S × P => fderiv ℝ (fun p => f (q.1,p)) q.2) (univ ×ˢ U) := by
  have hD := (hf.fderiv_of_isOpen (m := ∞) (isOpen_univ.prod hU) (by simp)).clm_comp
    (contDiffOn_const (c := ContinuousLinearMap.inr ℝ S P))
  apply hD.congr
  intro q hq
  have hc : HasFDerivAt (fun p : P => (q.1,p)) (ContinuousLinearMap.inr ℝ S P) q.2 := by
    convert! (hasFDerivAt_const (𝕜 := ℝ) q.1 q.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) q.2) using 1
  have hh := ((hf.contDiffAt ((isOpen_univ.prod hU).mem_nhds hq)).differentiableAt
    (by simp)).hasFDerivAt.comp q.2 hc
  exact hh.fderiv

theorem continuous_at_fixed_fiber_derivative {U : Set P} (hU : IsOpen U) {f : S × P → F}
    (hf : ContDiffOn ℝ ∞ f (univ ×ˢ U)) {x : P} (hx : x ∈ U) :
    Continuous (fun s : S => fderiv ℝ (fun p => f (s,p)) x) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  exact ((contDiffOn_fiber_derivative hU hf).contDiffAt
    ((isOpen_univ.prod hU).mem_nhds ⟨mem_univ _,hx⟩)).continuousAt.comp
      (continuousAt_id.prodMk continuousAt_const)


end

section
open scoped ContDiff Topology
open Set Function
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def timePullbackOneForm (α : ℝ × E → E →L[ℝ] ℝ) (g : F → E)
    (p : ℝ × F) : F →L[ℝ] ℝ := (α (p.1,g p.2)).comp (fderiv ℝ g p.2)

def timePullbackTwoForm (Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (g : F → E)
    (p : ℝ × F) : F →L[ℝ] F →L[ℝ] ℝ :=
  (Ω (p.1,g p.2)).bilinearComp (fderiv ℝ g p.2) (fderiv ℝ g p.2)

theorem timePullbackOneForm_contDiffAt {α : ℝ × E → E →L[ℝ] ℝ}
    {g : F → E} {p : ℝ × F} (hα : ContDiffAt ℝ ∞ α (p.1,g p.2))
    (hg : ContDiffAt ℝ ∞ g p.2) : ContDiffAt ℝ ∞ (timePullbackOneForm α g) p :=
  (hα.comp p (contDiffAt_fst.prodMk (hg.comp p contDiffAt_snd))).clm_comp
    ((hg.fderiv_right (by simp)).comp p contDiffAt_snd)

theorem timePullbackTwoForm_contDiffAt {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    {g : F → E} {p : ℝ × F} (hΩ : ContDiffAt ℝ ∞ Ω (p.1,g p.2))
    (hg : ContDiffAt ℝ ∞ g p.2) : ContDiffAt ℝ ∞ (timePullbackTwoForm Ω g) p := by
  have hval := hΩ.comp p (contDiffAt_fst.prodMk (hg.comp p contDiffAt_snd))
  have hd := (hg.fderiv_right (m := ∞) (by simp)).comp p contDiffAt_snd
  exact smooth_bilinear_flip ((smooth_bilinear_flip (hval.clm_comp hd)).clm_comp hd)

theorem timePullbackOneForm_fderiv {α : ℝ × E → E →L[ℝ] ℝ}
    {g : F → E} {p : ℝ × F} (hα : ContDiffAt ℝ ∞ α (p.1,g p.2))
    (hg : ContDiffAt ℝ ∞ g p.2) (v : ℝ × F) (w : F) :
    fderiv ℝ (timePullbackOneForm α g) p v w =
      fderiv ℝ α (p.1,g p.2) (v.1,fderiv ℝ g p.2 v.2) (fderiv ℝ g p.2 w) +
      α (p.1,g p.2) (fderiv ℝ (fderiv ℝ g) p.2 v.2 w) := by
  have hmap := (hasFDerivAt_fst (p := p)).prodMk
    ((hg.differentiableAt (by simp)).hasFDerivAt.comp p (hasFDerivAt_snd (p := p)))
  have hd := ((hα.differentiableAt (by simp)).hasFDerivAt.comp p hmap).clm_comp
    (((hg.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.comp p
      (hasFDerivAt_snd (p := p)))
  rw [show fderiv ℝ (timePullbackOneForm α g) p = _ from hd.fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.prod_apply]
  exact add_comm _ _

theorem timePullbackOneForm_exterior {α : ℝ × E → E →L[ℝ] ℝ}
    {g : F → E} {p : ℝ × F} (hα : ContDiffAt ℝ ∞ α (p.1,g p.2))
    (hg : ContDiffAt ℝ ∞ g p.2) (v w : F) :
    fderiv ℝ (timePullbackOneForm α g) p (0,v) w -
      fderiv ℝ (timePullbackOneForm α g) p (0,w) v =
    fderiv ℝ α (p.1,g p.2) (0,fderiv ℝ g p.2 v) (fderiv ℝ g p.2 w) -
      fderiv ℝ α (p.1,g p.2) (0,fderiv ℝ g p.2 w) (fderiv ℝ g p.2 v) := by
  rw [timePullbackOneForm_fderiv hα hg,timePullbackOneForm_fderiv hα hg]
  have hs := hg.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  rw [hs.eq v w]
  simp only
  ring

theorem timePullbackTwoForm_time {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    {g : F → E} {p : ℝ × F} (hΩ : ContDiffAt ℝ ∞ Ω (p.1,g p.2))
    (hg : ContDiffAt ℝ ∞ g p.2) (v w : F) :
    fderiv ℝ (timePullbackTwoForm Ω g) p (1,0) v w =
      fderiv ℝ Ω (p.1,g p.2) (1,0) (fderiv ℝ g p.2 v) (fderiv ℝ g p.2 w) := by
  have hL := (((timePullbackTwoForm_contDiffAt hΩ hg).differentiableAt (by simp)).hasFDerivAt.clm_apply
    (hasFDerivAt_const v p)).clm_apply (hasFDerivAt_const w p)
  have hLt := hL.comp_hasDerivAt p.1 ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  have hR := (((hΩ.differentiableAt (by simp)).hasFDerivAt.clm_apply
    (hasFDerivAt_const (fderiv ℝ g p.2 v) (p.1,g p.2))).clm_apply
    (hasFDerivAt_const (fderiv ℝ g p.2 w) (p.1,g p.2))).comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 (g p.2)))
  have he := hLt.unique hR
  simpa only [add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.apply_apply,
    zero_apply,map_zero,zero_add] using he

theorem timePullback_exact_time {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    {α : ℝ × E → E →L[ℝ] ℝ} {g : F → E} {p : ℝ × F}
    (hΩ : ContDiffAt ℝ ∞ Ω (p.1,g p.2)) (hα : ContDiffAt ℝ ∞ α (p.1,g p.2))
    (hg : ContDiffAt ℝ ∞ g p.2)
    (he : ∀ v w, fderiv ℝ Ω (p.1,g p.2) (1,0) v w =
      fderiv ℝ α (p.1,g p.2) (0,v) w - fderiv ℝ α (p.1,g p.2) (0,w) v) (v w : F) :
    fderiv ℝ (timePullbackTwoForm Ω g) p (1,0) v w =
      fderiv ℝ (timePullbackOneForm α g) p (0,v) w -
      fderiv ℝ (timePullbackOneForm α g) p (0,w) v := by
  rw [timePullbackTwoForm_time hΩ hg,timePullbackOneForm_exterior hα hg]
  exact he _ _


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_localized_manifold_moser_field
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    {U : Set ℝ} (hU : IsOpen U) (hI : Icc (0:ℝ) 1 ⊆ U)
    (hinv : ∀ t ∈ U, ∀ x, (Ω t x).IsInvertible) :
    ∃ V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2,
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
        (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)) ∧
      (∀ᶠ t in 𝓝ˢ (Icc (0:ℝ) 1), ∀ x, V (t,x) = manifoldMoserField Ω α (t,x)) ∧
      (∀ t x, α t x = 0 → V (t,x) = 0) := by
  obtain ⟨χ,hχ,_,hχU,hχ1,_⟩ := exists_smooth_cutoff isCompact_Icc hU hI
  let V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2 :=
    fun p => χ p.1 • manifoldMoserField Ω α p
  have he (c : M) (q : ℝ × E) : timeChartField V c q =
      χ q.1 • timeChartField (manifoldMoserField Ω α) c q := by
    dsimp only [timeChartField,V]
    exact (chartDifferential c _).map_smul _ _
  refine ⟨V,?_,?_,?_⟩
  · apply timeField_smooth_of_coordinates
    intro p
    let q : ℝ × E := (p.1,extChartAt 𝓘(ℝ,E) p.2 p.2)
    have hq : q.2 ∈ (extChartAt 𝓘(ℝ,E) p.2).target := mem_extChartAt_target p.2
    have hn : (univ ×ˢ (extChartAt 𝓘(ℝ,E) p.2).target) ∈ 𝓝 q :=
      (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) p.2)).mem_nhds
        ⟨mem_univ _,hq⟩
    by_cases hp : p.1 ∈ U
    · have hni : ∀ᶠ z : ℝ × E in 𝓝 q,
          (Ω z.1 ((extChartAt 𝓘(ℝ,E) p.2).symm z.2)).IsInvertible := by
        filter_upwards [continuousAt_fst.preimage_mem_nhds (hU.mem_nhds hp)] with z hz
        exact hinv z.1 hz _
      have hs := timeChartField_moser_contDiffAt hq ((hΩ p.2).contDiffAt hn)
        ((hα p.2).contDiffAt hn) hni
      exact ((hχ.contDiffAt.comp q contDiffAt_fst).smul hs).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (he p.2))
    · have hp' : p.1 ∉ tsupport χ := fun h => hp (hχU h)
      apply (contDiffAt_const (c := (0:E))).congr_of_eventuallyEq
      have hzero : ∀ᶠ t in 𝓝 p.1, χ t = 0 :=
        (isClosed_tsupport χ).isOpen_compl.eventually_mem hp' |>.mono
          (fun _ ht => image_eq_zero_of_notMem_tsupport ht)
      filter_upwards [continuousAt_fst.preimage_mem_nhds hzero] with z hz
      rw [he, hz,zero_smul]
  · filter_upwards [hχ1] with t ht
    intro x
    change χ t • _ = _
    rw [ht,one_smul]
  · intro t x hx
    change χ t • (-((Ω t x).inverse (α t x))) = (0:E)
    rw [hx,map_zero,neg_zero,smul_zero]


end

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem manifold_moser_PDE
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {U : Set ℝ} (hU : IsOpen U) {t : ℝ} (ht : t ∈ U)
    (hinv : ∀ s ∈ U, ∀ x, (Ω s x).IsInvertible)
    (heq : ∀ᶠ s in 𝓝 t, ∀ x, V (s,x) = manifoldMoserField Ω α (s,x))
    {c : M} {y : E} (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target)
    (hΩ : ContDiffAt ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y))
    (hα : ContDiffAt ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2) (t,y))
    (hskew : ∀ u v, chartTwoForm (Ω t) c y u v = -chartTwoForm (Ω t) c y v u)
    (hclosed : ∀ u v w,
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y) (0,u) v w -
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y) (0,v) u w +
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y) (0,w) u v = 0)
    (htime : ∀ v w,
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y) (1,0) v w =
      fderiv ℝ (fun q : ℝ × E => chartOneForm (α q.1) c q.2) (t,y) (0,v) w -
      fderiv ℝ (fun q : ℝ × E => chartOneForm (α q.1) c q.2) (t,y) (0,w) v)
    (v w : E) :
    fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y)
        (1,timeChartField V c (t,y)) v w +
      chartTwoForm (Ω t) c y (fderiv ℝ (timeChartField V c) (t,y) (0,v)) w +
      chartTwoForm (Ω t) c y v (fderiv ℝ (timeChartField V c) (t,y) (0,w)) = 0 := by
  have hn : (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) ∈ 𝓝 (t,y) :=
    (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds
      ⟨mem_univ _,hy⟩
  have hX := ((timeChartField_contDiffOn hV c).contDiffAt hn).differentiableAt (by simp)
  apply local_moser_transport_equation (hΩ.differentiableAt (by simp))
    (hα.differentiableAt (by simp)) hX _ hskew hclosed htime
  have htimeU : ∀ᶠ q : ℝ × E in 𝓝 (t,y), q.1 ∈ U :=
    continuousAt_fst.preimage_mem_nhds (hU.mem_nhds ht)
  have htarg : ∀ᶠ q : ℝ × E in 𝓝 (t,y), q.2 ∈ (extChartAt 𝓘(ℝ,E) c).target :=
    continuousAt_snd.preimage_mem_nhds ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hy)
  filter_upwards [htimeU,htarg,continuousAt_fst.preimage_mem_nhds heq] with q hq hqt hqe
  have hVe : timeChartField V c q = timeChartField (manifoldMoserField Ω α) c q := by
    dsimp only [timeChartField]
    rw [hqe ((extChartAt 𝓘(ℝ,E) c).symm q.2)]
  rw [hVe]
  exact chart_moser_contraction hqt (hinv q.1 hq _)



structure ManifoldMoserData (Ω : ℝ → ManifoldTwoForm E M)
    (α : ℝ → ManifoldOneForm E M) : Prop where
  smooth_two : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
    (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)
  smooth_one : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
    (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)
  nondegenerate : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, (Ω t x).IsInvertible
  skew : ∀ t ∈ Icc (0:ℝ) 1, ∀ c y, y ∈ (extChartAt 𝓘(ℝ,E) c).target → ∀ u v,
    chartTwoForm (Ω t) c y u v = -chartTwoForm (Ω t) c y v u
  closed : ∀ t ∈ Icc (0:ℝ) 1, ∀ c y, y ∈ (extChartAt 𝓘(ℝ,E) c).target → ∀ u v w,
    fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y) (0,u) v w -
    fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y) (0,v) u w +
    fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y) (0,w) u v = 0
  exact_time : ∀ t ∈ Icc (0:ℝ) 1, ∀ c y, y ∈ (extChartAt 𝓘(ℝ,E) c).target → ∀ v w,
    fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y) (1,0) v w =
    fderiv ℝ (fun q : ℝ × E => chartOneForm (α q.1) c q.2) (t,y) (0,v) w -
    fderiv ℝ (fun q : ℝ × E => chartOneForm (α q.1) c q.2) (t,y) (0,w) v

variable [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]

theorem exists_compact_manifold_moser
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    (h : ManifoldMoserData Ω α) :
    ∃ Φ Ψ : ℝ × M → M,
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ ∧
      (∀ x, Φ (0,x) = x) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x, Ψ (t,Φ (t,x)) = x ∧ Φ (t,Ψ (t,x)) = x) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x v w, manifoldPullback Φ Ω t x v w = Ω 0 x v w) ∧
      (∀ x, (∀ t, α t x = 0) → ∀ t, Φ (t,x) = x) := by
  let U : Set ℝ := {t | ∀ x, (Ω t x).IsInvertible}
  have hU : IsOpen U := manifoldTwoForm_isOpen_nondegenerate_times h.smooth_two
  have hIU : Icc (0:ℝ) 1 ⊆ U := h.nondegenerate
  obtain ⟨V,hV,hVe,hVzero⟩ := exists_localized_manifold_moser_field h.smooth_two h.smooth_one
    hU hIU (fun _ ht => ht)
  obtain ⟨Φ,Ψ,hΦ,hΨ,hΦ0,hinv,hODE,hfix⟩ := exists_nonautonomous_manifold_flow hV
  refine ⟨Φ,Ψ,hΦ,hΨ,hΦ0,hinv,?_,?_⟩
  · have hd (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : M) (v w : E) :
        HasDerivAt (fun s => manifoldPullback Φ Ω s x v w) 0 t := by
      apply manifold_form_transport_derivative hΦ hV isOpen_Ioo hODE h.smooth_two
        (show t ∈ Ioo (-2:ℝ) 2 by constructor <;> linarith [ht.1,ht.2])
      intro c y hy u z
      have hn : (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) ∈ 𝓝 (t,y) :=
        (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds
          ⟨mem_univ _,hy⟩
      exact manifold_moser_PDE hV hU (hIU ht) (fun _ hs => hs)
        (hVe.filter_mono (nhds_le_nhdsSet ht)) hy ((h.smooth_two c).contDiffAt hn)
        ((h.smooth_one c).contDiffAt hn) (h.skew t ht c y hy) (h.closed t ht c y hy)
        (h.exact_time t ht c y hy) u z
    intro t ht x v w
    rw [manifold_form_transport_constant hd ht]
    have hid : (fun y => Φ (0,y)) = id := funext hΦ0
    have hD : preferredDifferential (fun y => Φ (0,y)) x =
        ContinuousLinearMap.id ℝ E := by
      change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun y => Φ (0,y)) x = _
      rw [hid]
      exact mfderiv_id
    rw [manifoldPullback,hD]
    simp only [hΦ0,ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.id_apply]
  · intro x hx
    exact hfix x (fun t => hVzero t x (hx t))



end PackingSufficiencySupport.Hamiltonian
end

end OAI
