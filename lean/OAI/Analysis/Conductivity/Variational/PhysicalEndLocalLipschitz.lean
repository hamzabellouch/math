import Mathlib
import OAI.Analysis.Conductivity.Fourier.TorusPoissonContinuous
import OAI.Analysis.Conductivity.Fourier.EndPoissonRepresentative

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

def LocalLipAt {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    (f : E → F) (x : E) : Prop := ∃ K,∃ t∈𝓝 x,LipschitzOnWith K f t

lemma LocalLipAt.continuousAt {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {f : E → F} {x : E} (h : LocalLipAt f x) : ContinuousAt f x := by
  obtain ⟨K,t,ht,hh⟩ := h
  exact hh.continuousOn.continuousAt ht

lemma LocalLipAt.comp {E F G : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    [PseudoMetricSpace G] {f : E → F} {g : F → G} {x : E}
    (hg : LocalLipAt g (f x)) (hf : LocalLipAt f x) : LocalLipAt (g ∘ f) x := by
  have hcont := hf.continuousAt
  obtain ⟨K,t,ht,hK⟩ := hf
  obtain ⟨L,u,hu,hL⟩ := hg
  refine ⟨L*K,t∩f⁻¹' u,inter_mem ht (hcont hu),?_⟩
  exact hL.comp (hK.mono inter_subset_left) ((mapsTo_preimage f u).mono_left inter_subset_right)

lemma LocalLipAt.prodMk {E F G : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    [PseudoMetricSpace G] {f : E → F} {g : E → G} {x : E}
    (hf : LocalLipAt f x) (hg : LocalLipAt g x) : LocalLipAt (fun y => (f y,g y)) x := by
  obtain ⟨K,t,ht,hK⟩ := hf
  obtain ⟨L,u,hu,hL⟩ := hg
  exact ⟨max K L,t∩u,inter_mem ht hu,(hK.mono inter_subset_left).prodMk (hL.mono inter_subset_right)⟩

lemma LocalLipAt.congr {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {f g : E → F} {x : E} (hf : LocalLipAt f x) (hfg : f=ᶠ[𝓝 x]g) : LocalLipAt g x := by
  obtain ⟨K,t,ht,hK⟩ := hf
  refine ⟨K,t∩{y | f y=g y},inter_mem ht hfg,?_⟩
  intro y hy z hz
  have hyy : f y=g y := hy.2
  have hzz : f z=g z := hz.2
  simpa only [←hyy,←hzz] using hK hy.1 hz.1

lemma localLipAt_of_contDiffAt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E}
    (h : ContDiffAt ℝ 1 f x) : LocalLipAt f x := h.exists_lipschitzOnWith

lemma localLipschitz_abs : LipschitzWith 1 (fun r : ℝ => |r|) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_one,one_mul,Real.dist_eq] using abs_abs_sub_abs_le_abs_sub x y

lemma locallyLipschitz_sourceRadial : LocallyLipschitz sourceRadial := by
  have h0 : LocallyLipschitz (fun y : Fin 3 → ℝ => |y 0|/sourceLength) :=
    (show ContDiff ℝ 1 (fun r : ℝ => r/sourceLength) by fun_prop).locallyLipschitz.comp
      (localLipschitz_abs.locallyLipschitz.comp (LipschitzWith.eval 0).locallyLipschitz)
  exact h0.max (localLipschitz_abs.locallyLipschitz.comp (LipschitzWith.eval 1).locallyLipschitz)

lemma locallyLipschitz_sourceCollarTime : LocallyLipschitz sourceCollarTime := by
  have h0 : LocallyLipschitz (fun y : Fin 3 → ℝ => |(sourceRadial y-sourceRadialCenter)/sourceRadialWidth|) :=
    localLipschitz_abs.locallyLipschitz.comp
      ((show ContDiff ℝ 1 (fun r : ℝ => (r-sourceRadialCenter)/sourceRadialWidth) by fun_prop).locallyLipschitz.comp
        locallyLipschitz_sourceRadial)
  exact (show ContDiff ℝ 1 (fun r : ℝ => 1-r) by fun_prop).locallyLipschitz.comp
    (h0.max (localLipschitz_abs.locallyLipschitz.comp (LipschitzWith.eval 2).locallyLipschitz))

lemma locallyLipschitz_sourceDirection (j : Fin 2) :
    LocallyLipschitz (fun y => sourceComplexDirections y j) := by
  fin_cases j
  · have h0 : ContDiff ℝ 1 (fun y : Fin 3 → ℝ => y 0/sourceLength) := by fun_prop
    have h1 : ContDiff ℝ 1 (fun y : Fin 3 → ℝ => y 1) := by fun_prop
    have hc : ContDiff ℝ 1 (fun y : Fin 3 → ℝ => ((y 0/sourceLength:ℝ):ℂ)+Complex.I*(y 1:ℂ)) :=
      (Complex.ofRealCLM.contDiff.comp h0).add (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h1))
    exact hc.locallyLipschitz
  · have h0 : ContDiff ℝ 1 (fun p : ℝ×ℝ => p.1-sourceRadialCenter) := by fun_prop
    have h1 : ContDiff ℝ 1 (fun p : ℝ×ℝ => p.2) := by fun_prop
    have hc : ContDiff ℝ 1 (fun p : ℝ×ℝ => ((p.1-sourceRadialCenter:ℝ):ℂ)+Complex.I*(p.2:ℂ)) :=
      (Complex.ofRealCLM.contDiff.comp h0).add (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h1))
    have hpr : LocallyLipschitz (fun y : Fin 3 → ℝ => (sourceRadial y,y 2)) :=
      locallyLipschitz_sourceRadial.prodMk (LipschitzWith.eval 2).locallyLipschitz
    convert! hc.locallyLipschitz.comp hpr using 1

def localComplexArg (z₀ z : ℂ) : ℝ := (z/z₀).arg+z₀.arg

lemma localComplexArg_contDiffAt {z : ℂ} (hz : z≠0) :
    ContDiffAt ℝ 1 (localComplexArg z) z := by
  have hd : ContDiffAt ℝ 1 (fun w : ℂ => w/z) z := by fun_prop
  have hlog : ContDiffAt ℝ 1 Complex.log (z/z) :=
    (Complex.contDiffAt_log (by simpa only [div_self hz] using Complex.one_mem_slitPlane)).restrict_scalars ℝ
  have hi := Complex.imCLM.contDiff.contDiffAt.comp z (hlog.comp (f:=fun w : ℂ => w/z) z hd)
  change ContDiffAt ℝ 1 (fun w : ℂ => (w/z).arg+z.arg) z
  simpa only [Function.comp_apply,Complex.imCLM_apply,Complex.log_im] using hi.add contDiffAt_const

lemma localComplexArg_unitAngle {z₀ z : ℂ} (h₀ : z₀≠0) (hz : z≠0) :
    ((localComplexArg z₀ z/(2*Real.pi):ℝ):UnitAddCircle)=complexUnitAngle z := by
  have ha := Complex.arg_div_coe_angle hz h₀
  change (((z/z₀).arg:ℝ):AddCircle (2*Real.pi)) =
    ((z.arg:ℝ):AddCircle (2*Real.pi))-((z₀.arg:ℝ):AddCircle (2*Real.pi)) at ha
  have hh := congrArg (AddCircle.equivAddCircle (2*Real.pi) (1:ℝ)
    (by positivity) one_ne_zero) ha
  rw [map_sub,AddCircle.equivAddCircle_apply_mk,AddCircle.equivAddCircle_apply_mk,
    AddCircle.equivAddCircle_apply_mk] at hh
  simp only [mul_one,←div_eq_mul_inv] at hh
  unfold localComplexArg complexUnitAngle
  rw [add_div,AddCircle.coe_add,hh]
  abel

lemma physicalEndPoissonField_eq_continuation (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {y : Fin 3 → ℝ} (hy : 0<sourceCollarTime y)
    {x : Fin 3 → ℝ} (hx : x 0=sourceCollarTime y) (hθ : torusAngles x=sourcePhysicalAngles y) :
    (physicalEndPoissonField s f 0 y).re=
      torusRealContinuation s ((mFourierBasis (d:=Fin 2)).repr.symm (f.val 0)) x := by
  unfold torusRealContinuation
  rw [hx,hθ,torusPoissonContinuous_apply hs hy]
  unfold physicalEndPoissonField endPoissonField
  apply congrArg Complex.re
  apply tsum_congr
  intro h
  have hc : mFourierCoeff (((mFourierBasis (d:=Fin 2)).repr.symm (f.val 0)):TorusL2) h=f.val 0 h := by
    rw [←mFourierBasis_repr,LinearIsometryEquiv.apply_symm_apply]
  simp only [sourcePhysicalCoordinates,endPoissonModeField,endModeCoefficient,hc,Matrix.cons_val_zero]

def sourceLocalFlat (x y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![sourceCollarTime y,localComplexArg (sourceComplexDirections x 0) (sourceComplexDirections y 0),
    localComplexArg (sourceComplexDirections x 1) (sourceComplexDirections y 1)]

lemma sourceLocalFlat_localLip {x : Fin 3 → ℝ} (hx : ∀ i,sourceComplexDirections x i≠0) :
    LocalLipAt (sourceLocalFlat x) x := by
  have ha (i : Fin 2) : LocalLipAt (fun y => localComplexArg (sourceComplexDirections x i) (sourceComplexDirections y i)) x :=
    (localLipAt_of_contDiffAt (localComplexArg_contDiffAt (hx i))).comp
      (f:=fun y => sourceComplexDirections y i) (locallyLipschitz_sourceDirection i x)
  have hv : ContDiff ℝ 1 (fun p : ℝ×(ℝ×ℝ) => ![p.1,p.2.1,p.2.2]) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ 1 (fun p : ℝ×(ℝ×ℝ) => p.1); fun_prop
    · change ContDiff ℝ 1 (fun p : ℝ×(ℝ×ℝ) => p.2.1); fun_prop
    · change ContDiff ℝ 1 (fun p : ℝ×(ℝ×ℝ) => p.2.2); fun_prop
  have hp : LocalLipAt (fun y : Fin 3 → ℝ => (sourceCollarTime y,
      (localComplexArg (sourceComplexDirections x 0) (sourceComplexDirections y 0),
       localComplexArg (sourceComplexDirections x 1) (sourceComplexDirections y 1)))) x :=
    (show LocalLipAt sourceCollarTime x from locallyLipschitz_sourceCollarTime x).prodMk ((ha 0).prodMk (ha 1))
  convert! (localLipAt_of_contDiffAt hv.contDiffAt).comp (f:=fun y : Fin 3 → ℝ =>
    (sourceCollarTime y,(localComplexArg (sourceComplexDirections x 0) (sourceComplexDirections y 0),
      localComplexArg (sourceComplexDirections x 1) (sourceComplexDirections y 1)))) hp using 1

lemma sourceLocalFlat_angles {x y : Fin 3 → ℝ}
    (hx : ∀ i,sourceComplexDirections x i≠0) (hy : ∀ i,sourceComplexDirections y i≠0) :
    torusAngles (sourceLocalFlat x y)=sourcePhysicalAngles y := by
  funext i
  fin_cases i <;> simp only [torusAngles,sourceLocalFlat,sourcePhysicalAngles,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  · exact localComplexArg_unitAngle (hx 0) (hy 0)
  · exact localComplexArg_unitAngle (hx 1) (hy 1)

theorem physicalEndPoissonField_localLip (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {x : Fin 3 → ℝ}
    (ht : 0<sourceCollarTime x) (hx : ∀ i,sourceComplexDirections x i≠0) :
    LocalLipAt (fun y => (physicalEndPoissonField s f 0 y).re) x := by
  have hflat := sourceLocalFlat_localLip hx
  have hc := (torusRealContinuation_smooth hs ((mFourierBasis (d:=Fin 2)).repr.symm (f.val 0))).of_le
    (show (1:WithTop ℕ∞)≤↑(⊤:ℕ∞) by simp)
  have hc' := hc.contDiffAt ((axial_halfspace_open 0).mem_nhds (show 0<(sourceLocalFlat x x) 0 from ht))
  apply ((localLipAt_of_contDiffAt hc').comp hflat).congr
  have htime : ∀ᶠ y in 𝓝 x,0<sourceCollarTime y :=
    (locallyLipschitz_sourceCollarTime.continuous).continuousAt (Ioi_mem_nhds ht)
  have hdirs : ∀ᶠ y in 𝓝 x,∀ i,sourceComplexDirections y i≠0 := by
    rw [eventually_all]
    intro i
    exact (locallyLipschitz_sourceDirection i).continuous.continuousAt
      (isOpen_ne.mem_nhds (hx i))
  filter_upwards [htime,hdirs] with y hyt hyd
  exact (physicalEndPoissonField_eq_continuation s hs f hyt rfl (sourceLocalFlat_angles hx hyd)).symm

end ScalarConductivity

end

end OAI
