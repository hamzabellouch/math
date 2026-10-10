import Mathlib
import OAI.Geometry.BallPacking.Necessity.MarkedProfiles

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance localChartsInst1 (α : ℝ) : NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance localChartsInst2 (α : ℝ) : NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance localChartsInst3 (α : ℝ) : NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance localChartsInst4 (α : ℝ) : NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance localChartsInst5 (R : ℝ) : NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance localChartsInst6 (R : ℝ) : NormedSpace ℝ (CompactHolderSpace E R) := inferInstance
local instance localChartsInst7 (α : ℝ) : NormedAddCommGroup ((E × (ℂ →L[ℝ] E)) × C1HolderSpace E α) := inferInstance
local instance localChartsInst8 (α : ℝ) : NormedSpace ℝ ((E × (ℂ →L[ℝ] E)) × C1HolderSpace E α) := inferInstance
local instance localChartsInst9 (α : ℝ) : AddCommGroup ((E × (ℂ →L[ℝ] E)) × C1HolderSpace E α) :=
  (inferInstance : NormedAddCommGroup ((E × (ℂ →L[ℝ] E)) × C1HolderSpace E α)).toAddCommGroup

 
def affineC1Value (α : ℝ) (z : ℂ) :
    (E × (ℂ →L[ℝ] E)) × C1HolderSpace E α →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ E (ℂ →L[ℝ] E)).comp (ContinuousLinearMap.fst ℝ _ _) +
  ((ContinuousLinearMap.apply ℝ E z).comp (ContinuousLinearMap.snd ℝ E (ℂ →L[ℝ] E))).comp
    (ContinuousLinearMap.fst ℝ _ _) +
  (c1HolderEval α z).comp (ContinuousLinearMap.snd ℝ _ _)

@[simp] theorem affineC1Value_apply (α : ℝ) (z : ℂ)
    (p : (E × (ℂ →L[ℝ] E)) × C1HolderSpace E α) :
    affineC1Value α z p = c1HolderAffineCurve α p.1.1 p.1.2 p.2 z := rfl

 
def affineC1Deriv (α : ℝ) (z : ℂ) :
    (E × (ℂ →L[ℝ] E)) × C1HolderSpace E α →L[ℝ] (ℂ →L[ℝ] E) :=
  (ContinuousLinearMap.snd ℝ E (ℂ →L[ℝ] E)).comp (ContinuousLinearMap.fst ℝ _ _) +
  ((BoundedContinuousFunction.evalCLM ℝ z).comp ((holderValue α).comp (c1HolderDeriv α))).comp
    (ContinuousLinearMap.snd ℝ _ _)

@[simp] theorem affineC1Deriv_apply (α : ℝ) (z : ℂ)
    (p : (E × (ℂ →L[ℝ] E)) × C1HolderSpace E α) :
    affineC1Deriv α z p = fderiv ℝ (c1HolderAffineCurve α p.1.1 p.1.2 p.2) z := by
  rw [c1HolderAffineCurve_fderiv]; rfl

 
theorem c1HolderCRFamily_fderiv (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (J : E → E →L[ℝ] E) (J₀ : E →L[ℝ] E) (hJ : ContDiff ℝ ∞ J)
    (hc : HasCompactSupport (fun x => J x-J₀))
    (p h : (E × (ℂ →L[ℝ] E)) × C1HolderSpace E α)
    (m : ℝ) (hm : 0 < m) (hA : ∀ z, m*‖z‖≤‖p.1.2 z‖) (z : ℂ) :
    holderValue α (fderiv ℝ (c1HolderCRFamily α hα₀ hα₁ J J₀ hJ hc) p h) z =
      linearizedCR J (c1HolderAffineCurve α p.1.1 p.1.2 p.2)
        (c1HolderAffineCurve α h.1.1 h.1.2 h.2) z := by
  let : ContinuousSMul ℝ ((E × (ℂ →L[ℝ] E)) × C1HolderSpace E α) :=
    IsBoundedSMul.continuousSMul
  let ev := affineC1Value (E := E) α z
  let dev := affineC1Deriv (E := E) α z
  have hdJ := ((hJ.differentiable (by simp)) (ev p)).hasFDerivAt.comp p ev.hasFDerivAt
  have hdI := dev.hasFDerivAt.clm_apply (hasFDerivAt_const Complex.I p)
  have hd1 := dev.hasFDerivAt.clm_apply (hasFDerivAt_const (1:ℂ) p)
  have hd := hdI.sub (hdJ.clm_apply hd1)
  let hev : HolderSpace ℂ E α →L[ℝ] E :=
    (BoundedContinuousFunction.evalCLM ℝ z).comp (holderValue α)
  have hout := hev.hasFDerivAt.comp p
    ((c1HolderCRFamily_contDiffAt α hα₀ hα₁ J J₀ hJ hc p m hm hA).differentiableAt
      (by simp)).hasFDerivAt
  have heq : (fun q => hev (c1HolderCRFamily α hα₀ hα₁ J J₀ hJ hc q)) =
      (fun q => dev q Complex.I-J (ev q) (dev q 1)) := by
    funext q
    simpa only [hev,ev,dev,ContinuousLinearMap.comp_apply,
      BoundedContinuousFunction.evalCLM_apply,c1HolderCRFamily,affineC1Value_apply,affineC1Deriv_apply]
      using c1HolderCR_apply α hα₀ hα₁ J J₀ hJ hc q.1.1 q.1.2 q.2 z
  change HasFDerivAt (fun q => hev (c1HolderCRFamily α hα₀ hα₁ J J₀ hJ hc q)) _ p at hout
  rw [heq] at hout
  have he := congrArg (fun L => L h) (hout.unique hd)
  simp only [hev,ev,dev,ContinuousLinearMap.comp_apply,BoundedContinuousFunction.evalCLM_apply,
    sub_apply,add_apply,ContinuousLinearMap.flip_apply,zero_apply,map_zero,zero_add,
    Function.comp_def,affineC1Value_apply,affineC1Deriv_apply] at he
  exact he.trans (by unfold linearizedCR; abel)

 
def markedFramedCR (R : ℝ) (Ainf : E →L[ℝ] E) (P : ℂ → E →L[ℝ] E)
    (hP : ContDiff ℝ ∞ P) (hPc : HasCompactSupport P)
    (J : E → E →L[ℝ] E) (J₀ : E →L[ℝ] E) (hJ : ContDiff ℝ ∞ J)
    (hJc : HasCompactSupport (fun x => J x-J₀))
    (p : (E × (ℂ →L[ℝ] E)) × C1HolderSpace E ((1:ℝ)/3))
    (g : CompactHolderSpace E R) : HolderSpace ℂ E ((1:ℝ)/3) :=
  c1HolderCRFamily ((1:ℝ)/3) (by norm_num) (by norm_num) J J₀ hJ hJc
    (p+markedFramedProfile R Ainf P hP hPc g)

theorem markedFramedCR_contDiffAt_zero (R : ℝ) (Ainf : E →L[ℝ] E) (P : ℂ → E →L[ℝ] E)
    (hP : ContDiff ℝ ∞ P) (hPc : HasCompactSupport P)
    (J : E → E →L[ℝ] E) (J₀ : E →L[ℝ] E) (hJ : ContDiff ℝ ∞ J)
    (hJc : HasCompactSupport (fun x => J x-J₀))
    (p : (E × (ℂ →L[ℝ] E)) × C1HolderSpace E ((1:ℝ)/3))
    (m : ℝ) (hm : 0 < m) (hA : ∀ z, m*‖z‖≤‖p.1.2 z‖) :
    ContDiffAt ℝ ∞ (markedFramedCR R Ainf P hP hPc J J₀ hJ hJc p) 0 := by
  have hs := c1HolderCRFamily_contDiffAt ((1:ℝ)/3) (by norm_num) (by norm_num)
    J J₀ hJ hJc p m hm hA
  have ht : ContDiffAt ℝ ∞ (fun g => p+markedFramedProfile R Ainf P hP hPc g)
      (0:CompactHolderSpace E R) :=
    (contDiff_const.add (markedFramedProfile R Ainf P hP hPc).contDiff).contDiffAt
  apply hs.comp_of_eq 0 ht
  · exact mapsTo_univ _ _
  · rw [(markedFramedProfile R Ainf P hP hPc).map_zero,add_zero]

lemma affineC1Curve_profile (R : ℝ) (Ainf : E →L[ℝ] E) (P : ℂ → E →L[ℝ] E)
    (hP : ContDiff ℝ ∞ P) (hPc : HasCompactSupport P) (g : CompactHolderSpace E R) :
    let h := markedFramedProfile R Ainf P hP hPc g
    c1HolderAffineCurve ((1:ℝ)/3) h.1.1 h.1.2 h.2 = fun z => (Ainf+P z) (markedCRInverse R g z) := by
  funext z
  exact markedFramedProfile_value R Ainf P hP hPc g z

 

theorem markedFramedCR_fderiv_zero (R : ℝ) (Ainf : E →L[ℝ] E) (P : ℂ → E →L[ℝ] E)
    (hP : ContDiff ℝ ∞ P) (hPc : HasCompactSupport P)
    (J : E → E →L[ℝ] E) (J₀ : E →L[ℝ] E) (hJ : ContDiff ℝ ∞ J)
    (hJc : HasCompactSupport (fun x => J x-J₀))
    (p : (E × (ℂ →L[ℝ] E)) × C1HolderSpace E ((1:ℝ)/3))
    (m : ℝ) (hm : 0 < m) (hA : ∀ z, m*‖z‖≤‖p.1.2 z‖)
    (g : CompactHolderSpace E R) (z : ℂ) :
    holderValue ((1:ℝ)/3) (fderiv ℝ (markedFramedCR R Ainf P hP hPc J J₀ hJ hJc p) 0 g) z =
      linearizedCR J (c1HolderAffineCurve ((1:ℝ)/3) p.1.1 p.1.2 p.2)
        (fun w => (Ainf+P w) (markedCRInverse R g w)) z := by
  let F := markedFramedProfile R Ainf P hP hPc
  have hs := (c1HolderCRFamily_contDiffAt ((1:ℝ)/3) (by norm_num) (by norm_num)
    J J₀ hJ hJc p m hm hA).differentiableAt (by simp)
  have ht : HasFDerivAt (fun v => p+F v) F (0:CompactHolderSpace E R) := F.hasFDerivAt.const_add p
  have hs' : HasFDerivAt (c1HolderCRFamily ((1:ℝ)/3) (by norm_num) (by norm_num) J J₀ hJ hJc)
      (fderiv ℝ (c1HolderCRFamily ((1:ℝ)/3) (by norm_num) (by norm_num) J J₀ hJ hJc) p) (p+F 0) := by
    rw [F.map_zero,add_zero]
    exact hs.hasFDerivAt
  have hd := hs'.comp 0 ht
  change HasFDerivAt (markedFramedCR R Ainf P hP hPc J J₀ hJ hJc p) _ 0 at hd
  rw [hd.fderiv,ContinuousLinearMap.comp_apply]
  rw [c1HolderCRFamily_fderiv _ _ _ _ _ _ _ _ _ m hm hA]
  rw [affineC1Curve_profile]

end HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
local instance localChartsInst10 (α : ℝ) : NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance localChartsInst11 (α : ℝ) : NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance localChartsInst12 (α : ℝ) : NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance localChartsInst13 (α : ℝ) : NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance localChartsInst14 (R : ℝ) : NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance localChartsInst15 (R : ℝ) : NormedSpace ℝ (CompactHolderSpace E R) := inferInstance
local instance localChartsInst16 (α : ℝ) : NormedAddCommGroup ((E × (ℂ →L[ℝ] E)) × C1HolderSpace E α) := inferInstance
local instance localChartsInst17 (α : ℝ) : NormedSpace ℝ ((E × (ℂ →L[ℝ] E)) × C1HolderSpace E α) := inferInstance
local instance localChartsInst18 (α : ℝ) : AddCommGroup ((E × (ℂ →L[ℝ] E)) × C1HolderSpace E α) :=
  (inferInstance : NormedAddCommGroup ((E × (ℂ →L[ℝ] E)) × C1HolderSpace E α)).toAddCommGroup

 

omit [FiniteDimensional ℂ E] in
theorem affineC1_uniform_exterior (J : E → E →L[ℝ] E) (B : E →L[ℝ] E)
    (hc : HasCompactSupport (fun x => J x-B))
    (p : (E × (ℂ →L[ℝ] E)) × C1HolderSpace E ((1:ℝ)/3))
    (m : ℝ) (hm : 0 < m) (hA : ∀ z, m*‖z‖ ≤ ‖p.1.2 z‖) :
    ∃ S : ℝ, 0 < S ∧ ∀ q : (E × (ℂ →L[ℝ] E)) × C1HolderSpace E ((1:ℝ)/3),
      ‖q-p‖ < min 1 (m/2) → ∀ z : ℂ, S < ‖z‖ →
        J (c1HolderAffineCurve ((1:ℝ)/3) q.1.1 q.1.2 q.2 z)=B := by
  obtain ⟨T,hT,hJT⟩ := compactCoefficient_zero_outside hc
  let U := ‖p.2‖+1
  let S := max 1 (2*(T+‖p.1.1‖+1+U)/m)
  have hS : 0 < S := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨S,hS,?_⟩
  intro q hq z hz
  have hqp₁ : ‖q.1-p.1‖ < min 1 (m/2) := lt_of_le_of_lt (norm_fst_le (q-p)) hq
  have hd : ‖q.1.1-p.1.1‖ ≤ 1 :=
    ((norm_fst_le (q.1-p.1)).trans hqp₁.le).trans (min_le_left _ _)
  have hB : ‖q.1.2-p.1.2‖ ≤ m/2 :=
    ((norm_snd_le (q.1-p.1)).trans hqp₁.le).trans (min_le_right _ _)
  have hq₂ : ‖q.2-p.2‖ ≤ 1 :=
    ((norm_snd_le (q-p)).trans hq.le).trans (min_le_left _ _)
  have hqU : ‖q.2‖ ≤ U := by
    have hh : ‖q.2‖ ≤ ‖q.2-p.2‖+‖p.2‖ := norm_le_norm_sub_add _ _
    change ‖q.2‖ ≤ ‖p.2‖+1
    linarith only [hh,hq₂]
  have hv := (c1HolderValue_bound ((1:ℝ)/3) q.2 z).trans hqU
  have hzS : T+‖p.1.1‖+1+U  ≤  m/2*‖z‖ := by
    have hh := (le_max_right 1 (2*(T+‖p.1.1‖+1+U)/m)).trans hz.le
    have hh' := (div_le_iff₀ hm).mp hh
    linarith
  have he := affineProfile_lower_bound p.1.1 (q.1.1-p.1.1)
    (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) q.2) z)
    p.1.2 (q.1.2-p.1.2) m U T 1 hm hA hd hB hv ⟨zero_le_one,le_rfl⟩ z hzS
  have he' : T ≤ ‖c1HolderAffineCurve ((1:ℝ)/3) q.1.1 q.1.2 q.2 z‖ := by
    convert he using 1
    rw [one_smul,sub_apply]
    congr 1
    unfold c1HolderAffineCurve
    abel
  exact sub_eq_zero.mp (hJT _ he')

omit [FiniteDimensional ℂ E] in
lemma affineC1Curve_add (α : ℝ)
    (p q : (E × (ℂ →L[ℝ] E)) × C1HolderSpace E α) :
    c1HolderAffineCurve α (p+q).1.1 (p+q).1.2 (p+q).2 =
      fun z => c1HolderAffineCurve α p.1.1 p.1.2 p.2 z+
        c1HolderAffineCurve α q.1.1 q.1.2 q.2 z := by
  funext z
  exact (affineC1Value α z).map_add p q

 

omit [FiniteDimensional ℂ E] in
lemma framed_variation_exterior_cr (R : ℝ) (Ainf : E →L[ℝ] E)
    (hAinf : ∀ v, Ainf (Complex.I • v)=Complex.I • Ainf v)
    (P : ℂ → E →L[ℝ] E) (_hP : ContDiff ℝ ∞ P)
    (_hc : HasCompactSupport P) (hPR : ∀ z : ℂ, R < ‖z‖ → P z=0)
    (g : CompactHolderSpace E R) (z : ℂ) (hz : R < ‖z‖) :
    crOperator (fun _ => (ContinuousLinearMap.lsmul ℝ ℂ) Complex.I)
      (fun w => (Ainf+P w) (markedCRInverse R g w)) z=0 := by
  have hp : ∀ᶠ w in 𝓝 z, P w=0 := by
    filter_upwards [((isOpen_lt continuous_const continuous_norm).mem_nhds hz)] with w hw
    exact hPR w hw
  have he : (fun w => (Ainf+P w) (markedCRInverse R g w)) =ᶠ[𝓝 z]
      fun w => Ainf (markedCRInverse R g w) := by
    filter_upwards [hp] with w hw
    rw [hw,add_zero]
  have hd := Ainf.hasFDerivAt.comp z (markedCRInverse_differentiable R g z).hasFDerivAt
  change HasFDerivAt (fun w => Ainf (markedCRInverse R g w)) _ z at hd
  unfold crOperator
  rw [he.fderiv_eq,hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.lsmul_apply]
  rw [← hAinf,← map_sub,markedCRInverse_rightInverse]
  change Ainf (holderValue ((1:ℝ)/3) g.val z)=0
  rw [g.property z hz,map_zero]

 

omit [FiniteDimensional ℂ E] in
theorem markedFramedCR_eventually_compact (Ainf : E →L[ℝ] E)
    (hAinf : ∀ v, Ainf (Complex.I • v)=Complex.I • Ainf v)
    (P : ℂ → E →L[ℝ] E) (hP : ContDiff ℝ ∞ P) (hPc : HasCompactSupport P)
    (J : E → E →L[ℝ] E) (hJ : ContDiff ℝ ∞ J)
    (hc : HasCompactSupport (fun x => J x-(ContinuousLinearMap.lsmul ℝ ℂ) Complex.I))
    (p : (E × (ℂ →L[ℝ] E)) × C1HolderSpace E ((1:ℝ)/3))
    (m : ℝ) (hm : 0 < m) (hA : ∀ z, m*‖z‖ ≤ ‖p.1.2 z‖)
    (hsol : ∀ z, crOperator J (c1HolderAffineCurve ((1:ℝ)/3) p.1.1 p.1.2 p.2) z=0) :
    ∃ S : ℝ, 0 < S ∧ ∀ R : ℝ, S ≤ R →
      ∀ᶠ g : CompactHolderSpace E R in 𝓝 0,
        markedFramedCR R Ainf P hP hPc J ((ContinuousLinearMap.lsmul ℝ ℂ) Complex.I) hJ hc p g
          ∈ compactHolderSubmodule R := by
  let B : E →L[ℝ] E := (ContinuousLinearMap.lsmul ℝ ℂ) Complex.I
  obtain ⟨S₀,hS₀,hJS⟩ := affineC1_uniform_exterior J B hc p m hm hA
  obtain ⟨S₁,hS₁,hPS⟩ := compactCoefficient_zero_outside hPc
  let S := max S₀ S₁
  refine ⟨S,lt_of_lt_of_le hS₀ (le_max_left _ _),?_⟩
  intro R hR
  let F := markedFramedProfile R Ainf P hP hPc
  have hsmall : ∀ᶠ g : CompactHolderSpace E R in 𝓝 0, ‖F g‖ < min 1 (m/2) := by
    have ht := (F.continuous.continuousAt (x := 0)).tendsto
    have hm' : (0:ℝ) < min 1 (m/2) := lt_min zero_lt_one (by linarith)
    have hh : {q | ‖q‖ < min 1 (m/2)} ∈ 𝓝 (F 0) := by
      rw [F.map_zero]
      simpa only [Metric.ball,dist_zero_right] using Metric.ball_mem_nhds (0 : (E × (ℂ →L[ℝ] E)) × C1HolderSpace E ((1:ℝ)/3)) hm'
    exact ht.eventually hh
  filter_upwards [hsmall] with g hg
  intro z hz
  let u := c1HolderAffineCurve ((1:ℝ)/3) p.1.1 p.1.2 p.2
  let v := fun w => (Ainf+P w) (markedCRInverse R g w)
  have hPR : ∀ w : ℂ, R < ‖w‖ → P w=0 := fun w hw =>
    hPS w (((le_max_right _ _).trans hR).trans hw.le)
  have hJq : J (u z+v z)=B := by
    have hh := hJS (p+F g) (by simpa only [add_sub_cancel_left] using hg) z
      (lt_of_le_of_lt ((le_max_left _ _).trans hR) hz)
    rw [affineC1Curve_add,affineC1Curve_profile] at hh
    exact hh
  have hJp : J (u z)=B := hJS p (by simpa only [sub_self,norm_zero] using lt_min zero_lt_one (show (0:ℝ) < m/2 by linarith)) z
    (lt_of_le_of_lt ((le_max_left _ _).trans hR) hz)
  have hdu := (c1HolderAffineCurve_hasFDerivAt ((1:ℝ)/3) p.1.1 p.1.2 p.2 z).differentiableAt
  have hdv : DifferentiableAt ℝ v z :=
    ((contDiff_const.add hP).differentiable (by simp) z).clm_apply
      (markedCRInverse_differentiable R g z)
  have hv := framed_variation_exterior_cr R Ainf hAinf P hP hPc hPR g z hz
  have hu := hsol z
  change crOperator J u z=0 at hu
  unfold crOperator at hu hv
  rw [hJp] at hu
  change holderValue ((1:ℝ)/3) (c1HolderCRFamily _ _ _ _ _ _ _ (p+F g)) z=0
  rw [c1HolderCRFamily,c1HolderCR_apply,affineC1Curve_add,affineC1Curve_profile]
  change fderiv ℝ (fun w => u w+v w) z Complex.I-
    J (u z+v z) (fderiv ℝ (fun w => u w+v w) z 1)=0
  rw [fderiv_fun_add hdu hdv,hJq]
  simp only [add_apply,map_add]
  change fderiv ℝ v z Complex.I-B (fderiv ℝ v z 1)=0 at hv
  rw [sub_eq_zero] at hu hv ⊢
  rw [hu,hv]

end HigherDimensionalBallPacking.Rigidity

 

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
universe u
variable {X Y Z : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma linearIsometry_fderiv_mem (e : Y →ₗᵢ[ℝ] Z) (f : X → Y) (x v : X) :
    fderiv ℝ (e ∘ f) x v ∈ e.toLinearMap.range := by
  let S := e.toLinearMap.range
  let : IsClosed (S : Set Z) := e.isometry.isClosedEmbedding.isClosed_range
  by_cases hd : DifferentiableAt ℝ (e ∘ f) x
  · have he : (fun y => S.mkQL (e (f y))) = fun _ : X => (0 : Z ⧸ S) := by
      funext y
      exact (Submodule.Quotient.mk_eq_zero S).mpr ⟨f y,rfl⟩
    have hh := S.mkQL.hasFDerivAt.comp x hd.hasFDerivAt
    change HasFDerivAt (fun y => S.mkQL (e (f y))) _ x at hh
    rw [he] at hh
    have hv := congrArg (fun L : X →L[ℝ] (Z ⧸ S) => L v)
      (hh.unique (hasFDerivAt_const (0 : Z ⧸ S) x))
    exact (Submodule.Quotient.mk_eq_zero S).mp hv
  · rw [fderiv_zero_of_not_differentiableAt hd]
    exact S.zero_mem

 
def reflectedFDeriv (e : Y →ₗᵢ[ℝ] Z) (f : X → Y) (x : X) : X →L[ℝ] Y :=
  e.equivRange.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((fderiv ℝ (e ∘ f) x).codRestrict e.toLinearMap.range
      (linearIsometry_fderiv_mem e f x))

lemma reflectedFDeriv_comp (e : Y →ₗᵢ[ℝ] Z) (f : X → Y) (x : X) :
    e.toContinuousLinearMap.comp (reflectedFDeriv e f x) = fderiv ℝ (e ∘ f) x := by
  ext v
  exact congrArg Subtype.val (e.equivRange.apply_symm_apply
    ⟨fderiv ℝ (e ∘ f) x v,linearIsometry_fderiv_mem e f x v⟩)

lemma hasFDerivAt_reflected (e : Y →ₗᵢ[ℝ] Z) (f : X → Y) (x : X)
    (hd : DifferentiableAt ℝ (e ∘ f) x) :
    HasFDerivAt f (reflectedFDeriv e f x) x := by
  have hh := hd.hasFDerivAt
  rw [← reflectedFDeriv_comp e f x] at hh
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hh ⊢
  rw [← Asymptotics.isLittleO_norm_left] at hh ⊢
  simpa only [Function.comp_apply,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,← map_sub,e.norm_map] using hh

lemma fderiv_comp_linearIsometry (e : Y →ₗᵢ[ℝ] Z) (f : X → Y) (x : X) :
    e.toContinuousLinearMap.comp (fderiv ℝ f x) = fderiv ℝ (e ∘ f) x := by
  by_cases hd : DifferentiableAt ℝ (e ∘ f) x
  · rw [(hasFDerivAt_reflected e f x hd).fderiv]
    exact reflectedFDeriv_comp e f x
  · have hdf : ¬ DifferentiableAt ℝ f x := by
      intro hf
      exact hd (e.toContinuousLinearMap.differentiableAt.comp x hf)
    rw [fderiv_zero_of_not_differentiableAt hd,fderiv_zero_of_not_differentiableAt hdf]
    simp

 
theorem contDiffAt_reflect_isometry_nat (m : ℕ) (e : Y →ₗᵢ[ℝ] Z) (f : X → Y) (x : X)
    (hf : ContDiffAt ℝ m (e ∘ f) x) : ContDiffAt ℝ m f x := by
  induction m generalizing Y Z with
  | zero =>
    obtain ⟨U,hU,hc⟩ := contDiffAt_zero.mp hf
    apply contDiffAt_zero.mpr
    refine ⟨U,hU,?_⟩
    intro y hy
    exact e.isEmbedding.isInducing.continuousWithinAt_iff.mpr (hc y hy)
  | succ m ih =>
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    refine ⟨fderiv ℝ f,?_,?_⟩
    · have hlocal := hf.eventually (by simp)
      refine ⟨{y | ContDiffAt ℝ ((m+1 : ℕ) : ℕ∞ω) (e ∘ f) y},hlocal,?_⟩
      intro y hy
      change ContDiffAt ℝ ((m+1 : ℕ) : ℕ∞ω) (e ∘ f) y at hy
      have hd := (hasFDerivAt_reflected e f y (hy.differentiableAt (by simp)))
      rw [hd.fderiv]
      exact hd
    · let ep : (X →L[ℝ] Y) →ₗᵢ[ℝ] (X →L[ℝ] Z) := e.postcomp
      apply ih ep (fderiv ℝ f)
      have he : ep ∘ fderiv ℝ f = fderiv ℝ (e ∘ f) := by
        funext y
        exact fderiv_comp_linearIsometry e f y
      rw [he]
      exact hf.fderiv_right (by simp)

theorem contDiffAt_reflect_isometry (e : Y →ₗᵢ[ℝ] Z) (f : X → Y) (x : X)
    (hf : ContDiffAt ℝ ∞ (e ∘ f) x) : ContDiffAt ℝ ∞ f x :=
  contDiffAt_infty.mpr (fun m => contDiffAt_reflect_isometry_nat m e f x
    (contDiffAt_infty.mp hf m))

end HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
universe u
variable {X Y : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

 

def localCodRestrict (S : Submodule ℝ Y) (f : X → Y) (x : X) : S := by
  classical
  exact if h : f x ∈ S then ⟨f x,h⟩ else 0

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace Y] in
lemma localCodRestrict_eq (S : Submodule ℝ Y) (f : X → Y) {x : X} (h : f x ∈ S) :
    (localCodRestrict S f x : Y)=f x := by
  simp only [localCodRestrict,dite_eq_left h]

omit [NormedSpace ℝ X] [CompleteSpace Y] in
lemma localCodRestrict_eventually (S : Submodule ℝ Y) (f : X → Y) {x : X}
    (h : ∀ᶠ y in 𝓝 x, f y ∈ S) :
    (fun y => (localCodRestrict S f y : Y)) =ᶠ[𝓝 x] f := by
  filter_upwards [h] with y hy
  exact localCodRestrict_eq S f hy

def submoduleInclusionIsometry (S : Submodule ℝ Y) : S →ₗᵢ[ℝ] Y where
  toLinearMap := S.subtype
  norm_map' := fun _ => rfl

theorem localCodRestrict_contDiffAt (S : Submodule ℝ Y) [IsClosed (S : Set Y)]
    (f : X → Y) {x : X} (h : ∀ᶠ y in 𝓝 x, f y ∈ S) (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (localCodRestrict S f) x := by
  let : CompleteSpace S := IsClosed.completeSpace_coe
  apply contDiffAt_reflect_isometry (submoduleInclusionIsometry S)
  exact hf.congr_of_eventuallyEq (localCodRestrict_eventually S f h)

theorem localCodRestrict_fderiv (S : Submodule ℝ Y) [IsClosed (S : Set Y)]
    (f : X → Y) {x : X} (h : ∀ᶠ y in 𝓝 x, f y ∈ S) (v : X) :
    (fderiv ℝ (localCodRestrict S f) x v : Y)=fderiv ℝ f x v := by
  let : CompleteSpace S := IsClosed.completeSpace_coe
  have hh := congrArg (fun L : X →L[ℝ] Y => L v)
    (fderiv_comp_linearIsometry (submoduleInclusionIsometry S) (localCodRestrict S f) x)
  change (fderiv ℝ (localCodRestrict S f) x v : Y)=
    fderiv ℝ (fun y => (localCodRestrict S f y : Y)) x v at hh
  rw [(localCodRestrict_eventually S f h).fderiv_eq] at hh
  exact hh

end HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E]
local instance localChartsInst19 (α : ℝ) : NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance localChartsInst20 (α : ℝ) : NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance localChartsInst21 (α : ℝ) : NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance localChartsInst22 (α : ℝ) : NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance localChartsInst23 (R : ℝ) : NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance localChartsInst24 (R : ℝ) : NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

 
def compactMarkedCR (R : ℝ) (Ainf : E →L[ℝ] E) (P : ℂ → E →L[ℝ] E)
    (hP : ContDiff ℝ ∞ P) (hPc : HasCompactSupport P)
    (J : E → E →L[ℝ] E) (hJ : ContDiff ℝ ∞ J)
    (hc : HasCompactSupport (fun x => J x-(ContinuousLinearMap.lsmul ℝ ℂ) Complex.I))
    (p : (E × (ℂ →L[ℝ] E)) × C1HolderSpace E ((1:ℝ)/3)) :
    CompactHolderSpace E R → CompactHolderSpace E R :=
  localCodRestrict (compactHolderSubmodule R)
    (markedFramedCR R Ainf P hP hPc J ((ContinuousLinearMap.lsmul ℝ ℂ) Complex.I) hJ hc p)

 

omit [FiniteDimensional ℂ E] in
theorem compactMarkedCR_local_chart (Ainf : E →L[ℝ] E)
    (hAinf : ∀ v, Ainf (Complex.I • v)=Complex.I • Ainf v)
    (P : ℂ → E →L[ℝ] E) (hP : ContDiff ℝ ∞ P) (hPc : HasCompactSupport P)
    (J : E → E →L[ℝ] E) (hJ : ContDiff ℝ ∞ J)
    (hc : HasCompactSupport (fun x => J x-(ContinuousLinearMap.lsmul ℝ ℂ) Complex.I))
    (p : (E × (ℂ →L[ℝ] E)) × C1HolderSpace E ((1:ℝ)/3))
    (m : ℝ) (hm : 0 < m) (hA : ∀ z, m*‖z‖ ≤ ‖p.1.2 z‖)
    (hsol : ∀ z, crOperator J (c1HolderAffineCurve ((1:ℝ)/3) p.1.1 p.1.2 p.2) z=0) :
    ∃ S : ℝ, 0 < S ∧ ∀ R : ℝ, S ≤ R →
      ContDiffAt ℝ ∞ (compactMarkedCR R Ainf P hP hPc J hJ hc p) 0 ∧
      (∀ᶠ g : CompactHolderSpace E R in 𝓝 0, ∀ z,
        compactHolderValue R (compactMarkedCR R Ainf P hP hPc J hJ hc p g) z =
          crOperator J (fun w => c1HolderAffineCurve ((1:ℝ)/3) p.1.1 p.1.2 p.2 w+
            (Ainf+P w) (markedCRInverse R g w)) z) ∧
      ∀ g z, compactHolderValue R (fderiv ℝ (compactMarkedCR R Ainf P hP hPc J hJ hc p) 0 g) z =
        linearizedCR J (c1HolderAffineCurve ((1:ℝ)/3) p.1.1 p.1.2 p.2)
          (fun w => (Ainf+P w) (markedCRInverse R g w)) z := by
  obtain ⟨S,hS,hSR⟩ := markedFramedCR_eventually_compact Ainf hAinf P hP hPc J hJ hc p m hm hA hsol
  refine ⟨S,hS,?_⟩
  intro R hR
  have he := hSR R hR
  refine ⟨localCodRestrict_contDiffAt _ _ he
    (markedFramedCR_contDiffAt_zero R Ainf P hP hPc J _ hJ hc p m hm hA),?_,?_⟩
  · filter_upwards [he] with g hg
    intro z
    change holderValue ((1:ℝ)/3) (localCodRestrict _ _ g).val z=_
    rw [localCodRestrict_eq _ _ hg]
    unfold markedFramedCR
    rw [c1HolderCRFamily,c1HolderCR_apply,affineC1Curve_add,affineC1Curve_profile]
    rfl
  · intro g z
    change holderValue ((1:ℝ)/3)
      (fderiv ℝ (localCodRestrict _ _) 0 g).val z=_
    rw [localCodRestrict_fderiv _ _ he]
    exact markedFramedCR_fderiv_zero R Ainf P hP hPc J _ hJ hc p m hm hA g z

end HigherDimensionalBallPacking.Rigidity

end

end OAI
