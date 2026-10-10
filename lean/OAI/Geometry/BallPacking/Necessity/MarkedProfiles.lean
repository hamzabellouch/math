import Mathlib
import OAI.Geometry.BallPacking.Necessity.NonlinearCR

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

namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
local instance crFDerivC1NormedAddCommGroup (α : ℝ) : NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance crFDerivC1NormedSpace (α : ℝ) : NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance crFDerivHolderNormedAddCommGroup (α : ℝ) : NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance crFDerivHolderNormedSpace (α : ℝ) : NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance

 

theorem c1HolderCR_fderiv (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (J : E → E →L[ℝ] E) (J₀ : E →L[ℝ] E) (hJ : ContDiff ℝ ∞ J)
    (hc : HasCompactSupport (fun x => J x-J₀)) (c : E) (A : ℂ →L[ℝ] E)
    (u h : C1HolderSpace E α) (z : ℂ) :
    holderValue α (fderiv ℝ (c1HolderCR α hα₀ hα₁ J J₀ hJ hc c A) u h) z =
      holderValue α (c1HolderDeriv α h) z Complex.I -
      (fderiv ℝ J (c1HolderAffineCurve α c A u z) (holderValue α (c1HolderValue α h) z))
        (fderiv ℝ (c1HolderAffineCurve α c A u) z 1) -
      J (c1HolderAffineCurve α c A u z) (holderValue α (c1HolderDeriv α h) z 1) := by
  let ev : C1HolderSpace E α →L[ℝ] E :=
    (BoundedContinuousFunction.evalCLM ℝ z).comp ((holderValue α).comp (c1HolderValue α))
  let dev : C1HolderSpace E α →L[ℝ] (ℂ →L[ℝ] E) :=
    (BoundedContinuousFunction.evalCLM ℝ z).comp ((holderValue α).comp (c1HolderDeriv α))
  have hf : HasFDerivAt (fun v : C1HolderSpace E α => c1HolderAffineCurve α c A v z) ev u :=
    ev.hasFDerivAt.const_add (c+A z)
  have hs : HasFDerivAt (fun v : C1HolderSpace E α => A+holderValue α (c1HolderDeriv α v) z) dev u :=
    dev.hasFDerivAt.const_add A
  have hdJ := ((hJ.differentiable (by simp)) (c1HolderAffineCurve α c A u z)).hasFDerivAt.comp u hf
  have hdI := hs.clm_apply (hasFDerivAt_const Complex.I u)
  have hd1 := hs.clm_apply (hasFDerivAt_const (1:ℂ) u)
  have hd := hdI.sub (hdJ.clm_apply hd1)
  let hev : HolderSpace ℂ E α →L[ℝ] E :=
    (BoundedContinuousFunction.evalCLM ℝ z).comp (holderValue α)
  have hout := hev.hasFDerivAt.comp u
    (((c1HolderCR_contDiff α hα₀ hα₁ J J₀ hJ hc c A).differentiable (by simp)) u).hasFDerivAt
  change HasFDerivAt (fun v : C1HolderSpace E α =>
    holderValue α (c1HolderCR α hα₀ hα₁ J J₀ hJ hc c A v) z) _ u at hout
  simp only [c1HolderCR_apply,c1HolderAffineCurve_fderiv] at hout
  have he := congrArg (fun L : C1HolderSpace E α →L[ℝ] E => L h) (hout.unique hd)
  simp only [hev,ev,dev,ContinuousLinearMap.comp_apply,BoundedContinuousFunction.evalCLM_apply,
    sub_apply,add_apply,ContinuousLinearMap.flip_apply,zero_apply,map_zero,zero_add,
    Function.comp_def,sub_add_eq_sub_sub_swap] at he
  simpa only [c1HolderAffineCurve_fderiv, add_apply] using he

end HigherDimensionalBallPacking.Rigidity

 

namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
universe u v
variable {K : Type u} [MetricSpace K]
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
local instance cutoffHolderNormedAddCommGroup (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G] (α : ℝ) :
    NormedAddCommGroup (HolderSpace K G α) := inferInstance
local instance cutoffHolderNormedSpace (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G] (α : ℝ) :
    NormedSpace ℝ (HolderSpace K G α) := inferInstance

def holderConstCLM (α : ℝ) : E →L[ℝ] HolderSpace K E α :=
  LinearMap.mkContinuous
    { toFun := holderConst α
      map_add' := fun c d => by apply holderValue_injective α; ext z; rfl
      map_smul' := fun c d => by apply holderValue_injective α; ext z; rfl }
    1 (fun c => by
      change max ‖BoundedContinuousFunction.const K c‖ ‖(0 : OffDiagonal K →ᵇ E)‖ ≤ 1*‖c‖
      rw [norm_zero,one_mul]
      exact max_le (BoundedContinuousFunction.norm_const_le c) (norm_nonneg c))

@[simp] theorem holderConstCLM_apply (α : ℝ) (c : E) :
    holderConstCLM (K := K) α c = holderConst α c := rfl

 

def holderSourceCutoff (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1) (b : ContDiffBump (0:ℂ)) :
    HolderSpace ℂ ℝ α :=
  compactSmoothHolder α hα₀ hα₁ b b.contDiff b.hasCompactSupport

def holderSourceCutoffLinear (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1) (b : ContDiffBump (0:ℂ)) :
    HolderSpace ℂ ℂ α :=
  compactSmoothHolder α hα₀ hα₁ (fun z => b z • z) (b.contDiff.smul contDiff_id)
    b.hasCompactSupport.smul_right

def holderCutoffAffine (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1) (b : ContDiffBump (0:ℂ))
    (p : E × (ℂ →L[ℝ] E)) : HolderSpace ℂ E α :=
  holderCLM α (holderLinearPost α (ContinuousLinearMap.lsmul ℝ ℝ)
    (holderSourceCutoff α hα₀ hα₁ b)) (holderConst α p.1) +
  holderLinearPost α p.2 (holderSourceCutoffLinear α hα₀ hα₁ b)

@[simp] theorem holderCutoffAffine_apply (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (b : ContDiffBump (0:ℂ)) (p : E × (ℂ →L[ℝ] E)) (z : ℂ) :
    holderValue α (holderCutoffAffine α hα₀ hα₁ b p) z = b z • (p.1+p.2 z) := by
  change b z • p.1+p.2 (b z • z) = _
  rw [map_smul,smul_add]

 theorem holderCutoffAffine_contDiff (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (b : ContDiffBump (0:ℂ)) : ContDiff ℝ ∞ (holderCutoffAffine (E := E) α hα₀ hα₁ b) := by
  have hconst : ContDiff ℝ ∞ (fun p : E × (ℂ →L[ℝ] E) => holderConst (K := ℂ) α p.1) :=
    (holderConstCLM (K := ℂ) (E := E) α).contDiff.comp contDiff_fst
  have hlin : ContDiff ℝ ∞ (fun p : E × (ℂ →L[ℝ] E) =>
      holderLinearPost α p.2 (holderSourceCutoffLinear α hα₀ hα₁ b)) := by
    exact ((holderOperatorCLM (K := ℂ) (E := ℂ) (F := E) α).contDiff.comp
      ((holderConstCLM (K := ℂ) (E := ℂ →L[ℝ] E) α).contDiff.comp contDiff_snd)).clm_apply contDiff_const
  let M : HolderSpace ℂ (E →L[ℝ] E) α := holderLinearPost α
    (ContinuousLinearMap.lsmul ℝ ℝ) (holderSourceCutoff α hα₀ hα₁ b)
  have hmul := (holderCLM (K := ℂ) (E := E) (F := E) α M).contDiff.comp hconst
  exact hmul.add hlin

end HigherDimensionalBallPacking.Rigidity

namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
local instance affineFamilyDomainNormedAddCommGroup (α : ℝ) : NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance affineFamilyDomainNormedSpace (α : ℝ) : NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance affineFamilyCodomainNormedAddCommGroup (α : ℝ) : NormedAddCommGroup (HolderSpace ℂ F α) := inferInstance
local instance affineFamilyCodomainNormedSpace (α : ℝ) : NormedSpace ℝ (HolderSpace ℂ F α) := inferInstance

omit [CompleteSpace E] in
theorem affineProfile_lower_bound (c d v : E) (A B : ℂ →L[ℝ] E) (m U R t : ℝ)
    (_hm : 0 < m) (hA : ∀ z, m*‖z‖≤‖A z‖) (hd : ‖d‖≤1) (hB : ‖B‖≤ m/2)
    (hv : ‖v‖≤U) (ht : t∈Icc (0:ℝ) 1) (z : ℂ)
    (hz : R+‖c‖+1+U ≤ m/2*‖z‖) :
    R ≤ ‖c+A z+t • (d+B z)+v‖ := by
  have hb : ‖t • (d+B z)‖ ≤ 1+(m/2)*‖z‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    calc
      t*‖d+B z‖ ≤ ‖d+B z‖ := mul_le_of_le_one_left (norm_nonneg _) ht.2
      _ ≤ ‖d‖+‖B z‖ := norm_add_le _ _
      _ ≤ 1+‖B‖*‖z‖ := add_le_add hd (B.le_opNorm z)
      _ ≤ 1+(m/2)*‖z‖ := add_le_add (le_refl 1) (mul_le_mul_of_nonneg_right hB (norm_nonneg z))
  have hrev : ‖A z‖ ≤ ‖c+A z+t • (d+B z)+v‖+‖c‖+1+(m/2)*‖z‖+U := by
    calc
      ‖A z‖ = ‖(c+A z+t • (d+B z)+v)-(c+t • (d+B z)+v)‖ := by congr 1; abel
      _ ≤ ‖c+A z+t • (d+B z)+v‖+‖c+t • (d+B z)+v‖ := norm_sub_le _ _
      _ ≤ ‖c+A z+t • (d+B z)+v‖+((‖c‖+‖t • (d+B z)‖)+‖v‖) :=
        add_le_add (le_refl _) ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _)))
      _ ≤ ‖c+A z+t • (d+B z)+v‖+‖c‖+1+(m/2)*‖z‖+U := by linarith
  have ha := hA z
  linarith

 

omit [NormedSpace ℝ E] [CompleteSpace E] [NormedSpace ℝ F] [CompleteSpace F] in
theorem compactCoefficient_zero_outside {f : E → F} (hc : HasCompactSupport f) :
    ∃ R : ℝ, 0<R ∧ ∀ x, R≤‖x‖ → f x=0 := by
  obtain ⟨R,hR,hs⟩ := hc.isCompact.isBounded.subset_ball_lt 0 (0:E)
  refine ⟨R,hR,fun x hx => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have hh := hs h
  simp only [Metric.mem_ball,dist_zero_right] at hh
  exact (not_lt_of_ge hx) hh

def holderAffineFamily (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (p : (E × (ℂ →L[ℝ] E)) × HolderSpace ℂ E α) : HolderSpace ℂ F α :=
  holderProfilePost α hα₀ hα₁ (realAffineProfile p.1.1 p.1.2)
    (realAffineProfile_lipschitz p.1.1 p.1.2) f hf hc p.2

omit [CompleteSpace E] in
@[simp] theorem holderAffineFamily_apply (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (p : (E × (ℂ →L[ℝ] E)) × HolderSpace ℂ E α) (z : ℂ) :
    holderValue α (holderAffineFamily α hα₀ hα₁ f hf hc p) z =
      f (p.1.1+p.1.2 z+holderValue α p.2 z) := rfl

def localizedAffineFamily (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c : E) (A : ℂ →L[ℝ] E) (b : ContDiffBump (0:ℂ))
    (p : (E × (ℂ →L[ℝ] E)) × HolderSpace ℂ E α) : HolderSpace ℂ F α :=
  holderProfilePost α hα₀ hα₁ (realAffineProfile c A) (realAffineProfile_lipschitz c A) f hf hc
    (holderCutoffAffine α hα₀ hα₁ b (p.1.1-c,p.1.2-A)+p.2)

omit [CompleteSpace E] in
theorem localizedAffineFamily_contDiff (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c : E) (A : ℂ →L[ℝ] E) (b : ContDiffBump (0:ℂ)) :
    ContDiff ℝ ∞ (localizedAffineFamily α hα₀ hα₁ f hf hc c A b) := by
  apply (holderProfilePost_contDiff α hα₀ hα₁ (realAffineProfile c A)
    (realAffineProfile_lipschitz c A) f hf hc).comp
  exact ((holderCutoffAffine_contDiff α hα₀ hα₁ b).comp
    (((contDiff_fst.fst).sub contDiff_const).prodMk ((contDiff_fst.snd).sub contDiff_const))).add contDiff_snd

omit [CompleteSpace E] in
@[simp] theorem localizedAffineFamily_apply (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c : E) (A : ℂ →L[ℝ] E) (b : ContDiffBump (0:ℂ))
    (p : (E × (ℂ →L[ℝ] E)) × HolderSpace ℂ E α) (z : ℂ) :
    holderValue α (localizedAffineFamily α hα₀ hα₁ f hf hc c A b p) z =
      f (c+A z+b z • ((p.1.1-c)+(p.1.2-A) z)+holderValue α p.2 z) := by
  change f (c+A z+(holderValue α (holderCutoffAffine α hα₀ hα₁ b (p.1.1-c,p.1.2-A)) z+
    holderValue α p.2 z)) = _
  rw [holderCutoffAffine_apply]
  simp only [add_assoc]

omit [CompleteSpace E] in
theorem localizedAffineFamily_eq (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c : E) (A : ℂ →L[ℝ] E) (b : ContDiffBump (0:ℂ)) (m U R : ℝ)
    (hm : 0 < m) (hA : ∀ z, m*‖z‖≤‖A z‖) (hfR : ∀ x, R≤‖x‖ → f x=0)
    (hT : R+‖c‖+1+U ≤ m/2*b.rIn)
    (p : (E × (ℂ →L[ℝ] E)) × HolderSpace ℂ E α)
    (hd : ‖p.1.1-c‖≤1) (hB : ‖p.1.2-A‖≤ m/2) (hu : ‖p.2‖≤U) :
    localizedAffineFamily α hα₀ hα₁ f hf hc c A b p = holderAffineFamily α hα₀ hα₁ f hf hc p := by
  apply holderValue_injective α
  ext z
  rw [localizedAffineFamily_apply,holderAffineFamily_apply]
  by_cases hz : ‖z‖≤b.rIn
  · have hb : b z=1 := b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)
    rw [hb,one_smul]
    congr 1
    simp only [sub_apply]
    abel
  · have hz' : R+‖c‖+1+U ≤ m/2*‖z‖ := hT.trans
      (mul_le_mul_of_nonneg_left (le_of_not_ge hz) (half_pos hm).le)
    have hv : ‖holderValue α p.2 z‖≤U :=
      ((holderValue α p.2).norm_coe_le_norm z).trans ((holderValue_norm α p.2).trans hu)
    have ht : b z∈Icc (0:ℝ) 1 := ⟨b.nonneg,b.le_one⟩
    rw [hfR _ (affineProfile_lower_bound c (p.1.1-c) (holderValue α p.2 z)
      A (p.1.2-A) m U R (b z) hm hA hd hB hv ht z hz')]
    symm
    apply hfR
    convert affineProfile_lower_bound c (p.1.1-c) (holderValue α p.2 z)
      A (p.1.2-A) m U R 1 hm hA hd hB hv (by constructor <;> norm_num) z hz' using 1
    congr 1
    simp only [one_smul,sub_apply]
    abel

 

omit [CompleteSpace E] in
theorem holderAffineFamily_contDiffAt (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (p : (E × (ℂ →L[ℝ] E)) × HolderSpace ℂ E α)
    (m : ℝ) (hm : 0 < m) (hA : ∀ z, m*‖z‖≤‖p.1.2 z‖) :
    ContDiffAt ℝ ∞ (holderAffineFamily α hα₀ hα₁ f hf hc) p := by
  obtain ⟨R,hR,hfR⟩ := compactCoefficient_zero_outside hc
  let U : ℝ := ‖p.2‖+1
  let T : ℝ := (R+‖p.1.1‖+1+U)/(m/2)
  have hTpos : 0<T := div_pos (by dsimp [U]; positivity) (half_pos hm)
  let b : ContDiffBump (0:ℂ) := ⟨T,T+1,hTpos,lt_add_one T⟩
  have hT : R+‖p.1.1‖+1+U ≤ m/2*b.rIn := by
    dsimp [b,T]
    rw [mul_comm,div_mul_cancel₀ _ (half_pos hm).ne']
  let P := (E × (ℂ →L[ℝ] E)) × HolderSpace ℂ E α
  have hdc : ∀ᶠ q : P in 𝓝 p, ‖q.1.1-p.1.1‖<1 := by
    have h := (show Continuous (fun q : P => q.1.1) from continuous_fst.fst).continuousAt.tendsto.eventually
      (Metric.ball_mem_nhds p.1.1 (by norm_num : (0:ℝ)<1))
    simpa only [Metric.mem_ball,dist_eq_norm] using h
  have hdA : ∀ᶠ q : P in 𝓝 p, ‖q.1.2-p.1.2‖< m/2 := by
    have h := (show Continuous (fun q : P => q.1.2) from continuous_fst.snd).continuousAt.tendsto.eventually
      (Metric.ball_mem_nhds p.1.2 (half_pos hm))
    simpa only [Metric.mem_ball,dist_eq_norm] using h
  have hdu : ∀ᶠ q : P in 𝓝 p, ‖q.2-p.2‖<1 := by
    have h := (show Continuous (fun q : P => q.2) from continuous_snd).continuousAt.tendsto.eventually
      (Metric.ball_mem_nhds p.2 (by norm_num : (0:ℝ)<1))
    simpa only [Metric.mem_ball,dist_eq_norm] using h
  apply (localizedAffineFamily_contDiff α hα₀ hα₁ f hf hc p.1.1 p.1.2 b).contDiffAt.congr_of_eventuallyEq
  filter_upwards [hdc,hdA,hdu] with q hqc hqA hqu
  have hqu' : ‖q.2‖≤U := by
    calc
      ‖q.2‖ ≤ ‖q.2-p.2‖+‖p.2‖ := norm_le_norm_sub_add q.2 p.2
      _ ≤ 1+‖p.2‖ := add_le_add (le_of_lt hqu) (le_refl _)
      _ = U := add_comm _ _
  exact (localizedAffineFamily_eq α hα₀ hα₁ f hf hc p.1.1 p.1.2 b m U R hm hA hfR hT q
    hqc.le hqA.le hqu').symm

end HigherDimensionalBallPacking.Rigidity

 

namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
local instance crFamilyHolderNormedAddCommGroup (α : ℝ) : NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance crFamilyHolderNormedSpace (α : ℝ) : NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance crFamilyC1NormedAddCommGroup (α : ℝ) : NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance crFamilyC1NormedSpace (α : ℝ) : NormedSpace ℝ (C1HolderSpace E α) := inferInstance

def c1HolderCRFamily (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (J : E → E →L[ℝ] E) (J₀ : E →L[ℝ] E) (hJ : ContDiff ℝ ∞ J)
    (hc : HasCompactSupport (fun x => J x-J₀))
    (p : (E × (ℂ →L[ℝ] E)) × C1HolderSpace E α) : HolderSpace ℂ E α :=
  c1HolderCR α hα₀ hα₁ J J₀ hJ hc p.1.1 p.1.2 p.2

theorem c1HolderCRFamily_contDiffAt (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (J : E → E →L[ℝ] E) (J₀ : E →L[ℝ] E) (hJ : ContDiff ℝ ∞ J)
    (hc : HasCompactSupport (fun x => J x-J₀))
    (p : (E × (ℂ →L[ℝ] E)) × C1HolderSpace E α)
    (m : ℝ) (hm : 0 < m) (hA : ∀ z, m*‖z‖≤‖p.1.2 z‖) :
    ContDiffAt ℝ ∞ (c1HolderCRFamily α hα₀ hα₁ J J₀ hJ hc) p := by
  let P := (E × (ℂ →L[ℝ] E)) × C1HolderSpace E α
  let Q : P → (E × (ℂ →L[ℝ] E)) × HolderSpace ℂ E α :=
    fun q => (q.1,c1HolderValue α q.2)
  have hQ : ContDiff ℝ ∞ Q :=
    contDiff_fst.prodMk ((c1HolderValue (E := E) α).contDiff.comp contDiff_snd)
  let B : P → HolderSpace ℂ (E →L[ℝ] E) α := fun q =>
    holderConst α J₀ + holderAffineFamily α hα₀ hα₁ (fun x => J x-J₀)
      (hJ.sub contDiff_const) hc (Q q)
  have hB : ContDiffAt ℝ ∞ B p := contDiffAt_const.add
    ((holderAffineFamily_contDiffAt α hα₀ hα₁ (fun x => J x-J₀)
      (hJ.sub contDiff_const) hc (Q p) m hm hA).comp p hQ.contDiffAt)
  let D : P → HolderSpace ℂ (ℂ →L[ℝ] E) α :=
    fun q => holderConst α q.1.2+c1HolderDeriv α q.2
  have hD : ContDiff ℝ ∞ D :=
    ((holderConstCLM (K := ℂ) (E := ℂ →L[ℝ] E) α).contDiff.comp contDiff_fst.snd).add
      ((c1HolderDeriv (E := E) α).contDiff.comp contDiff_snd)
  have hop := (holderOperatorCLM (K := ℂ) (E := E) (F := E) α).contDiff.contDiffAt.comp p hB
  have hI := (holderJetEval (K := ℂ) (E := E) α Complex.I).contDiff.contDiffAt.comp p hD.contDiffAt
  have h1 := (holderJetEval (K := ℂ) (E := E) α 1).contDiff.contDiffAt.comp p hD.contDiffAt
  exact hI.sub (hop.clm_apply h1)

end HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
local instance graphHolderNormedAddCommGroup (α : ℝ) : NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance graphHolderNormedSpace (α : ℝ) : NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance graphC1NormedAddCommGroup (α : ℝ) : NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance graphC1NormedSpace (α : ℝ) : NormedSpace ℝ (C1HolderSpace E α) := inferInstance

lemma c1HolderGraph_mem_of_hasFDerivAt (α : ℝ) (f : HolderSpace ℂ E α)
    (D : HolderSpace ℂ (ℂ →L[ℝ] E) α)
    (hD : ∀ z, HasFDerivAt (holderValue α f) (holderValue α D z) z) :
    (f,D) ∈ c1HolderGraph α := by
  intro x y
  change holderValue α f y-holderValue α f x = linearSegmentIntegral x y (holderValue α D)
  rw [linearSegmentIntegral_apply]
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => holderValue α f (x+s • (y-x)))
      (holderValue α D (x+t • (y-x)) (y-x)) t := by
    simpa only [id_eq,one_smul,Function.comp_def] using
      ((hD (x+t • (y-x))).comp_hasDerivAt t (((hasDerivAt_id t).smul_const (y-x)).const_add x))
  symm
  simpa only [one_smul,zero_smul,add_zero,add_sub_cancel] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((segmentIntegrand_continuous (holderValue α D) x y).intervalIntegrable (0:ℝ) 1)

 
def compactSmoothC1Holder (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : ℂ → E) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : C1HolderSpace E α :=
  ⟨(compactSmoothHolder α hα₀ hα₁ f hf hc,
      compactSmoothHolder α hα₀ hα₁ (fderiv ℝ f) (hf.fderiv_right (by simp)) (hc.fderiv ℝ)),
    c1HolderGraph_mem_of_hasFDerivAt α _ _ (fun z => (hf.differentiable (by simp) z).hasFDerivAt)⟩

@[simp] lemma compactSmoothC1Holder_value (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : ℂ → E) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (z : ℂ) :
    holderValue α (c1HolderValue α (compactSmoothC1Holder α hα₀ hα₁ f hf hc)) z=f z := rfl

 

def c1HolderMultiply (α : ℝ) (P : C1HolderSpace (E →L[ℝ] F) α) :
    C1HolderSpace E α →L[ℝ] C1HolderSpace F α := by
  let V := (holderCLM α (c1HolderValue α P)).comp (c1HolderValue α)
  let A : HolderSpace ℂ ((ℂ →L[ℝ] E) →L[ℝ] (ℂ →L[ℝ] F)) α :=
    holderMap α (ContinuousLinearMap.compL ℝ ℂ E F) (c1HolderValue α P)
  let B : HolderSpace ℂ (E →L[ℝ] (ℂ →L[ℝ] F)) α :=
    holderMap α (ContinuousLinearMap.flipₗᵢ ℝ ℂ E F).toContinuousLinearEquiv.toContinuousLinearMap
      (c1HolderDeriv α P)
  let D := ((holderCLM α A).comp (c1HolderDeriv α))+((holderCLM α B).comp (c1HolderValue α))
  exact (V.prod D).codRestrict (c1HolderGraph α) (by
    intro u
    apply c1HolderGraph_mem_of_hasFDerivAt α
    intro z
    exact (c1Holder_hasFDerivAt α P z).clm_apply (c1Holder_hasFDerivAt α u z))

@[simp] lemma c1HolderMultiply_value (α : ℝ) (P : C1HolderSpace (E →L[ℝ] F) α)
    (u : C1HolderSpace E α) (z : ℂ) :
    holderValue α (c1HolderValue α (c1HolderMultiply α P u)) z =
      holderValue α (c1HolderValue α P) z (holderValue α (c1HolderValue α u) z) := rfl

 
def c1HolderConstantCLM (α : ℝ) : E →L[ℝ] C1HolderSpace E α :=
  ((holderConstantCLM α).prod 0).codRestrict (c1HolderGraph α) (by
    intro c
    apply c1HolderGraph_mem_of_hasFDerivAt α
    intro z
    exact hasFDerivAt_const c z)

@[simp] lemma c1HolderConstantCLM_value (α : ℝ) (c : E) (z : ℂ) :
    holderValue α (c1HolderValue α (c1HolderConstantCLM α c)) z = c := rfl

end HigherDimensionalBallPacking.Rigidity

open scoped ContDiff Topology BoundedContinuousFunction
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance markedProfileHolderNormedAddCommGroup (α : ℝ) : NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance markedProfileHolderNormedSpace (α : ℝ) : NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance markedProfileC1NormedAddCommGroup (α : ℝ) : NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance markedProfileC1NormedSpace (α : ℝ) : NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance markedProfileCompactNormedAddCommGroup (R : ℝ) : NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance markedProfileCompactNormedSpace (R : ℝ) : NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

 

def markedFramedProfile (R : ℝ) (Ainf : E →L[ℝ] E) (P : ℂ → E →L[ℝ] E)
    (hP : ContDiff ℝ ∞ P) (hc : HasCompactSupport P) :
    CompactHolderSpace E R →L[ℝ] (E × (ℂ →L[ℝ] E)) × C1HolderSpace E ((1:ℝ)/3) := by
  let C := compactCRInverse (E := E) R
  let C₀ := (c1HolderEval ((1:ℝ)/3) 0).comp C
  let D := ((c1HolderEval ((1:ℝ)/3) 1).comp C)-C₀
  let p := compactSmoothC1Holder ((1:ℝ)/3) (by norm_num) (by norm_num) P hP hc
  let N := compactSmoothC1Holder ((1:ℝ)/3) (by norm_num) (by norm_num)
    (slopeCoefficient P) (slopeCoefficient_smooth P hP) (slopeCoefficient_compact P hc)
  let A := c1HolderConstantCLM ((1:ℝ)/3) Ainf+p
  let B := (c1HolderMultiply ((1:ℝ)/3) A).comp C-
    ((c1HolderMultiply ((1:ℝ)/3) p).comp (c1HolderConstantCLM ((1:ℝ)/3))).comp C₀-
    ((c1HolderMultiply ((1:ℝ)/3) N).comp (c1HolderConstantCLM ((1:ℝ)/3))).comp D
  let a := -(Ainf.comp C₀)
  let d := -(((ContinuousLinearMap.compL ℝ ℂ E E) Ainf).comp
    (((ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] E →L[ℝ] E).flip).comp D))
  exact (a.prod d).prod B

lemma markedFramedProfile_value (R : ℝ) (Ainf : E →L[ℝ] E) (P : ℂ → E →L[ℝ] E)
    (hP : ContDiff ℝ ∞ P) (hc : HasCompactSupport P) (g : CompactHolderSpace E R) (z : ℂ) :
    (markedFramedProfile R Ainf P hP hc g).1.1+
      (markedFramedProfile R Ainf P hP hc g).1.2 z+
      holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) (markedFramedProfile R Ainf P hP hc g).2) z =
        (Ainf+P z) (markedCRInverse R g z) := by
  change -Ainf (compactCRInverseValue R g 0) +
    -Ainf (z • (compactCRInverseValue R g 1-compactCRInverseValue R g 0))+
    ((Ainf+P z) (compactCRInverseValue R g z)-P z (compactCRInverseValue R g 0)-
      P z (z • (compactCRInverseValue R g 1-compactCRInverseValue R g 0))) = _
  simp only [markedCRInverse,map_sub,add_apply]
  abel

 
lemma markedFramedProfile_marks (R : ℝ) (Ainf : E →L[ℝ] E) (P : ℂ → E →L[ℝ] E)
    (hP : ContDiff ℝ ∞ P) (hc : HasCompactSupport P) (g : CompactHolderSpace E R) :
    (∀ z ∈ ({0,1} : Set ℂ), (markedFramedProfile R Ainf P hP hc g).1.1+
      (markedFramedProfile R Ainf P hP hc g).1.2 z+
      holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) (markedFramedProfile R Ainf P hP hc g).2) z=0) := by
  intro z hz
  rw [markedFramedProfile_value]
  simp only [mem_insert_iff,mem_singleton_iff] at hz
  rcases hz with rfl|rfl <;> simp

end HigherDimensionalBallPacking.Rigidity

end

end OAI
