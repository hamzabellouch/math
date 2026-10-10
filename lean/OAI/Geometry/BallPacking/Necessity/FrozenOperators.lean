import Mathlib
import OAI.Geometry.BallPacking.Fredholm.CompactFredholmAlternative
import OAI.Geometry.BallPacking.Necessity.C1Energy
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
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap _root_.OAI.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology
open Set Filter Function MeasureTheory
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity

 theorem decaying_holomorphic_extends {n : ℕ} {u : ℂ → Phase n}
    (hholo : ∀ᶠ z in cocompact ℂ, DifferentiableAt ℂ u z)
    (hlim : Tendsto u (cocompact ℂ) (𝓝 0)) :
    ∃ v : ℂ → Phase n, ContDiffAt ℝ ∞ v 0 ∧
      u =ᶠ[cocompact ℂ] fun z => v z⁻¹ := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 (0:ℂ)) := by
    rw [←Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  have hl : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 (0:Phase n)) := by
    simpa only [zero_smul] using hi.smul hlim
  let V := infinityGerm u 0
  have hV : AnalyticAt ℂ V 0 := infinityGerm_analyticAt hholo hl
  have hV0 : V 0 = 0 := by simp [V,infinityGerm]
  obtain ⟨r,hr,hVr⟩ := hV.exists_ball_analyticOnNhd
  have hball : Metric.ball (0:ℂ) r ∈ 𝓝 (0:ℂ) := Metric.ball_mem_nhds _ hr
  have hv := ((Complex.differentiableOn_dslope hball).mpr hVr.differentiableOn).analyticAt hball
  refine ⟨dslope V 0,hv.contDiffAt.restrict_scalars ℝ,?_⟩
  filter_upwards [(isCompact_singleton (x := (0:ℂ))).compl_mem_cocompact] with z hz
  have hz0 : z ≠ 0 := by simpa using hz
  rw [dslope_of_ne V (inv_ne_zero hz0)]
  simp only [slope_def_module,sub_zero,V,infinityGerm,inv_ne_zero hz0,
    ite_false,ite_true,sub_zero,inv_inv,smul_smul,mul_inv_cancel₀ hz0,one_smul]

 theorem c1_decaying_CR_zero {n : ℕ} (K : ℂ → End n)
    (hK : ∀ z, Compatible (K z)) {u : ℂ → Phase n}
    (hu : ContDiff ℝ 1 u)
    (hCR : ∀ z, fderiv ℝ u z Complex.I=K z (fderiv ℝ u z 1))
    (hholo : ∀ᶠ z in cocompact ℂ, DifferentiableAt ℂ u z)
    (hlim : Tendsto u (cocompact ℂ) (𝓝 0)) : u=0 := by
  obtain ⟨v,hv,he⟩ := decaying_holomorphic_extends hholo hlim
  have hru : ContDiff ℝ 1 (realCurve u) := hu.comp Complex.equivRealProdCLM.symm.contDiff
  have hcr (z : Plane) : fderiv ℝ (realCurve u) z (0,1)=
      K (Complex.equivRealProdCLM.symm z) (fderiv ℝ (realCurve u) z (1,0)) := by
    rw [realCurve_fderiv (hu.differentiable one_ne_zero _),realCurve_fderiv (hu.differentiable one_ne_zero _)]
    simpa only [Complex.equivRealProdCLM_symm_apply,Complex.ofReal_zero,Complex.ofReal_one,
      zero_mul,one_mul,add_zero,zero_add] using hCR (Complex.equivRealProdCLM.symm z)
  have hpos (z : Plane) : 0≤c1Area (realCurve u) z := by
    unfold c1Area
    rw [hcr]
    by_cases hz : fderiv ℝ (realCurve u) z (1,0)=0
    · simp [hz,standardForm]
    · exact ((hK _).2.2 _ hz).le
  have hang : Tendsto (fun z : Plane => planarPullback (realCurve u) stdPrimitive z (planeRotation z))
      (cocompact Plane) (𝓝 0) := by
    have hr : Tendsto Complex.equivRealProdCLM.symm (cocompact Plane) (cocompact ℂ) :=
      Complex.equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding.tendsto_cocompact
    have hh := (affine_primitive_angular_limit_zero hv he (stdPrimitive_smooth n).continuous).comp hr
    apply hh.congr
    intro z
    change stdPrimitive _ _=stdPrimitive _ _
    have hd := realCurve_fderiv (z:=z) (hu.differentiable one_ne_zero _) (planeRotation z)
    rw [equivRealProd_rotation] at hd
    exact congrArg (stdPrimitive (u (Complex.equivRealProdCLM.symm z))) hd.symm
  obtain ⟨hai,ha0⟩ := c1_area_of_nonneg_of_angular_limit hru hpos hang
  have ha : c1Area (realCurve u)=0 :=
    ((c1Area_continuous hru).ae_eq_iff_eq volume continuous_const).mp
      ((integral_eq_zero_iff_of_nonneg hpos hai).mp ha0)
  have hx (z : Plane) : fderiv ℝ (realCurve u) z (1,0)=0 := by
    by_contra hn
    have hp := (hK (Complex.equivRealProdCLM.symm z)).2.2 _ hn
    have hz := congrFun ha z
    change standardForm _ _=0 at hz
    rw [hcr] at hz
    linarith
  have hd (z : Plane) : fderiv ℝ (realCurve u) z=0 := by
    apply ContinuousLinearMap.ext
    intro w
    have hw : w=w.1 • ((1,0):Plane)+w.2 • ((0,1):Plane) := by ext <;> simp
    rw [hw,map_add,map_smul,map_smul,hx,hcr,hx,map_zero]
    simp
  have hc (z : ℂ) : u z=u 0 := by
    have hh := is_const_of_fderiv_eq_zero (hru.differentiable one_ne_zero)
      hd (Complex.equivRealProdCLM z) 0
    simpa only [realCurve,Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply,map_zero] using hh
  have hec : u=fun _ => u 0 := funext hc
  have hz : u 0=0 := tendsto_nhds_unique tendsto_const_nhds (hec ▸ hlim)
  funext z
  exact (hc z).trans hz

local instance FrozenKernelLocal1 (n : ℕ) (R : ℝ) : NormedAddCommGroup (CompactHolderSpace (Phase n) R) := inferInstance
local instance FrozenKernelLocal2 (n : ℕ) (R : ℝ) : NormedSpace ℝ (CompactHolderSpace (Phase n) R) := inferInstance

 theorem compactCRInverse_frozen_kernel {n : ℕ} (R : ℝ) (K : ℂ → End n)
    (hK : ∀ z, Compatible (K z)) (g : CompactHolderSpace (Phase n) R)
    (hCR : ∀ z, fderiv ℝ (compactCRInverseValue R g) z Complex.I=
      K z (fderiv ℝ (compactCRInverseValue R g) z 1)) : g=0 := by
  have hholo : ∀ᶠ z in cocompact ℂ, DifferentiableAt ℂ (compactCRInverseValue R g) z := by
    have he := hasCompactSupport_iff_eventuallyEq.mp (compactHolderValue_compactSupport R g)
    rw [coclosedCompact_eq_cocompact] at he
    filter_upwards [he] with z hz
    apply differentiableAt_complex_iff_differentiableAt_real.mpr
    refine ⟨(compactCRInverse_contDiff R g).differentiable one_ne_zero z,?_⟩
    exact sub_eq_zero.mp ((compactCRInverse_rightInverse R g z).trans hz)
  have hu := c1_decaying_CR_zero K hK (compactCRInverse_contDiff R g) hCR hholo
    (compactCRInverse_tendsto_zero R g)
  apply Subtype.ext
  apply holderValue_injective ((1:ℝ)/3)
  apply BoundedContinuousFunction.ext
  intro z
  have he := compactCRInverse_rightInverse R g z
  rw [hu] at he
  simpa using he.symm

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
local instance HolderLowerCompactLocal1 : NormedAddCommGroup (HolderSpace ℂ E ((1:ℝ)/3)) := inferInstance
local instance HolderLowerCompactLocal2 : NormedSpace ℝ (HolderSpace ℂ E ((1:ℝ)/3)) := inferInstance
local instance HolderLowerCompactLocal3 : NormedAddCommGroup (C1HolderSpace E ((1:ℝ)/3)) := inferInstance
local instance HolderLowerCompactLocal4 : NormedSpace ℝ (C1HolderSpace E ((1:ℝ)/3)) := inferInstance

 theorem c1LowerOrderCLM_compact_holder (R : ℝ)
    (M : HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) M z=0) :
    IsCompactOperator (c1LowerOrderCLM M) := by
  let b : ContDiffBump (0:ℂ) := ⟨max R 0+1,max R 0+2,by positivity,by linarith⟩
  let P : ℂ → E →L[ℝ] E := fun z => b z • ContinuousLinearMap.id ℝ E
  have hP : ContDiff ℝ ∞ P := b.contDiff.smul contDiff_const
  have hc : HasCompactSupport P := b.hasCompactSupport.smul_right
  let Q := compactSmoothHolder ((1:ℝ)/3) (by norm_num) (by norm_num) P hP hc
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hP (by simp)
  have hQ := c1LowerOrderCLM_compact (E := E) b.rOut Q (by
    intro z hz
    change b z • ContinuousLinearMap.id ℝ E=0
    rw [b.zero_of_le_dist (by simpa using hz.le),zero_smul]) L hL
  have he : c1LowerOrderCLM M=(holderCLM ((1:ℝ)/3) M).comp (c1LowerOrderCLM Q) := by
    apply ContinuousLinearMap.ext
    intro u
    apply holderValue_injective ((1:ℝ)/3)
    apply BoundedContinuousFunction.ext
    intro z
    change holderValue ((1:ℝ)/3) M z (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u) z)=
      holderValue ((1:ℝ)/3) M z (P z (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u) z))
    by_cases hz : ‖z‖≤R
    · have hb : b z=1 := b.one_of_mem_closedBall (by
        simp only [Metric.mem_closedBall,dist_zero_right]
        exact hz.trans ((le_max_left R 0).trans (by dsimp [b]; linarith)))
      simp only [P,hb,one_smul,ContinuousLinearMap.id_apply]
    · rw [hs z (lt_of_not_ge hz)]
      rfl
  rw [he]
  exact hQ.clm_comp (holderCLM ((1:ℝ)/3) M)

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
local instance FrozenFrameLocal1 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance FrozenFrameLocal2 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance FrozenFrameLocal3 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :
    NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance FrozenFrameLocal4 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :
    NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance FrozenFrameLocal5 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance FrozenFrameLocal6 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

 theorem c1_decay_cauchy_representation {n : ℕ} (R : ℝ)
    (g : CompactHolderSpace (Phase n) R) {v : ℂ → Phase n} (hv : ContDiff ℝ 1 v)
    (hcurl : ∀ z, fderiv ℝ v z Complex.I-Complex.I • fderiv ℝ v z 1=compactHolderValue R g z)
    (hlim : Tendsto v (cocompact ℂ) (𝓝 0)) : v=compactCRInverseValue R g := by
  let w : ℂ → Phase n := fun z => v z-compactCRInverseValue R g z
  have hd : Differentiable ℂ w := by
    intro z
    have hvd := hv.differentiable one_ne_zero z
    have hgd := (compactCRInverse_contDiff R g).differentiable one_ne_zero z
    apply differentiableAt_complex_iff_differentiableAt_real.mpr
    refine ⟨hvd.sub hgd,?_⟩
    change fderiv ℝ (v-_) z Complex.I=Complex.I • fderiv ℝ (v-_) z 1
    rw [fderiv_sub hvd hgd]
    simp only [sub_apply,smul_sub]
    have h1 := hcurl z
    have h2 := compactCRInverse_rightInverse R g z
    exact sub_eq_sub_iff_sub_eq_sub.mp (h1.trans h2.symm)
  have hl : Tendsto w (cocompact ℂ) (𝓝 0) := by
    simpa only [sub_self] using hlim.sub (compactCRInverse_tendsto_zero R g)
  have he := hd.eq_const_of_tendsto_cocompact hl
  funext z
  exact sub_eq_zero.mp (congrFun he z)

 def unmarkedLower {n : ℕ} (R : ℝ) (M : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) M z=0) :
    CompactHolderSpace (Phase n) R →L[ℝ] CompactHolderSpace (Phase n) R :=
  ((c1LowerOrderCLM M).comp (compactCRInverse R)).codRestrict (compactHolderSubmodule R) (by
    intro g z hz
    change holderValue ((1:ℝ)/3) M z (compactCRInverseValue R g z)=0
    rw [hs z hz,zero_apply])

 @[simp] theorem unmarkedLower_value {n : ℕ} (R : ℝ) (M : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) M z=0)
    (g : CompactHolderSpace (Phase n) R) (z : ℂ) :
    compactHolderValue R (unmarkedLower R M hs g) z=
      holderValue ((1:ℝ)/3) M z (compactCRInverseValue R g z) := rfl

 theorem unmarkedLower_compact {n : ℕ} (R : ℝ) (M : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) M z=0) :
    IsCompactOperator (unmarkedLower R M hs) :=
  ((c1LowerOrderCLM_compact_holder R M hs).comp_clm _).codRestrict _
    (compactHolderSubmodule_isClosed R)

 def c1StandardCurl {n : ℕ} : C1HolderSpace (Phase n) ((1:ℝ)/3) →L[ℝ]
      HolderSpace ℂ (Phase n) ((1:ℝ)/3) :=
  (holderJetEval (E := Phase n) ((1:ℝ)/3) Complex.I).comp (c1HolderDeriv ((1:ℝ)/3))-
    (holderMap ((1:ℝ)/3) (standardJ n)).comp
      ((holderJetEval (E := Phase n) ((1:ℝ)/3) 1).comp (c1HolderDeriv ((1:ℝ)/3)))

 theorem c1StandardCurl_value {n : ℕ} (u : C1HolderSpace (Phase n) ((1:ℝ)/3)) (z : ℂ) :
    holderValue ((1:ℝ)/3) (c1StandardCurl u) z =
    fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) z Complex.I-
      Complex.I • fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)) z 1 := by
  rw [(c1Holder_hasFDerivAt ((1:ℝ)/3) u z).fderiv]
  rfl

 theorem frame_product_CR {n : ℕ} {a : ℂ → End n} {v : ℂ → Phase n} {z : ℂ}
    (ha : DifferentiableAt ℝ a z) (hv : DifferentiableAt ℝ v z) (K M : End n)
    (hint : ∀ x, a z (Complex.I • x)=K (a z x))
    (hM : ∀ x, fderiv ℝ a z Complex.I x-K (fderiv ℝ a z 1 x)=a z (M x)) :
    fderiv ℝ (fun w => a w (v w)) z Complex.I-
      K (fderiv ℝ (fun w => a w (v w)) z 1)=
    a z (fderiv ℝ v z Complex.I-Complex.I • fderiv ℝ v z 1+M (v z)) := by
  have hd (w : ℂ) : fderiv ℝ (fun w => a w (v w)) z w=
      a z (fderiv ℝ v z w)+fderiv ℝ a z w (v z) := by
    rw [fderiv_clm_apply ha hv]
    rfl
  rw [hd Complex.I,hd 1,map_add,←hint (fderiv ℝ v z 1),map_add,map_sub]
  calc
    _ = (a z (fderiv ℝ v z Complex.I)-a z (Complex.I • fderiv ℝ v z 1))+
      (fderiv ℝ a z Complex.I (v z)-K (fderiv ℝ a z 1 (v z))) := by abel
    _ = _ := by rw [hM]

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
local instance FrozenSurjectiveLocal1 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance FrozenSurjectiveLocal2 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance FrozenSurjectiveLocal3 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :
    NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance FrozenSurjectiveLocal4 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :
    NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance FrozenSurjectiveLocal5 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance FrozenSurjectiveLocal6 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

 theorem c1_framed_decaying_kernel {n : ℕ} (R : ℝ) (K a M : ℂ → End n)
    (hK : ∀ z, Compatible (K z)) (hKout : ∀ z : ℂ, R<‖z‖ → K z=standardJ n)
    (ha : ContDiff ℝ 1 a) (v : ℂ → Phase n) (hv : ContDiff ℝ 1 v)
    (hAout : ∀ z : ℂ, R<‖z‖ → a z=ContinuousLinearMap.id ℝ _)
    (hAinj : ∀ z, Injective (a z))
    (hint : ∀ z x, a z (Complex.I • x)=K z (a z x))
    (hM : ∀ z x, fderiv ℝ a z Complex.I x-K z (fderiv ℝ a z 1 x)=a z (M z x))
    (hzero : ∀ z, fderiv ℝ v z Complex.I-Complex.I • fderiv ℝ v z 1+M z (v z)=0)
    (hvlim : Tendsto v (cocompact ℂ) (𝓝 0)) : v=0 := by
  let u : ℂ → Phase n := fun z => a z (v z)
  have hu : ContDiff ℝ 1 u := ha.clm_apply hv
  have hCR (z : ℂ) : fderiv ℝ u z Complex.I=K z (fderiv ℝ u z 1) := by
    apply sub_eq_zero.mp
    have hh := frame_product_CR (ha.differentiable one_ne_zero z)
      (hv.differentiable one_ne_zero z) (K z) (M z) (hint z) (hM z)
    change fderiv ℝ u z Complex.I-K z (fderiv ℝ u z 1)=_ at hh
    rw [hh,hzero z,map_zero]
  have hlim : Tendsto u (cocompact ℂ) (𝓝 0) := by
    apply hvlim.congr'
    filter_upwards [(isCompact_closedBall (0:ℂ) R).compl_mem_cocompact] with z hz
    have hzR : R<‖z‖ := by simpa only [mem_compl_iff,Metric.mem_closedBall,dist_zero_right,not_le] using hz
    change v z=a z (v z)
    rw [hAout z hzR,ContinuousLinearMap.id_apply]
  have hholo : ∀ᶠ z in cocompact ℂ, DifferentiableAt ℂ u z := by
    filter_upwards [(isCompact_closedBall (0:ℂ) R).compl_mem_cocompact] with z hz
    have hzR : R<‖z‖ := by simpa only [mem_compl_iff,Metric.mem_closedBall,dist_zero_right,not_le] using hz
    apply differentiableAt_complex_iff_differentiableAt_real.mpr
    refine ⟨hu.differentiable one_ne_zero z,?_⟩
    have hh := hCR z
    rw [hKout z hzR] at hh
    exact hh
  have hu0 := c1_decaying_CR_zero K hK hu hCR hholo hlim
  funext z
  apply hAinj z
  change u z=a z 0
  rw [congrFun hu0 z,map_zero]
  rfl

 theorem framed_unmarked_surjective {n : ℕ} (R : ℝ) (K : ℂ → End n)
    (hK : ∀ z, Compatible (K z)) (hKout : ∀ z : ℂ, R<‖z‖ → K z=standardJ n)
    (A : C1HolderSpace (End n) ((1:ℝ)/3)) (M : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) M z=0)
    (hAout : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z=ContinuousLinearMap.id ℝ _)
    (hAinj : ∀ z, Injective (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z))
    (hint : ∀ z x, holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z (Complex.I • x)=
      K z (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z x))
    (hM : ∀ z x, fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) z Complex.I x-
      K z (fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) z 1 x)=
      holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z (holderValue ((1:ℝ)/3) M z x)) :
    Surjective (fun g : CompactHolderSpace (Phase n) R => g+unmarkedLower R M hs g) := by
  apply (compactPerturbation_injective_iff_surjective _ (unmarkedLower_compact R M hs)).mp
  apply (LinearMap.ker_eq_bot (f := (ContinuousLinearMap.id ℝ (CompactHolderSpace (Phase n) R)+unmarkedLower R M hs).toLinearMap)).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro g hg
  change g+unmarkedLower R M hs g=0 at hg
  have hzero (z : ℂ) : compactHolderValue R g z+holderValue ((1:ℝ)/3) M z (compactCRInverseValue R g z)=0 :=
    congrArg (fun g => compactHolderValue R g z) hg
  have hg0 := c1_framed_decaying_kernel R K
    (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) (holderValue ((1:ℝ)/3) M)
    hK hKout (c1Holder_contDiff _ A) (compactCRInverseValue R g)
    (compactCRInverse_contDiff R g) hAout hAinj hint hM
    (fun z => by rw [compactCRInverse_rightInverse R g z]; exact hzero z)
    (compactCRInverse_tendsto_zero R g)
  apply Subtype.ext
  apply holderValue_injective ((1:ℝ)/3)
  apply BoundedContinuousFunction.ext
  intro z
  have hh := compactCRInverse_rightInverse R g z
  rw [hg0] at hh
  simpa using hh.symm

end HigherDimensionalBallPacking.Rigidity

end

end OAI
