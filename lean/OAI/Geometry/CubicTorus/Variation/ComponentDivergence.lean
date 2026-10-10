import Mathlib
import OAI.Geometry.CubicTorus.Estimates.CorrectedChain

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
namespace Periodic

lemma simultaneousCofactor_second_deriv (l : List Variation) (x n : Cover) :
    deriv (deriv (fun t ↦ chainCofactor (simultaneousChain l t) x n)) 0=(normalJet l x n).2.2 := by
  induction l using List.reverseRecOn with
  | nil => simp [simultaneousChain,chainCofactor,normalJet]
  | append_singleton l a ih =>
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ chainMove (simultaneousChain l t) x) :=
      (simultaneousMove_smooth l).comp (contDiff_id.prodMk contDiff_const)
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ chainCofactor (simultaneousChain l t) x n) :=
      (simultaneousCofactor_smooth l).comp (contDiff_id.prodMk (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ ↦ (x,n))))
    have hf : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ coordinateNormalVelocity a.coordinate a.function
      (chainMove (simultaneousChain l t) x) (chainCofactor (simultaneousChain l t) x n)) :=
      (wallVelocity_contDiff a).comp (hm.prodMk hc)
    have he : (fun t ↦ chainCofactor (simultaneousChain (l++[a]) t) x n)=
        (fun t ↦ chainCofactor (simultaneousChain l t) x n+
          t • coordinateNormalVelocity a.coordinate a.function (chainMove (simultaneousChain l t) x)
            (chainCofactor (simultaneousChain l t) x n)) := by
      funext t
      simp [simultaneousChain,List.map_append,chainCofactor_append,chainCofactor,coordinateCofactor_eq]
    rw [he,second_deriv_add_time_smul hc hf,ih,normalJet_append]
    dsimp only
    congr 2
    have hdf : HasFDerivAt (fun p : Cover×Cover ↦ coordinateNormalVelocity a.coordinate a.function p.1 p.2)
        (fderiv ℝ (fun p : Cover×Cover ↦ coordinateNormalVelocity a.coordinate a.function p.1 p.2) (x,n))
        (chainMove (simultaneousChain l 0) x,chainCofactor (simultaneousChain l 0) x n) := by
      simpa only [simultaneousMove_zero,simultaneousCofactor_zero] using
        ((wallVelocity_contDiff a).differentiable (by simp) (x,n)).hasFDerivAt
    have hd := hdf.comp_hasDerivAt 0
      ((hm.differentiable (by simp) 0).hasDerivAt.prodMk (hc.differentiable (by simp) 0).hasDerivAt)
    simpa only [Function.comp_def,simultaneousMove_deriv,simultaneousCofactor_deriv,
      (normalJet_first l x n).1,(normalJet_first l x n).2] using hd.deriv

theorem simultaneousArea_second_deriv (l : List Variation) (μ : FiniteMeasure NormalBundle) :
    deriv (deriv (fun t ↦ ∫ z,‖chainCofactor (simultaneousChain l t) z.1 z.2‖
      ∂(μ : Measure NormalBundle))) 0 =
      ∫ z,‖chainNormalVelocity l z.1 z.2‖^2-⟪(z.2 : Cover),chainNormalVelocity l z.1 z.2⟫^2+
        ⟪(z.2 : Cover),(normalJet l z.1 z.2).2.2⟫ ∂(μ : Measure NormalBundle) := by
  have h := normalArea_second_derivative (simultaneousCofactor_smooth l)
    (by intro p _; exact simultaneousCofactor_zero l p.1 p.2) μ
  simpa only [normalEmbedding,simultaneousCofactor_deriv,simultaneousCofactor_second_deriv] using h

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

def componentDivergence (a : Variation) (x : Cover) : ℝ :=
  fderiv ℝ a.function x (EuclideanSpace.single a.coordinate 1)

lemma componentDivergence_smooth (a : Variation) : ContDiff ℝ (⊤ : ℕ∞) (componentDivergence a) :=
  (a.smooth.fderiv_right (by simp)).clm_apply contDiff_const

def massJet (l : List Variation) (x : Cover) : Cover×ℝ×ℝ :=
  l.foldl (fun j a ↦ (j.1+a.function x • EuclideanSpace.single a.coordinate 1,
    j.2.1+componentDivergence a x,
    j.2.2+2*(fderiv ℝ (componentDivergence a) x j.1+j.2.1*componentDivergence a x))) (0,0,0)

lemma massJet_append (l : List Variation) (a : Variation) (x : Cover) :
    massJet (l++[a]) x = ((massJet l x).1+a.function x • EuclideanSpace.single a.coordinate 1,
      (massJet l x).2.1+componentDivergence a x,
      (massJet l x).2.2+2*(fderiv ℝ (componentDivergence a) x (massJet l x).1+
        (massJet l x).2.1*componentDivergence a x)) := by
  simp only [massJet,List.foldl_append,List.foldl_cons,List.foldl_nil]

lemma massJet_first (l : List Variation) (x : Cover) :
    (massJet l x).1=chainVelocity l x := by
  induction l using List.reverseRecOn with
  | nil => simp [massJet,chainVelocity]
  | append_singleton l a ih =>
    simpa [massJet_append,chainVelocity,List.map_append] using
      congrArg (fun u ↦ u+a.function x • EuclideanSpace.single a.coordinate (1 : ℝ)) ih

lemma simultaneousJacobian_append (l : List Variation) (a : Variation) (x : Cover) (t : ℝ) :
    chainJacobian (simultaneousChain (l++[a]) t) x=chainJacobian (simultaneousChain l t) x+
      t*(chainJacobian (simultaneousChain l t) x*componentDivergence a (chainMove (simultaneousChain l t) x)) := by
  simp only [simultaneousChain,List.map_append,chainJacobian_append,List.map_cons,List.map_nil,
    chainJacobian,coordinateJacobian,mul_one,componentDivergence]
  ring

lemma simultaneousJacobian_deriv (l : List Variation) (x : Cover) :
    deriv (fun t ↦ chainJacobian (simultaneousChain l t) x) 0=(massJet l x).2.1 := by
  induction l using List.reverseRecOn with
  | nil => simp [simultaneousChain,chainJacobian,massJet]
  | append_singleton l a ih =>
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ chainMove (simultaneousChain l t) x) :=
      (simultaneousMove_smooth l).comp (contDiff_id.prodMk contDiff_const)
    have hj : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ chainJacobian (simultaneousChain l t) x) :=
      (simultaneousJacobian_smooth l).comp (contDiff_id.prodMk contDiff_const)
    simp_rw [simultaneousJacobian_append l a x]
    simpa [massJet_append,ih] using deriv_add_time_smul hj (hj.mul ((componentDivergence_smooth a).comp hm))

lemma simultaneousJacobian_second_deriv (l : List Variation) (x : Cover) :
    deriv (deriv (fun t ↦ chainJacobian (simultaneousChain l t) x)) 0=(massJet l x).2.2 := by
  induction l using List.reverseRecOn with
  | nil => simp [simultaneousChain,chainJacobian,massJet]
  | append_singleton l a ih =>
    have hm : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ chainMove (simultaneousChain l t) x) :=
      (simultaneousMove_smooth l).comp (contDiff_id.prodMk contDiff_const)
    have hj : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ ↦ chainJacobian (simultaneousChain l t) x) :=
      (simultaneousJacobian_smooth l).comp (contDiff_id.prodMk contDiff_const)
    have hd : HasFDerivAt (componentDivergence a) (fderiv ℝ (componentDivergence a) x)
        (chainMove (simultaneousChain l 0) x) := by
      simpa only [simultaneousMove_zero] using
        ((componentDivergence_smooth a).differentiable (by simp) x).hasFDerivAt
    have hf := hd.comp_hasDerivAt 0 ((hm.differentiable (by simp) 0).hasDerivAt)
    have he := ((hj.differentiable (by simp) 0).hasDerivAt.mul hf).deriv
    simp only [Function.comp_def,simultaneousJacobian_zero,simultaneousMove_zero,
      simultaneousMove_deriv,simultaneousJacobian_deriv,one_mul] at he
    change deriv (fun t ↦ chainJacobian (simultaneousChain l t) x *
      componentDivergence a (chainMove (simultaneousChain l t) x)) 0 =
      (massJet l x).2.1*componentDivergence a x+fderiv ℝ (componentDivergence a) x (chainVelocity l x) at he
    simp_rw [simultaneousJacobian_append l a x]
    have hh := second_deriv_add_time_smul hj (hj.mul ((componentDivergence_smooth a).comp hm))
    simp only [smul_eq_mul,Function.comp_def] at hh
    rw [hh,ih,he,massJet_append]
    simp only [massJet_first]
    ring

lemma simultaneousMass_second_deriv (l : List Variation) (E : Set Torus) :
    deriv (deriv (fun t ↦ chainMass (simultaneousChain l t) E)) 0=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,(massJet l x).2.2 := by
  simpa only [chainMass,simultaneousJacobian_second_deriv] using
    second_deriv_compact_parameter_integral isCompact_closedFundamentalCube
      (cubeIntersection_compact_carrier E) (simultaneousJacobian_smooth l) 0

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem exists_chain_of_field {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ m x,F (x+latticeVector m)=F x) :
    ∃ l : List Variation,(∀ x,chainVelocity l x=F x) ∧
      (∀ E,chainFlux l E=∫ x in fundamentalCube∩quotientMap ⁻¹' E,divergence F x) ∧
      ∀ x n,⟪n,chainNormalVelocity l x n⟫=‖n‖^2*divergence F x-⟪n,fderiv ℝ F x n⟫ := by
  have hx (i : Fin 3) : ∃ a : Variation,a.coordinate=i ∧ a.function=(fun x ↦ F x i) :=
    exists_variation_of_function i ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff.comp hF)
      (fun m x ↦ by change F (x+latticeVector m) i=F x i; rw [hp])
  choose a ha hb using hx
  refine ⟨List.ofFn a,?_,?_,?_⟩
  · intro x
    simp only [chainVelocity,List.map_ofFn,List.sum_ofFn,Function.comp_apply,ha,hb]
    ext j
    simp [Finset.sum_apply,Pi.single_apply,smul_eq_mul]
  · intro E
    simp only [chainFlux,List.map_ofFn,List.sum_ofFn,Function.comp_apply,ha,hb]
    exact (flux_sum_components E hF).symm
  · intro x n
    simp only [chainNormalVelocity,List.map_ofFn,List.sum_ofFn,Function.comp_apply,ha,hb,
      inner_sum,coordinateNormalVelocity,inner_sub_right,real_inner_smul_right,
      real_inner_self_eq_norm_sq,inner_gradient_right,conj_trivial,
      Finset.sum_sub_distrib,← Finset.sum_mul]
    simp_rw [fderiv_component (hF.differentiable (by simp) x)]
    dsimp [divergence]
    congr 1
    · ring
    · simp [PiLp.inner_apply,EuclideanSpace.single,mul_comm]

theorem isMinimizerAt_stable_fields {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ),IsNormalMeasure E μ ∧
      (∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ n x,F (x+latticeVector n)=F x) →
        (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
          H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) ∧
      ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ n x,F (x+latticeVector n)=F x) →
        (∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))=0 →
        ∃ l : List Variation,(∀ x,deriv (fun t ↦ chainMove (simultaneousChain l t) x) 0=F x) ∧
          0≤deriv (deriv (fun t ↦ ∫ z,‖chainCofactor (simultaneousChain l t) z.1 z.2‖
            ∂(μ : Measure NormalBundle))) 0-
            H*deriv (deriv (fun t ↦ chainMass (simultaneousChain l t) E)) 0 := by
  obtain ⟨μ,H,hμ,hH,hs⟩ := isMinimizerAt_stable_periodic hV hE hmin
  refine ⟨μ,H,hμ,fun F hf hp ↦ weakCMC_identity hμ hH hf hp,?_⟩
  intro F hf hp hz
  obtain ⟨l,hl,hflux,_⟩ := exists_chain_of_field hf hp
  refine ⟨l,fun x ↦ (simultaneousMove_deriv l x).trans (hl x),hs l ?_⟩
  rw [simultaneousMass_deriv,hflux]
  obtain ⟨C,hC,hbound⟩ := periodic_bounded hf.continuous hp
  rw [← normalMeasure_flux hμ hf hp (by linarith : 0<C+1)
    (fun x ↦ (hbound x).trans (by linarith : C≤C+1))]
  exact hz

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

def chainQuadratic (E : Set Torus) (μ : FiniteMeasure NormalBundle) (H : ℝ)
    (l : List Variation) : ℝ :=
  (∫ z,‖chainNormalVelocity l z.1 z.2‖^2-⟪(z.2 : Cover),chainNormalVelocity l z.1 z.2⟫^2+
    ⟪(z.2 : Cover),(normalJet l z.1 z.2).2.2⟫ ∂(μ : Measure NormalBundle))-
    H*(∫ x in fundamentalCube∩quotientMap ⁻¹' E,(massJet l x).2.2)

theorem isMinimizerAt_expanded_stability {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ),IsNormalMeasure E μ ∧
      (∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ n x,F (x+latticeVector n)=F x) →
        (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
          H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) ∧
      (∀ l : List Variation,chainFlux l E=0 → 0≤chainQuadratic E μ H l) ∧
      ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ n x,F (x+latticeVector n)=F x) →
        (∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))=0 →
        ∃ l : List Variation,(∀ x,chainVelocity l x=F x) ∧
          chainFlux l E=0 ∧ 0≤chainQuadratic E μ H l := by
  obtain ⟨μ,H,hμ,hH,hs⟩ := isMinimizerAt_stable_periodic hV hE hmin
  have hq (l : List Variation) (hl : chainFlux l E=0) : 0≤chainQuadratic E μ H l := by
    have hh := hs l (by rw [simultaneousMass_deriv,hl])
    simpa only [chainQuadratic,simultaneousArea_second_deriv,simultaneousMass_second_deriv] using hh
  refine ⟨μ,H,hμ,fun F hf hp ↦ weakCMC_identity hμ hH hf hp,hq,?_⟩
  intro F hf hp hz
  obtain ⟨l,hl,hflux,_⟩ := exists_chain_of_field hf hp
  have hh : chainFlux l E=0 := by
    rw [hflux]
    obtain ⟨C,_,hbound⟩ := periodic_bounded hf.continuous hp
    have hC : 0<C+‖F 0‖+1 := by linarith [hbound 0,norm_nonneg (F 0)]
    rw [← normalMeasure_flux hμ hf hp hC (fun x ↦ (hbound x).trans (by linarith [norm_nonneg (F 0)] : C≤C+‖F 0‖+1))]
    exact hz
  exact ⟨l,hl,hh,hq l hh⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coverTrace (L : Cover →L[ℝ] Cover) : ℝ :=
  ∑ i : Fin 3, L (EuclideanSpace.single i 1) i

lemma cover_decompose (v : Cover) : v=∑ i : Fin 3,v i • EuclideanSpace.single i 1 := by
  ext j
  simp [Pi.single_apply]

lemma cover_clm_component (L : Cover →L[ℝ] Cover) (v : Cover) (i : Fin 3) :
    L v i=∑ j : Fin 3,v j*L (EuclideanSpace.single j 1) i := by
  change (EuclideanSpace.proj i : Cover →L[ℝ] ℝ) (L v)=_
  conv_lhs => rw [cover_decompose v,map_sum,map_sum]
  simp only [map_smul,smul_eq_mul]
  rfl

@[simp] lemma coverTrace_zero : coverTrace 0=0 := by simp [coverTrace]
@[simp] lemma coverTrace_add (L M : Cover →L[ℝ] Cover) :
    coverTrace (L+M)=coverTrace L+coverTrace M := by simp [coverTrace,Finset.sum_add_distrib]
@[simp] lemma coverTrace_smul (a : ℝ) (L : Cover →L[ℝ] Cover) :
    coverTrace (a • L)=a*coverTrace L := by simp [coverTrace,Finset.mul_sum]

def coverTraceCLM : (Cover →L[ℝ] Cover) →L[ℝ] ℝ :=
  ({toFun := coverTrace, map_add' := coverTrace_add,
    map_smul' := by intro a L; exact coverTrace_smul a L} :
      (Cover →L[ℝ] Cover) →ₗ[ℝ] ℝ).toContinuousLinearMap

@[simp] lemma coverTraceCLM_apply (L : Cover →L[ℝ] Cover) : coverTraceCLM L=coverTrace L := rfl

lemma coverTrace_comp_comm (L M : Cover →L[ℝ] Cover) :
    coverTrace (L.comp M)=coverTrace (M.comp L) := by
  simp only [coverTrace,ContinuousLinearMap.comp_apply]
  conv_lhs => enter [2,i]; rw [cover_clm_component]
  conv_rhs => enter [2,i]; rw [cover_clm_component]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma coverTrace_smulRight (l : Cover →L[ℝ] ℝ) (v : Cover) :
    coverTrace (l.smulRight v)=l v := by
  conv_rhs => rw [cover_decompose v]
  simp only [coverTrace,ContinuousLinearMap.smulRight_apply,PiLp.smul_apply,
    smul_eq_mul,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma divergence_eq_coverTrace (F : Cover → Cover) (x : Cover) :
    divergence F x=coverTrace (fderiv ℝ F x) := rfl

def cofactorLinear (L : Cover →L[ℝ] Cover) (n : Cover) : Cover :=
  coverTrace L • n-L.adjoint n

def cofactorQuadratic (L : Cover →L[ℝ] Cover) (n : Cover) : Cover :=
  ((coverTrace L)^2-coverTrace (L.comp L)) • n-
    (2*coverTrace L) • L.adjoint n+2 • L.adjoint (L.adjoint n)

lemma cofactorLinear_add (L M : Cover →L[ℝ] Cover) (n : Cover) :
    cofactorLinear (L+M) n=cofactorLinear L n+cofactorLinear M n := by
  simp only [cofactorLinear,coverTrace_add,map_add,add_apply]
  module

lemma cofactorQuadratic_add (L M : Cover →L[ℝ] Cover) (n : Cover) :
    cofactorQuadratic (L+M) n=cofactorQuadratic L n+cofactorQuadratic M n+
      2 • (cofactorLinear M (cofactorLinear L n)-cofactorLinear (M.comp L) n) := by
  simp only [cofactorQuadratic,cofactorLinear,coverTrace_add,ContinuousLinearMap.add_comp,
    ContinuousLinearMap.comp_add,coverTrace_comp_comm L M,map_add,add_apply,
    ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.comp_apply,map_sub,map_smul]
  module

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_halfspace_L1_tilt_small {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function)
    {n : Cover} (hn : ‖n‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (c : MovingCenter.InteriorCenter) (r : ℝ),
      0 < r → r < η →
      (∫ x in Metric.closedBall (0 : Cover) 1,
        |blowupCharacteristic E c r x-(coverHalfspace n).indicator (fun _ ↦ (1 : ℝ)) x|) < η →
      (∫ z, blowupTilt n z ∂(blowupNormalMeasure μ c r 2 : Measure BlowupNormalBundle)) < ε := by
  by_contra h
  push Not at h
  let d : ℕ → ℝ := fun i ↦ 1/((i : ℝ)+1)
  have hd (i : ℕ) : 0 < d i := by dsimp [d]; positivity
  have hb (i : ℕ) := h (d i) (hd i)
  choose c r hr hrd he ht using hb
  have hdlim : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hrlim : Tendsto r atTop (𝓝 0) :=
    squeeze_zero (fun i ↦ (hr i).le) (fun i ↦ (hrd i).le) hdlim
  have hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (c i) (r i) x-
        (coverHalfspace n).indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0) :=
    squeeze_zero (fun i ↦ integral_nonneg (fun _ ↦ abs_nonneg _))
      (fun i ↦ (he i).le) hdlim
  obtain ⟨ν,k,U,hU,hν,_,hstat⟩ := isMinimizerAt_moving_paired_normal_limit
    hV hE hmin hμ hH c r hr hrlim (measurableSet_coverHalfspace n) hconv
  have hflux (F : Cover → Cover) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
      (hs : tsupport F ⊆ Metric.closedBall (0 : Cover) 1) := (hstat F hF hs).2
  have heq := moving_blowup_perimeter_eq_normal_ball hV hE hmin hμ
    (fun i ↦ c (i+k)) (fun i ↦ r (i+k)) (fun i ↦ hr _)
    ((hrlim.comp (tendsto_add_atTop_nat k)).mono_left hU)
    (measurableSet_coverHalfspace n)
    ((hconv.comp (tendsto_add_atTop_nat k)).mono_left hU) hν hflux
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)
  have hmodel : ∀ᵐ x : Cover ∂volume, x ∈ Metric.ball (0 : Cover) 1 →
      (x ∈ coverHalfspace n ↔ x ∈ coverHalfspace n) := ae_of_all _ (by simp)
  have hmass : (ν : Measure BlowupNormalBundle).real
      {z | z.1 ∈ Metric.ball (0 : Cover) (1/2)} = Real.pi*(1/2)^2 := by
    rw [Measure.real_def,← heq,
      halfspace_model_perimeter_ball (measurableSet_coverHalfspace n) hn hmodel
        (by norm_num) (by norm_num), ENNReal.toReal_ofReal (by positivity)]
  have hflat := flat_set_limit_normal (measurableSet_coverHalfspace n) hn hmodel hmass hflux
  have htilt := flat_moving_normal_tilt_limit
    (fun i ↦ (c (i+k) : Cover)) (fun i ↦ r (i+k)) hν hflat
  obtain ⟨i,hi⟩ := (htilt.eventually (Iio_mem_nhds hε)).exists
  exact (not_lt_of_ge (ht (i+k))) hi

theorem isMinimizerAt_halfspace_L1_normal_charts {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function) :
    ∃ C K ρ δ : ℝ, 0 < C ∧ 0 < K ∧ 0 < ρ ∧ ρ ≤ 1/16 ∧ 0 < δ ∧
      ∀ n : Cover, ‖n‖ = 1 → ∀ e : ℝ, 0 < e → e ≤ δ →
      ∃ η : ℝ, 0 < η ∧ ∀ (c : Cover) (r : ℝ),
        ‖c-cubeCenter‖ ≤ 1/16 → 0 < r → r < η →
        (∫ x in Metric.closedBall (0 : Cover) 1,
          |blowupCharacteristic E c r x-(coverHalfspace n).indicator (fun _ ↦ (1 : ℝ)) x|) < η →
        BoundaryNormalChart E c n (r/272) e C K ρ := by
  obtain ⟨R,C,K,ρ,hR,hC,hK,hρ,hρs,hmod⟩ :=
    MovingCenter.isMinimizerAt_moving_normal_modulus hV hE hmin hcenter
  obtain ⟨N,hN,hp,hu⟩ := normalMeasure_polar_unit hμ
  obtain ⟨δ,hδ,hcharts⟩ := hmod μ hμ N hN hp hu
  refine ⟨C,K,ρ,δ,hC,hK,hρ,hρs,hδ,?_⟩
  intro n hn e he heδ
  obtain ⟨η,hη,hsmall⟩ := isMinimizerAt_halfspace_L1_tilt_small hV hE hmin hμ hH hn
    (show 0 < e^2/272^2 by positivity)
  refine ⟨min η (min (272*R) (min (272*δ*e^2) 1)),by positivity,?_⟩
  intro c r hc hr hrs hL1
  have hrη : r < η := hrs.trans_le (min_le_left _ _)
  have hrR : r/272 ≤ R := by
    have hh := hrs.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hratio : (r/272)/e^2 ≤ δ := by
    apply (div_le_iff₀ (sq_pos_of_pos he)).mpr
    have hh := hrs.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    linarith
  have hr1 : r < 1 := hrs.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  let d : MovingCenter.InteriorCenter := ⟨c,by linarith⟩
  have ht := hsmall d r hr hrη (hL1.trans_le (min_le_left _ _))
  have hchart : Metric.ball c (r/8) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
    Metric.ball_subset_closedBall.trans (MovingCenter.closedBall_interior (c := d) (by linarith))
  have htilt := spatial_tilt_le_blowupTilt hN hp hu c n hr hchart
  have hbound : (∫ x in Metric.closedBall (quotientMap c) (17*(r/272)), ‖N x-n‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r/272)^2*e^2 := by
    rw [show 17*(r/272)=r/16 by ring]
    calc
      _ ≤ _ := htilt
      _ ≤ r^2*(e^2/272^2) := mul_le_mul_of_nonneg_left ht.le (sq_nonneg _)
      _ = _ := by ring
  exact hcharts c hc n (r/272) e hn (div_pos hr (by norm_num)) hrR he heδ hratio hbound

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma localL1_eventually_lt_model {g : ℕ → Cover → ℝ}
    (hg : ∀ i, Measurable (g i)) (hgb : ∀ i x, |g i x| ≤ 1)
    {f F : Cover → ℝ} (hf : Measurable f) (hfb : ∀ x, |f x| ≤ 1)
    (hF : Measurable F) (hFb : ∀ x, |F x| ≤ 1) {R : ℝ} {l : Filter ℕ}
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
      |g i x-f x|) l (𝓝 0)) {η : ℝ}
    (hclose : (∫ x in Metric.closedBall (0 : Cover) R, |f x-F x|) < η) :
    ∀ᶠ i in l, (∫ x in Metric.closedBall (0 : Cover) R, |g i x-F x|) < η := by
  have he := hconv.eventually (Iio_mem_nhds (sub_pos.mpr hclose))
  filter_upwards [he] with i hi
  let m : Measure Cover := volume.restrict (Metric.closedBall (0 : Cover) R)
  have ht := dist_triangle (boundedFunctionL1 m (g i) (hg i) (hgb i))
    (boundedFunctionL1 m f hf hfb) (boundedFunctionL1 m F hF hFb)
  simp only [boundedFunctionL1_dist] at ht
  change (∫ x in Metric.closedBall (0 : Cover) R, |g i x-F x|) ≤
    (∫ x in Metric.closedBall (0 : Cover) R, |g i x-f x|) +
    (∫ x in Metric.closedBall (0 : Cover) R, |f x-F x|) at ht
  linarith

theorem isMinimizerAt_close_limit_fixed_scale_graphs {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function)
    {n : Cover} (hn : ‖n‖ = 1) :
    ∃ η : ℝ, 0 < η ∧
      ∀ (c : ℕ → MovingCenter.InteriorCenter) (r : ℕ → ℝ),
        (∀ i, 0 < r i) → Tendsto r atTop (𝓝 0) →
        (∀ᶠ i in atTop, ‖(c i : Cover)-cubeCenter‖ ≤ 1/32) →
      ∀ A : Set Cover, MeasurableSet A →
        Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
          |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
          atTop (𝓝 0) →
        (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
          0 < volume.real (A ∩ Metric.ball (0 : Cover) ρ) ∧
          0 < volume.real (Aᶜ ∩ Metric.ball (0 : Cover) ρ)) →
        (∫ x in Metric.closedBall (0 : Cover) 1,
          |A.indicator (fun _ ↦ (1 : ℝ)) x-
            (coverHalfspace n).indicator (fun _ ↦ (1 : ℝ)) x|) < η →
        ∀ᶠ i in atTop, ∃ a : Cover, dist a (c i : Cover) < r i/(544*4096) ∧
          ∃ g : Plane → ℝ, LipschitzWith (1/4) g ∧
            ContDiffOn ℝ 1 g (Metric.ball 0 ((r i/544)/1024)) ∧
            (∀ y ∈ Metric.ball (0 : Plane) ((r i/544)/1024),
              quotientMap a+quotientMap (normalGraph n g y) ∈ frontier (openRepresentative E) ∧
              ‖normalGraph n g y‖ < (r i/544)/512) ∧
            (∀ x ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball a ((r i/544)/128),
              normalGraph n g (normalPlaneCoordinates n (x-a)) = x-a) := by
  obtain ⟨R,hR,hgraphs⟩ := MovingCenter.isMinimizerAt_moving_C1_graph hV hE hmin hcenter
  obtain ⟨N,hN,hp,hu⟩ := normalMeasure_polar_unit hμ
  obtain ⟨δ,hδ,hgraph⟩ := hgraphs μ hμ N hN hp hu
  let e := δ/2
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨η,hη,hsmall⟩ := isMinimizerAt_halfspace_L1_tilt_small hV hE hmin hμ hH hn
    (show 0 < e^2/544^2 by positivity)
  refine ⟨η,hη,?_⟩
  intro c r hr hrlim hc A hA hconv hphases hclose
  have hpositive : 0 < min η (min (544*R) (min (544*δ*e^2) (1/32))) := by positivity
  have hs := hrlim.eventually (Iio_mem_nhds hpositive)
  have hL1 := localL1_eventually_lt_model
    (fun i ↦ measurable_blowupCharacteristic hE (c i) (r i))
    (fun i ↦ blowupCharacteristic_bound E (c i) (r i))
    (measurable_const.indicator hA) (cover_indicator_bound A)
    (measurable_const.indicator (measurableSet_coverHalfspace n))
    (cover_indicator_bound (coverHalfspace n)) hconv hclose
  have hpoints := isMinimizerAt_moving_frontier_approximation hV hE hmin c r hr hrlim hA hconv
    (by norm_num : (0:ℝ) < 1/(544*4096)) (by norm_num : (1:ℝ)/(544*4096) ≤ 1)
    (hphases _ (by norm_num) (by norm_num))
  filter_upwards [hc,hs,hL1,hpoints] with i hci hri hL1i hpoint
  have hrη : r i < η := hri.trans_le (min_le_left _ _)
  have hri' := hri.trans_le (min_le_right _ _)
  have hti := hsmall (c i) (r i) (hr i) hrη hL1i
  obtain ⟨a,ha,hbase⟩ := hpoint
  have had : dist a (c i : Cover) < r i/(544*4096) := by
    simpa only [Metric.mem_ball,div_eq_mul_inv,one_mul] using ha
  have hrR : r i/544 ≤ R := by have hh := hri'.trans_le (min_le_left _ _); linarith
  have hrsmall : r i < 1/32 := hri'.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hratio : (r i/544)/e^2 ≤ δ := by
    apply (div_le_iff₀ (sq_pos_of_pos he)).mpr
    have hh := hri'.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hnear : ‖a-cubeCenter‖ ≤ 1/16 := by
    have hh := dist_triangle a (c i : Cover) cubeCenter
    simp only [dist_eq_norm] at hh had
    linarith
  have hchart : Metric.ball (c i : Cover) (r i/8) ⊆ {x | ∀ j, 0 < x j ∧ x j < 1} :=
    Metric.ball_subset_closedBall.trans (MovingCenter.closedBall_interior (by linarith : r i/8 < 3/8))
  have htilt := spatial_tilt_le_blowupTilt hN hp hu (c i) n (hr i) hchart
  have hadq : dist (quotientMap a) (quotientMap (c i)) < r i/(544*4096) := by
    rw [dist_eq_norm,← quotientMap_sub]
    exact (norm_quotientMap_le _).trans_lt (by simpa only [dist_eq_norm] using had)
  have hsub : Metric.closedBall (quotientMap a) (17*(r i/544)) ⊆
      Metric.closedBall (quotientMap (c i)) (r i/16) := by
    intro x hx
    have hx' : dist x (quotientMap a) ≤ 17*(r i/544) := hx
    have hh := dist_triangle x (quotientMap a) (quotientMap (c i))
    change dist x (quotientMap (c i)) ≤ r i/16
    linarith [hr i]
  have hbound : (∫ x in Metric.closedBall (quotientMap a) (17*(r i/544)), ‖N x-n‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i/544)^2*e^2 := by
    calc
      _ ≤ (∫ x in Metric.closedBall (quotientMap (c i)) (r i/16), ‖N x-n‖^2
        ∂(spatialNormalMeasure μ : Measure Torus)) := setIntegral_mono_set
          (polar_tilt_integrable hN hu n).integrableOn (Eventually.of_forall fun _ ↦ sq_nonneg _) hsub.eventuallyLE
      _ ≤ _ := htilt
      _ ≤ (r i)^2*(e^2/544^2) := mul_le_mul_of_nonneg_left hti.le (sq_nonneg _)
      _ = _ := by ring
  exact ⟨a,had,hgraph a hnear hbase n (r i/544) e hn (div_pos (hr i) (by norm_num))
    hrR he (by dsimp [e]; linarith) hratio hbound⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_close_limit_fixed_scale_normals {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function) :
    ∃ C K ρ δ : ℝ, 0 < C ∧ 0 < K ∧ 0 < ρ ∧ ρ ≤ 1/16 ∧ 0 < δ ∧
      ∀ n : Cover, ‖n‖ = 1 → ∀ e : ℝ, 0 < e → e ≤ δ →
      ∃ η : ℝ, 0 < η ∧
      ∀ (c : ℕ → Cover) (r : ℕ → ℝ), (∀ i, 0 < r i) → Tendsto r atTop (𝓝 0) →
        (∀ᶠ i in atTop, ‖c i-cubeCenter‖ ≤ 1/16) →
      ∀ A : Set Cover, MeasurableSet A →
        Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
          |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
          atTop (𝓝 0) →
        (∫ x in Metric.closedBall (0 : Cover) 1,
          |A.indicator (fun _ ↦ (1 : ℝ)) x-
            (coverHalfspace n).indicator (fun _ ↦ (1 : ℝ)) x|) < η →
        ∀ᶠ i in atTop, BoundaryNormalChart E (c i) n (r i/272) e C K ρ := by
  obtain ⟨C,K,ρ,δ,hC,hK,hρ,hρs,hδ,hcharts⟩ :=
    isMinimizerAt_halfspace_L1_normal_charts hV hE hmin hcenter hμ hH
  refine ⟨C,K,ρ,δ,hC,hK,hρ,hρs,hδ,?_⟩
  intro n hn e he heδ
  obtain ⟨η,hη,hsmall⟩ := hcharts n hn e he heδ
  refine ⟨η,hη,?_⟩
  intro c r hr hrlim hc A hA hconv hclose
  have hs := hrlim.eventually (Iio_mem_nhds hη)
  have hL1 := localL1_eventually_lt_model
    (fun i ↦ measurable_blowupCharacteristic hE (c i) (r i))
    (fun i ↦ blowupCharacteristic_bound E (c i) (r i))
    (measurable_const.indicator hA) (cover_indicator_bound A)
    (measurable_const.indicator (measurableSet_coverHalfspace n))
    (cover_indicator_bound (coverHalfspace n)) hconv hclose
  filter_upwards [hc,hs,hL1] with i hci hri hL1i
  exact hsmall (c i) (r i) hci (hr i) hri hL1i

lemma ae_closedBall_imp_of_ae_ball {P : Cover → Prop} {a : Cover} {r : ℝ}
    (h : ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball a r → P x) :
    ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.closedBall a r → P x := by
  have hz : ∀ᵐ x ∂(volume : Measure Cover), x ∉ Metric.sphere a r := by
    rw [ae_iff]
    simpa only [not_not,Metric.sphere,dist_eq_norm,Set.mem_ofPred_eq] using Measure.addHaar_sphere (volume : Measure Cover) a r
  filter_upwards [h,hz] with x hx hxz hxc
  apply hx
  have hh : dist x a ≤ r := hxc
  have hn : dist x a ≠ r := hxz
  exact lt_of_le_of_ne hh hn

lemma localL1_limit_congr_ae_ball {g : ℕ → Cover → ℝ} {f F : Cover → ℝ}
    {R : ℝ} {l : Filter ℕ}
    (heq : ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) R → f x = F x)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R, |g i x-f x|) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R, |g i x-F x|) l (𝓝 0) := by
  have hh := ae_closedBall_imp_of_ae_ball heq
  have he (i : ℕ) : (∫ x in Metric.closedBall (0 : Cover) R, |g i x-f x|) =
      ∫ x in Metric.closedBall (0 : Cover) R, |g i x-F x| := by
    apply setIntegral_congr_ae Metric.isClosed_closedBall.measurableSet
    filter_upwards [hh] with x hx hxb
    rw [hx hxb]
  simpa only [he] using hconv

lemma volume_real_affine_preimage_ball {A : Set Cover} (hA : MeasurableSet A)
    (p : Cover) {s : ℝ} (hs : 0 < s) (ρ : ℝ) :
    volume.real (((fun x ↦ p+s • x) ⁻¹' A) ∩ Metric.ball (0 : Cover) ρ) =
      s⁻¹^3*volume.real (A ∩ Metric.ball p (s*ρ)) := by
  have he (D : Set Cover) (hD : MeasurableSet D) (a : Cover) (r : ℝ) :
      (∫ x in Metric.ball a r, D.indicator (fun _ ↦ (1 : ℝ)) x) =
        volume.real (D ∩ Metric.ball a r) := by
    rw [integral_indicator hD,Measure.restrict_restrict hD,integral_const,smul_eq_mul,mul_one,
      Measure.real_def,Measure.restrict_apply_univ]
    rfl
  have hD : MeasurableSet ((fun x : Cover ↦ p+s • x) ⁻¹' A) :=
    hA.preimage (by fun_prop)
  rw [← he A hA p,← he _ hD 0]
  rw [integral_ball_affine_scaling _ p hs ρ]
  have hh (x : Cover) : ((fun x ↦ p+s • x) ⁻¹' A).indicator (fun _ ↦ (1 : ℝ)) x =
      A.indicator (fun _ ↦ (1 : ℝ)) (p+s • x) := rfl
  simp only [hh]
  field_simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def ActualBoundaryGraph (E : Set Torus) (c n : Cover) (q : ℝ) : Prop :=
  ∃ a : Cover, dist a c < q/(544*4096) ∧
    ∃ g : Plane → ℝ, LipschitzWith (1/4) g ∧
      ContDiffOn ℝ 1 g (Metric.ball 0 ((q/544)/1024)) ∧
      (∀ y ∈ Metric.ball (0 : Plane) ((q/544)/1024),
        quotientMap a+quotientMap (normalGraph n g y) ∈ frontier (openRepresentative E) ∧
        ‖normalGraph n g y‖ < (q/544)/512) ∧
      (∀ x ∈ quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball a ((q/544)/128),
        normalGraph n g (normalPlaneCoordinates n (x-a)) = x-a)

theorem actual_primary_fixed_scale_packets {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function) :
    ∃ C K ρ δ : ℝ, 0 < C ∧ 0 < K ∧ 0 < ρ ∧ ρ ≤ 1/16 ∧ 0 < δ ∧
      ∀ n : Cover, ‖n‖ = 1 → ∀ e : ℝ, 0 < e → e ≤ δ →
      ∃ η : ℝ, 0 < η ∧
      ∀ (r : ℕ → ℝ), (∀ i, 0 < r i) → Tendsto r atTop (𝓝 0) →
      ∀ A : Set Cover, MeasurableSet A →
        Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
          |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
          atTop (𝓝 0) →
      ∀ p : Cover, ‖p‖ < 1 →
        (∀ t : ℝ, 0 < t → 0 < volume.real (A ∩ Metric.ball p t) ∧
          0 < volume.real (Aᶜ ∩ Metric.ball p t)) →
      ∀ s : ℝ, 0 < s → s ≤ 1 →
        (∫ x in Metric.closedBall (0 : Cover) 1,
          |A.indicator (fun _ ↦ (1 : ℝ)) (p+s • x)-
            (coverHalfspace n).indicator (fun _ ↦ (1 : ℝ)) x|) < η →
      ∀ᶠ i in atTop,
        ActualBoundaryGraph E (cubeCenter+r i • p) n (r i*s) ∧
        BoundaryNormalChart E (cubeCenter+r i • p) n ((r i*s)/272) e C K ρ := by
  obtain ⟨C,K,ρ,δ,hC,hK,hρ,hρs,hδ,hnormals⟩ :=
    isMinimizerAt_close_limit_fixed_scale_normals hV hE hmin hcenter hμ hH
  refine ⟨C,K,ρ,δ,hC,hK,hρ,hρs,hδ,?_⟩
  intro n hn e he heδ
  obtain ⟨ηN,hηN,hN⟩ := hnormals n hn e he heδ
  obtain ⟨ηG,hηG,hG⟩ := isMinimizerAt_close_limit_fixed_scale_graphs hV hE hmin hcenter hμ hH hn
  refine ⟨min ηN ηG,lt_min hηN hηG,?_⟩
  intro r hr hrlim A hA hconv p hp hboundary s hs hs1 hclose
  obtain ⟨k,hk⟩ := eventually_atTop.mp (hrlim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/32)))
  let c : ℕ → MovingCenter.InteriorCenter := fun i ↦ ⟨cubeCenter+r (i+k) • p,by
    simp only [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg (hr _).le]
    have hh := hk (i+k) (by omega)
    nlinarith [hr (i+k)]⟩
  let q : ℕ → ℝ := fun i ↦ r (i+k)*s
  have hq : ∀ i, 0 < q i := fun i ↦ mul_pos (hr _) hs
  have hqlim : Tendsto q atTop (𝓝 0) := by
    simpa only [q,Function.comp_def,zero_mul] using (hrlim.comp (tendsto_add_atTop_nat k)).mul_const s
  have hc (i : ℕ) : ‖(c i : Cover)-cubeCenter‖ ≤ 1/32 := by
    change ‖cubeCenter+r (i+k) • p-cubeCenter‖ ≤ 1/32
    rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg (hr _).le]
    have hh := hk (i+k) (by omega)
    nlinarith [hr (i+k)]
  let D : Set Cover := (fun x ↦ p+s • x) ⁻¹' A
  have hD : MeasurableSet D := hA.preimage (by fun_prop)
  have hsub : Metric.closedBall p (s*1) ⊆ Metric.closedBall (0 : Cover) 2 := by
    intro x hx
    have hx' : ‖x-p‖ ≤ s := by simpa only [Metric.mem_closedBall,dist_eq_norm,mul_one] using hx
    have hh := norm_add_le (x-p) p
    rw [sub_add_cancel] at hh
    simpa only [Metric.mem_closedBall,dist_zero_right] using (by linarith : ‖x‖ ≤ 2)
  have hshift := localL1_affine_tendsto
    (fun i ↦ measurable_blowupCharacteristic hE cubeCenter (r i))
    (fun i ↦ blowupCharacteristic_bound E cubeCenter (r i))
    (measurable_const.indicator hA) (cover_indicator_bound A) hconv p hs hsub
  have hlim : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (c i) (q i) x-D.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0) := by
    have hh := hshift.comp (tendsto_add_atTop_nat k)
    convert hh using 2
    rename_i i
    apply integral_congr_ae
    apply ae_of_all
    intro x
    change |blowupCharacteristic E (cubeCenter+r (i+k) • p) (r (i+k)*s) x-
      D.indicator (fun _ ↦ (1 : ℝ)) x| =
      |blowupCharacteristic E cubeCenter (r (i+k)) (p+s • x)-
        A.indicator (fun _ ↦ (1 : ℝ)) (p+s • x)|
    rw [blowupCharacteristic_affine]
    rfl
  have hphases (t : ℝ) (ht : 0 < t) (_ : t ≤ 1) :
      0 < volume.real (D ∩ Metric.ball (0 : Cover) t) ∧
      0 < volume.real (Dᶜ ∩ Metric.ball (0 : Cover) t) := by
    have hh := hboundary (s*t) (mul_pos hs ht)
    change 0 < volume.real (((fun x ↦ p+s • x) ⁻¹' A) ∩ Metric.ball (0 : Cover) t) ∧
      0 < volume.real (((fun x ↦ p+s • x) ⁻¹' Aᶜ) ∩ Metric.ball (0 : Cover) t)
    rw [volume_real_affine_preimage_ball hA p hs,volume_real_affine_preimage_ball hA.compl p hs]
    exact ⟨mul_pos (by positivity) hh.1,mul_pos (by positivity) hh.2⟩
  have hclose' : (∫ x in Metric.closedBall (0 : Cover) 1,
      |D.indicator (fun _ ↦ (1 : ℝ)) x-(coverHalfspace n).indicator (fun _ ↦ (1 : ℝ)) x|) < min ηN ηG := hclose
  have hgg := hG c q hq hqlim (Eventually.of_forall hc) D hD hlim hphases
    (hclose'.trans_le (min_le_right _ _))
  have hnn := hN (fun i ↦ (c i : Cover)) q hq hqlim
    (Eventually.of_forall (fun i ↦ (hc i).trans (by norm_num : (1:ℝ)/32 ≤ 1/16))) D hD hlim
    (hclose'.trans_le (min_le_left _ _))
  have hall : ∀ᶠ i in atTop,
      ActualBoundaryGraph E (cubeCenter+r (i+k) • p) n (r (i+k)*s) ∧
      BoundaryNormalChart E (cubeCenter+r (i+k) • p) n ((r (i+k)*s)/272) e C K ρ := by
    filter_upwards [hgg,hnn] with i hgi hni
    exact ⟨hgi,hni⟩
  obtain ⟨j,hj⟩ := eventually_atTop.mp hall
  refine eventually_atTop.mpr ⟨j+k,?_⟩
  intro i hi
  have hh := hj (i-k) (by omega)
  simpa only [Nat.sub_add_cancel (by omega : k ≤ i)] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma exists_uniform_subseq_of_bounded_modulus {X Y : Type*}
    [PseudoMetricSpace X] [CompactSpace X] [MetricSpace Y] [ProperSpace Y]
    (f : ℕ → X → Y) (hc : ∀ i, Continuous (f i)) (y₀ : Y) (M : ℝ)
    (hb : ∀ i x, dist (f i x) y₀ ≤ M)
    (hm : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ i x y, dist x y < η → dist (f i x) (f i y) < ε) :
    ∃ (g : X → Y) (φ : ℕ → ℕ), Continuous g ∧ StrictMono φ ∧
      TendstoUniformly (fun i ↦ f (φ i)) g atTop := by
  let F : ℕ → BoundedContinuousFunction X Y := fun i ↦
    BoundedContinuousFunction.mkOfCompact ⟨f i,hc i⟩
  have heq : Equicontinuous ((↑) : range F → X → Y) := by
    apply UniformEquicontinuous.equicontinuous
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    obtain ⟨η,hη,hηm⟩ := hm ε hε
    refine ⟨η,hη,?_⟩
    intro x y hxy
    rintro ⟨_,i,rfl⟩
    exact hηm i x y hxy
  have hcpt := BoundedContinuousFunction.arzela_ascoli
    (Metric.closedBall y₀ M) (isCompact_closedBall y₀ M) (range F)
    (by rintro _ x ⟨i,rfl⟩; exact hb i x) heq
  obtain ⟨g,_,φ,hφ,hconv⟩ := hcpt.tendsto_subseq (fun i ↦ subset_closure (mem_range_self i))
  exact ⟨g,φ,g.continuous,hφ,BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hconv⟩

def normalGraphDerivative (n ν : Cover) : Plane →L[ℝ] ℝ :=
  (⟪ν,n⟫)⁻¹ • (-((innerSL ℝ ν).comp (normalPlaneLinearIsometry n).toContinuousLinearMap))

lemma transverse_inner_lower {n ν : Cover} (hn : ‖n‖ = 1) (hν : ‖n-ν‖ ≤ 1/2) :
    1/2 ≤ ⟪ν,n⟫ := by
  have hh := abs_real_inner_le_norm (n-ν) n
  rw [inner_sub_left,real_inner_self_eq_norm_sq,hn,mul_one] at hh
  have hl := (abs_le.mp hh).2
  norm_num at hl
  linarith

lemma normalGraphDerivative_continuousOn {n : Cover} (hn : ‖n‖ = 1) :
    ContinuousOn (normalGraphDerivative n) (Metric.closedBall n (1/2)) := by
  have hi : ContinuousOn (fun ν : Cover ↦ (⟪ν,n⟫)⁻¹) (Metric.closedBall n (1/2)) := by
    apply (continuous_id.inner continuous_const).continuousOn.inv₀
    intro ν hν
    have hnorm : ‖n-ν‖ ≤ 1/2 := by simpa only [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev] using hν
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (transverse_inner_lower hn hnorm))
  exact hi.smul ((((innerSL ℝ).continuous.continuousOn).clm_comp continuousOn_const).neg)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def rescaledActualBoundary (E : Set Torus) (c : Cover) (q : ℝ) : Set Cover :=
  (fun x ↦ quotientMap (c+q • x)) ⁻¹' frontier (openRepresentative E)

end CubicTorus
end
end
end

end OAI
