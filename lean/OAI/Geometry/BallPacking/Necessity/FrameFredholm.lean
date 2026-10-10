import Mathlib
import OAI.Geometry.BallPacking.Fredholm.FiniteExtensions
import OAI.Geometry.BallPacking.Necessity.HolderCompactness
import OAI.Geometry.BallPacking.Necessity.MarkedInverse

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

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
section
universe v
variable {E F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
local instance : NormedAddCommGroup (HolderSpace ℂ E ((1:ℝ)/3)) := inferInstance
local instance : NormedSpace ℝ (HolderSpace ℂ E ((1:ℝ)/3)) := inferInstance
local instance : NormedAddCommGroup (HolderSpace ℂ (E →L[ℝ] F) ((1:ℝ)/3)) := inferInstance
local instance : NormedSpace ℝ (HolderSpace ℂ (E →L[ℝ] F) ((1:ℝ)/3)) := inferInstance
local instance : NormedAddCommGroup (C1HolderSpace E ((1:ℝ)/3)) := inferInstance
local instance : NormedSpace ℝ (C1HolderSpace E ((1:ℝ)/3)) := inferInstance
local instance : NormedAddCommGroup (HolderSpace ℂ F ((1:ℝ)/3)) := inferInstance
local instance : NormedSpace ℝ (HolderSpace ℂ F ((1:ℝ)/3)) := inferInstance

lemma c1HolderValue_bound (α : ℝ) (u : C1HolderSpace E α) (x : ℂ) :
    ‖holderValue α (c1HolderValue α u) x‖ ≤ ‖u‖ :=
  ((holderValue α (c1HolderValue α u)).norm_coe_le_norm x).trans
    ((le_max_left _ _).trans (le_max_left _ _))

lemma c1HolderDeriv_bound (α : ℝ) (u : C1HolderSpace E α) (x : ℂ) :
    ‖holderValue α (c1HolderDeriv α u) x‖ ≤ ‖u‖ :=
  ((holderValue α (c1HolderDeriv α u)).norm_coe_le_norm x).trans
    ((le_max_left _ _).trans (le_max_right _ _))

lemma c1HolderValue_lipschitz (α : ℝ) (u : C1HolderSpace E α) :
    LipschitzWith ‖u‖₊ (holderValue α (c1HolderValue α u)) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (fun x => (c1Holder_hasFDerivAt α u x).differentiableAt)
  intro x
  rw [c1Holder_fderiv]
  exact_mod_cast c1HolderDeriv_bound α u x

def c1LowerOrderCLM (M : HolderSpace ℂ (E →L[ℝ] F) ((1:ℝ)/3)) :
    C1HolderSpace E ((1:ℝ)/3) →L[ℝ] HolderSpace ℂ F ((1:ℝ)/3) :=
  (holderCLM ((1:ℝ)/3) M).comp (c1HolderValue ((1:ℝ)/3))

@[simp] lemma c1LowerOrderCLM_value (M : HolderSpace ℂ (E →L[ℝ] F) ((1:ℝ)/3))
    (u : C1HolderSpace E ((1:ℝ)/3)) (x : ℂ) :
    holderValue ((1:ℝ)/3) (c1LowerOrderCLM M u) x =
      holderValue ((1:ℝ)/3) M x (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u) x) := rfl

lemma c1LowerOrder_image_lipschitz (M : HolderSpace ℂ (E →L[ℝ] F) ((1:ℝ)/3))
    (L : NNReal) (hL : LipschitzWith L (holderValue ((1:ℝ)/3) M))
    (u : C1HolderSpace E ((1:ℝ)/3)) (hu : ‖u‖ ≤ 1) :
    LipschitzWith (‖M‖₊+L) (holderValue ((1:ℝ)/3) (c1LowerOrderCLM M u)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let f := holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) u)
  let A := holderValue ((1:ℝ)/3) M
  have hMx : ‖A x‖≤‖M‖ := (A.norm_coe_le_norm x).trans (holderValue_norm _ M)
  have huy : ‖f y‖≤1 := (c1HolderValue_bound _ u y).trans hu
  have hfv : ‖f x-f y‖≤dist x y := by
    have hf : ‖f x-f y‖≤‖u‖*dist x y := by
      simpa only [f,dist_eq_norm,coe_nnnorm] using (c1HolderValue_lipschitz _ u).norm_sub_le x y
    calc
      ‖f x-f y‖ ≤ ‖u‖*dist x y := hf
      _ ≤ 1*dist x y := mul_le_mul_of_nonneg_right hu dist_nonneg
      _ = dist x y := one_mul _
  have hAv : ‖A x-A y‖≤(L:ℝ)*dist x y := by
    simpa only [A,dist_eq_norm] using hL.norm_sub_le x y
  rw [dist_eq_norm]
  change ‖A x (f x)-A y (f y)‖≤(↑(‖M‖₊+L):ℝ)*dist x y
  have he : A x (f x)-A y (f y) = A x (f x-f y)+(A x-A y) (f y) := by
    simp only [map_sub,sub_apply]
    abel
  rw [he,NNReal.coe_add]
  exact (norm_add_le _ _).trans ((add_le_add
    ((A x).le_opNorm _ |>.trans (mul_le_mul hMx hfv (norm_nonneg _) (norm_nonneg _)))
    ((A x-A y).le_opNorm _ |>.trans (mul_le_mul hAv huy (norm_nonneg _) (by positivity)))).trans_eq
    (by simp only [mul_one,coe_nnnorm];ring))

lemma c1LowerOrderCLM_compact [ProperSpace F] [CompleteSpace F]
    (R : ℝ) (M : HolderSpace ℂ (E →L[ℝ] F) ((1:ℝ)/3))
    (hs : ∀ x : ℂ, R < ‖x‖ → holderValue ((1:ℝ)/3) M x=0)
    (L : NNReal) (hL : LipschitzWith L (holderValue ((1:ℝ)/3) M)) :
    IsCompactOperator (c1LowerOrderCLM M) := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall (c1LowerOrderCLM M).toLinearMap
    (by norm_num : (0:ℝ)<1)).mpr
  apply (holderLipschitzSet_isCompact_closure R ‖M‖ (‖M‖₊+L)).of_isClosed_subset isClosed_closure
  apply closure_mono
  rintro v ⟨u,hu,rfl⟩
  have hu' : ‖u‖≤1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hu
  refine ⟨?_,?_,c1LowerOrder_image_lipschitz M L hL u hu'⟩
  · intro x hx
    change holderValue ((1:ℝ)/3) (c1LowerOrderCLM M u) x=0
    rw [c1LowerOrderCLM_value,hs x hx,zero_apply]
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg M)).mpr
    intro x
    change ‖holderValue ((1:ℝ)/3) (c1LowerOrderCLM M u) x‖≤‖M‖
    rw [c1LowerOrderCLM_value]
    exact ((holderValue ((1:ℝ)/3) M x).le_opNorm _).trans
      ((mul_le_mul ((holderValue ((1:ℝ)/3) M).norm_coe_le_norm x |>.trans
        (holderValue_norm _ M)) ((c1HolderValue_bound _ u x).trans hu')
          (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_one _))

end

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
section
universe v
variable {E X : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
local instance : NormedAddCommGroup (HolderSpace ℂ E ((1:ℝ)/3)) := inferInstance
local instance : NormedSpace ℝ (HolderSpace ℂ E ((1:ℝ)/3)) := inferInstance
local instance : NormedAddCommGroup (HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) := inferInstance
local instance : NormedSpace ℝ (HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) := inferInstance
local instance : NormedAddCommGroup (C1HolderSpace E ((1:ℝ)/3)) := inferInstance
local instance : NormedSpace ℝ (C1HolderSpace E ((1:ℝ)/3)) := inferInstance

 
def holderConstantCLM (α : ℝ) : E →L[ℝ] HolderSpace ℂ E α :=
  LinearMap.mkContinuous
    { toFun := fun c => ⟨(BoundedContinuousFunction.const ℂ c,0),by intro z;simp⟩
      map_add' := fun c d => by apply holderValue_injective α; ext z; rfl
      map_smul' := fun c d => by apply holderValue_injective α; ext z; rfl }
    1 (fun c => by
      change max ‖BoundedContinuousFunction.const ℂ c‖ ‖(0 : OffDiagonal ℂ →ᵇ E)‖ ≤ 1*‖c‖
      rw [norm_zero,one_mul]
      exact max_le (BoundedContinuousFunction.norm_const_le c) (norm_nonneg c))

omit [CompleteSpace E] in
@[simp] lemma holderConstantCLM_value (α : ℝ) (c : E) (z : ℂ) :
    holderValue α (holderConstantCLM α c) z=c := rfl

def c1HolderEval (α : ℝ) (z : ℂ) : C1HolderSpace E α →L[ℝ] E :=
  (BoundedContinuousFunction.evalCLM ℝ z).comp ((holderValue α).comp (c1HolderValue α))

@[simp] lemma c1HolderEval_apply (α : ℝ) (z : ℂ) (u : C1HolderSpace E α) :
    c1HolderEval α z u=holderValue α (c1HolderValue α u) z := rfl

 

def markedLowerOrderAmbient (C : X →L[ℝ] C1HolderSpace E ((1:ℝ)/3))
    (M N : HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) :
    X →L[ℝ] HolderSpace ℂ E ((1:ℝ)/3) :=
  (c1LowerOrderCLM M).comp C -
    ((holderCLM ((1:ℝ)/3) M).comp (holderConstantCLM ((1:ℝ)/3))).comp
      ((c1HolderEval ((1:ℝ)/3) 0).comp C) -
    ((holderCLM ((1:ℝ)/3) N).comp (holderConstantCLM ((1:ℝ)/3))).comp
      (((c1HolderEval ((1:ℝ)/3) 1).comp C)-((c1HolderEval ((1:ℝ)/3) 0).comp C))

@[simp] lemma markedLowerOrderAmbient_value
    (C : X →L[ℝ] C1HolderSpace E ((1:ℝ)/3))
    (M N : HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) (g : X) (z : ℂ) :
    holderValue ((1:ℝ)/3) (markedLowerOrderAmbient C M N g) z =
      holderValue ((1:ℝ)/3) M z (c1HolderEval ((1:ℝ)/3) z (C g)) -
      holderValue ((1:ℝ)/3) M z (c1HolderEval ((1:ℝ)/3) 0 (C g)) -
      holderValue ((1:ℝ)/3) N z
        (c1HolderEval ((1:ℝ)/3) 1 (C g)-c1HolderEval ((1:ℝ)/3) 0 (C g)) := by
  rfl

lemma markedLowerOrderAmbient_compact [FiniteDimensional ℝ E]
    (C : X →L[ℝ] C1HolderSpace E ((1:ℝ)/3))
    (R : ℝ) (M N : HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3))
    (hs : ∀ x : ℂ, R < ‖x‖ → holderValue ((1:ℝ)/3) M x=0)
    (L : NNReal) (hL : LipschitzWith L (holderValue ((1:ℝ)/3) M)) :
    IsCompactOperator (markedLowerOrderAmbient C M N) := by
  have h₁ := (c1LowerOrderCLM_compact R M hs L hL).comp_clm C
  have h₂ := (isCompactOperator_of_locallyCompactSpace_rng
    ((holderCLM ((1:ℝ)/3) M).comp (holderConstantCLM ((1:ℝ)/3)))).comp_clm
      ((c1HolderEval ((1:ℝ)/3) 0).comp C)
  have h₃ := (isCompactOperator_of_locallyCompactSpace_rng
    ((holderCLM ((1:ℝ)/3) N).comp (holderConstantCLM ((1:ℝ)/3)))).comp_clm
      (((c1HolderEval ((1:ℝ)/3) 1).comp C)-((c1HolderEval ((1:ℝ)/3) 0).comp C))
  exact (h₁.sub h₂).sub h₃

end

 

section
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
universe u v
variable {K : Type u} [MetricSpace K]
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
local instance (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G] (α : ℝ) :
    NormedAddCommGroup (HolderSpace K G α) := inferInstance
local instance (G : Type) [NormedAddCommGroup G] [NormedSpace ℝ G] (α : ℝ) :
    NormedSpace ℝ (HolderSpace K G α) := inferInstance

omit [NormedSpace ℝ E] in
theorem boundedLipschitz_holder_estimate (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : K →ᵇ E) {L : NNReal} (hf : LipschitzWith L f) (x y : K) :
    ‖f x-f y‖ ≤ ((L:ℝ)+2*‖f‖)*(dist x y)^α := by
  by_cases hd : dist x y ≤ 1
  · have h := hf.dist_le_mul x y
    rw [dist_eq_norm] at h
    exact h.trans ((mul_le_mul_of_nonneg_left
      (Real.self_le_rpow_of_le_one dist_nonneg hd hα₁) L.coe_nonneg).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (Real.rpow_nonneg dist_nonneg α)))
  · have hr : 1≤(dist x y)^α := Real.one_le_rpow (le_of_not_ge hd) hα₀
    have hb : ‖f x-f y‖ ≤ 2*‖f‖ :=
      (norm_sub_le _ _).trans ((add_le_add (f.norm_coe_le_norm x) (f.norm_coe_le_norm y)).trans_eq (by ring))
    calc
      ‖f x-f y‖ ≤ 2*‖f‖ := hb
      _ ≤ (2*‖f‖)*(dist x y)^α := le_mul_of_one_le_right (by positivity) hr
      _ ≤ ((L:ℝ)+2*‖f‖)*(dist x y)^α :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left L.coe_nonneg) (Real.rpow_nonneg dist_nonneg α)

def holderOfLipschitz (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : K →ᵇ E) {L : NNReal} (hf : LipschitzWith L f) : HolderSpace K E α :=
  holderSpaceMk α f ((L:ℝ)+2*‖f‖) (by positivity)
    (boundedLipschitz_holder_estimate α hα₀ hα₁ f hf)

@[simp] theorem holderOfLipschitz_apply (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : K →ᵇ E) {L : NNReal} (hf : LipschitzWith L f) (x : K) :
    holderValue α (holderOfLipschitz α hα₀ hα₁ f hf) x = f x := rfl

def compactSmoothHolder (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) : HolderSpace E F α :=
  holderOfLipschitz α hα₀ hα₁ (compactCoefficient f hf.continuous hc)
    (Classical.choose_spec (ContDiff.lipschitzWith_of_hasCompactSupport hc hf (by simp)))

@[simp] theorem compactSmoothHolder_apply (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (x : E) :
    holderValue α (compactSmoothHolder α hα₀ hα₁ f hf hc) x = f x := rfl

end

 

 

open Set Function Filter Topology

 

 

open Set Function Filter Topology
open scoped NNReal

 

 

open scoped NNReal
open Set Function Filter Topology

 

 

open Set Function Filter Topology

 

 

open Set Function Filter Topology

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance : NormedAddCommGroup (HolderSpace ℂ E ((1:ℝ)/3)) := inferInstance
local instance : NormedSpace ℝ (HolderSpace ℂ E ((1:ℝ)/3)) := inferInstance
local instance : NormedAddCommGroup (HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) := inferInstance
local instance : NormedSpace ℝ (HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) := inferInstance
local instance : NormedAddCommGroup (C1HolderSpace E ((1:ℝ)/3)) := inferInstance
local instance : NormedSpace ℝ (C1HolderSpace E ((1:ℝ)/3)) := inferInstance
local instance (R : ℝ) : NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance (R : ℝ) : NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

 

def smoothHolderField (M : ℂ → E →L[ℝ] E) (hs : ContDiff ℝ ∞ M) (hc : HasCompactSupport M) :
    HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3) :=
  compactSmoothHolder ((1:ℝ)/3) (by norm_num) (by norm_num) M hs hc

omit [CompleteSpace E] in
@[simp] lemma smoothHolderField_value
    (M : ℂ → E →L[ℝ] E) (hs : ContDiff ℝ ∞ M) (hc : HasCompactSupport M) (z : ℂ) :
    holderValue ((1:ℝ)/3) (smoothHolderField M hs hc) z=M z := rfl

def slopeCoefficient (M : ℂ → E →L[ℝ] E) (z : ℂ) : E →L[ℝ] E :=
  (M z).comp ((ContinuousLinearMap.lsmul ℝ ℂ) z)

omit [CompleteSpace E] in
@[simp] lemma slopeCoefficient_apply (M : ℂ → E →L[ℝ] E) (z : ℂ) (a : E) :
    slopeCoefficient M z a = M z (z • a) := rfl

omit [CompleteSpace E] in
lemma slopeCoefficient_smooth (M : ℂ → E →L[ℝ] E) (hs : ContDiff ℝ ∞ M) :
    ContDiff ℝ ∞ (slopeCoefficient M) :=
  hs.clm_comp (ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] E →L[ℝ] E).contDiff

omit [CompleteSpace E] in
lemma slopeCoefficient_compact (M : ℂ → E →L[ℝ] E) (hc : HasCompactSupport M) :
    HasCompactSupport (slopeCoefficient M) := by
  rw [hasCompactSupport_iff_eventuallyEq] at hc ⊢
  filter_upwards [hc] with z hz
  simp only [slopeCoefficient,hz,Pi.zero_apply,ContinuousLinearMap.zero_comp]

 

def markedCRLower (R : ℝ) (M : ℂ → E →L[ℝ] E)
    (hs : ContDiff ℝ ∞ M) (hc : HasCompactSupport M)
    (hR : ∀ z : ℂ, R < ‖z‖ → M z=0) :
    CompactHolderSpace E R →L[ℝ] CompactHolderSpace E R :=
  (markedLowerOrderAmbient (compactCRInverse (E := E) R) (smoothHolderField M hs hc)
    (smoothHolderField (slopeCoefficient M) (slopeCoefficient_smooth M hs)
      (slopeCoefficient_compact M hc))).codRestrict (compactHolderSubmodule R) (by
        intro g z hz
        rw [markedLowerOrderAmbient_value]
        simp only [smoothHolderField_value,hR z hz,slopeCoefficient_apply,zero_apply,sub_self])

@[simp] lemma markedCRLower_value (R : ℝ) (M : ℂ → E →L[ℝ] E)
    (hs : ContDiff ℝ ∞ M) (hc : HasCompactSupport M)
    (hR : ∀ z : ℂ, R < ‖z‖ → M z=0) (g : CompactHolderSpace E R) (z : ℂ) :
    compactHolderValue R (markedCRLower R M hs hc hR g) z = M z (markedCRInverse R g z) := by
  change holderValue ((1:ℝ)/3) (markedLowerOrderAmbient _ _ _ g) z = _
  rw [markedLowerOrderAmbient_value]
  simp only [smoothHolderField_value,slopeCoefficient_apply,markedCRInverse,smul_sub,map_sub]
  rfl

lemma markedCRLower_compact [FiniteDimensional ℂ E] (R : ℝ) (M : ℂ → E →L[ℝ] E)
    (hs : ContDiff ℝ ∞ M) (hc : HasCompactSupport M)
    (hR : ∀ z : ℂ, R < ‖z‖ → M z=0) :
    IsCompactOperator (markedCRLower R M hs hc hR) := by
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hs (by simp)
  have ht := markedLowerOrderAmbient_compact (compactCRInverse (E := E) R) R
    (smoothHolderField M hs hc)
    (smoothHolderField (slopeCoefficient M) (slopeCoefficient_smooth M hs)
      (slopeCoefficient_compact M hc)) hR L hL
  exact ht.codRestrict _ (compactHolderSubmodule_isClosed R)

 

def markedCRLinear (R : ℝ) (M : ℂ → E →L[ℝ] E)
    (hs : ContDiff ℝ ∞ M) (hc : HasCompactSupport M)
    (hR : ∀ z : ℂ, R < ‖z‖ → M z=0) :
    CompactHolderSpace E R →L[ℝ] CompactHolderSpace E R :=
  ContinuousLinearMap.id ℝ _+markedCRLower R M hs hc hR

lemma markedCRLinear_differential (R : ℝ) (M : ℂ → E →L[ℝ] E)
    (hs : ContDiff ℝ ∞ M) (hc : HasCompactSupport M)
    (hR : ∀ z : ℂ, R < ‖z‖ → M z=0) (g : CompactHolderSpace E R) (z : ℂ) :
    compactHolderValue R (markedCRLinear R M hs hc hR g) z =
      fderiv ℝ (markedCRInverse R g) z Complex.I -
      Complex.I • fderiv ℝ (markedCRInverse R g) z 1 + M z (markedCRInverse R g z) := by
  rw [markedCRInverse_rightInverse]
  change compactHolderValue R (g+markedCRLower R M hs hc hR g) z = _
  rw [map_add,BoundedContinuousFunction.add_apply,markedCRLower_value]

lemma markedCRLinear_fredholm [FiniteDimensional ℂ E] (R : ℝ) (M : ℂ → E →L[ℝ] E)
    (hs : ContDiff ℝ ∞ M) (hc : HasCompactSupport M)
    (hR : ∀ z : ℂ, R < ‖z‖ → M z=0) :
    (markedCRLinear R M hs hc hR).IsFredholm :=
  compactPerturbation_fredholm _ (markedCRLower_compact R M hs hc hR)

end

open scoped ContDiff Topology
open Set Function Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 
def CompatibleWith (η : E →L[ℝ] E →L[ℝ] ℝ) (J : E →L[ℝ] E) : Prop :=
  (∀ v, J (J v) = -v) ∧ (∀ u v, η (J u) (J v) = η u v) ∧
    (∀ v ≠ 0, 0 < η v (J v))

 theorem CompatibleWith.form_left {η : E →L[ℝ] E →L[ℝ] ℝ} {J : E →L[ℝ] E}
    (hJ : CompatibleWith η J) (u v : E) : η (J u) v = -η u (J v) := by
  have h := hJ.2.1 u (J v)
  rw [hJ.1 v, map_neg] at h
  linarith

 
def relativeTransition (t : ℝ) (B J : E →L[ℝ] E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - t • J.comp B

@[simp] theorem relativeTransition_apply (t : ℝ) (B J : E →L[ℝ] E) (v : E) :
    relativeTransition t B J v = v - t • J (B v) := rfl

 theorem relativeTransition_apply_B {η : E →L[ℝ] E →L[ℝ] ℝ} {B : E →L[ℝ] E}
    (hB : CompatibleWith η B) (t : ℝ) (J : E →L[ℝ] E) (v : E) :
    relativeTransition t B J (B v) = B v + t • J v := by
  simp [hB.1, sub_eq_add_neg]

 theorem relativeTransition_positive_identity {η : E →L[ℝ] E →L[ℝ] ℝ}
    {B J : E →L[ℝ] E} (hB : CompatibleWith η B) (hJ : CompatibleWith η J)
    (t : ℝ) (v : E) :
    η (relativeTransition t B J v) (relativeTransition t B J (B v)) =
      (1+t^2) * η v (B v) + t * η v (J v) + t * η (B v) (J (B v)) := by
  rw [relativeTransition_apply_B hB, relativeTransition_apply]
  simp only [map_add, map_sub, map_smul, sub_apply,
    smul_apply, smul_eq_mul, hJ.2.1, hJ.form_left]
  rw [hB.form_left v v]
  ring

 theorem relativeTransition_positive {η : E →L[ℝ] E →L[ℝ] ℝ}
    {B J : E →L[ℝ] E} (hB : CompatibleWith η B) (hJ : CompatibleWith η J)
    {t : ℝ} (ht : 0 ≤ t) {v : E} (hv : v ≠ 0) :
    0 < η (relativeTransition t B J v) (relativeTransition t B J (B v)) := by
  rw [relativeTransition_positive_identity hB hJ]
  have hBv : B v ≠ 0 := by
    intro hh
    have h := congrArg B hh
    exact hv (by simpa only [hB.1, map_zero, neg_eq_zero] using h)
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg (mul_pos (by positivity) (hB.2.2 v hv))
      (mul_nonneg ht (hJ.2.2 v hv).le)) (mul_nonneg ht (hJ.2.2 _ hBv).le)

 theorem relativeTransition_isInvertible [FiniteDimensional ℝ E] {η : E →L[ℝ] E →L[ℝ] ℝ}
    {B J : E →L[ℝ] E} (hB : CompatibleWith η B) (hJ : CompatibleWith η J)
    {t : ℝ} (ht : 0 ≤ t) : (relativeTransition t B J).IsInvertible := by
  have hz (v : E) (hv : relativeTransition t B J v = 0) : v = 0 := by
    by_contra h
    have hp := relativeTransition_positive hB hJ ht h
    simp only [hv, map_zero, zero_apply, lt_self_iff_false] at hp
  have hinj : Injective (relativeTransition t B J) := by
    intro u v huv
    exact sub_eq_zero.mp (hz (u-v) (by rw [map_sub, huv, sub_self]))
  exact ⟨(LinearEquiv.ofBijective (relativeTransition t B J).toLinearMap
    ⟨hinj, LinearMap.surjective_of_injective hinj⟩).toContinuousLinearEquiv, rfl⟩

 
def crOperator (J : E → E →L[ℝ] E) (u : ℂ → E) (z : ℂ) : E :=
  fderiv ℝ u z Complex.I - J (u z) (fderiv ℝ u z 1)

 
def crJet (J : E → E →L[ℝ] E) (p : E × (ℂ →L[ℝ] E)) : E :=
  p.2 Complex.I - J p.1 (p.2 1)

 theorem crJet_smooth {J : E → E →L[ℝ] E} (hJ : ContDiff ℝ ∞ J) :
    ContDiff ℝ ∞ (crJet J) := by
  exact (contDiff_snd.clm_apply contDiff_const).sub
    ((hJ.comp contDiff_fst).clm_apply (contDiff_snd.clm_apply contDiff_const))

 

 theorem crJet_fderiv {J : E → E →L[ℝ] E} {x : E}
    (hJ : DifferentiableAt ℝ J x) (A : ℂ →L[ℝ] E)
    (v : E) (B : ℂ →L[ℝ] E) :
    fderiv ℝ (crJet J) (x,A) (v,B) =
      B Complex.I - (fderiv ℝ J x v) (A 1) - J x (B 1) := by
  have hf : HasFDerivAt (Prod.fst : E × (ℂ →L[ℝ] E) → E)
      (ContinuousLinearMap.fst ℝ E (ℂ →L[ℝ] E)) (x,A) := hasFDerivAt_fst
  have hs : HasFDerivAt (Prod.snd : E × (ℂ →L[ℝ] E) → (ℂ →L[ℝ] E))
      (ContinuousLinearMap.snd ℝ E (ℂ →L[ℝ] E)) (x,A) := hasFDerivAt_snd
  have hdJ := hJ.hasFDerivAt.comp (x,A) hf
  have hdI := hs.clm_apply
    (hasFDerivAt_const (Complex.I : ℂ) (x,A))
  have hd1 := hs.clm_apply
    (hasFDerivAt_const (1 : ℂ) (x,A))
  have hd := hdI.sub (hdJ.clm_apply hd1)
  change fderiv ℝ (fun p : E × (ℂ →L[ℝ] E) =>
    p.2 Complex.I - J p.1 (p.2 1)) (x,A) (v,B) = _
  rw [show fderiv ℝ (fun p : E × (ℂ →L[ℝ] E) =>
    p.2 Complex.I - J p.1 (p.2 1)) (x,A) = _ from hd.fderiv]
  simp only [sub_apply,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,zero_apply,map_zero,zero_add]
  change B Complex.I - (J x (B 1) + (fderiv ℝ J x v) (A 1)) = _
  abel

 
 theorem compactSupport_comp_proper {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [Zero Z] {f : Y → Z} {g : X → Y}
    (hf : HasCompactSupport f) (hg : IsProperMap g) : HasCompactSupport (f ∘ g) := by
  apply (hg.isCompact_preimage hf).of_isClosed_subset isClosed_closure
  apply closure_minimal _ ((isClosed_tsupport f).preimage hg.continuous)
  intro x hx
  exact subset_tsupport f hx

 
 def crFrame (B : E →L[ℝ] E) (J : E → E →L[ℝ] E) (u : ℂ → E)
    (z : ℂ) : E →L[ℝ] E := relativeTransition 1 B (J (u z))

 theorem crFrame_intertwines {B : E →L[ℝ] E} {J : E → E →L[ℝ] E}
    (hB : ∀ v, B (B v) = -v) (hJ : ∀ x v, J x (J x v) = -v)
    (u : ℂ → E) (z : ℂ) (v : E) :
    crFrame B J u z (B v) = J (u z) (crFrame B J u z v) := by
  simp only [crFrame,relativeTransition_apply,one_smul,map_sub,hB,hJ,map_neg,sub_neg_eq_add]
  exact add_comm _ _

 theorem crFrame_smooth {B : E →L[ℝ] E} {J : E → E →L[ℝ] E} {u : ℂ → E}
    (hJ : ContDiff ℝ ∞ J) (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (crFrame B J u) := by
  change ContDiff ℝ ∞ (fun z => ContinuousLinearMap.id ℝ E-1 • (J (u z)).comp B)
  simp only [one_smul]
  exact contDiff_const.sub ((hJ.comp hu).clm_comp contDiff_const)

 theorem crFrame_invertible [FiniteDimensional ℝ E] {η : E → E →L[ℝ] E →L[ℝ] ℝ}
    {B : E →L[ℝ] E} {J : E → E →L[ℝ] E}
    (hB : ∀ x, CompatibleWith (η x) B) (hJ : ∀ x, CompatibleWith (η x) (J x))
    (u : ℂ → E) (z : ℂ) : (crFrame B J u z).IsInvertible :=
  relativeTransition_isInvertible (hB (u z)) (hJ (u z)) (by norm_num)

 def linearizedCR (J : E → E →L[ℝ] E) (u v : ℂ → E) (z : ℂ) : E :=
  fderiv ℝ v z Complex.I - J (u z) (fderiv ℝ v z 1) -
    (fderiv ℝ J (u z) (v z)) (fderiv ℝ u z 1)

 theorem linearizedCR_jet {J : E → E →L[ℝ] E} (u v : ℂ → E)
    (hJ : Differentiable ℝ J) (z : ℂ) :
    linearizedCR J u v z =
      fderiv ℝ (crJet J) (u z,fderiv ℝ u z) (v z,fderiv ℝ v z) := by
  rw [crJet_fderiv (hJ (u z))]
  simp only [linearizedCR]
  abel

 def frameLowerOrder (B : E →L[ℝ] E) (J : E → E →L[ℝ] E)
    (u : ℂ → E) (z : ℂ) : E →L[ℝ] E :=
  fderiv ℝ (crFrame B J u) z Complex.I -
    (J (u z)).comp (fderiv ℝ (crFrame B J u) z 1) -
    ((fderiv ℝ J (u z)).flip (fderiv ℝ u z 1)).comp (crFrame B J u z)

 theorem linearizedCR_frame {B : E →L[ℝ] E} {J : E → E →L[ℝ] E}
    (hB : ∀ v, B (B v) = -v) (hJ : ∀ x v, J x (J x v) = -v)
    {u v : ℂ → E} (hA : Differentiable ℝ (crFrame B J u))
    (hv : Differentiable ℝ v) (z : ℂ) :
    linearizedCR J u (fun w => crFrame B J u w (v w)) z =
      crFrame B J u z (crOperator (fun _ => B) v z) + frameLowerOrder B J u z (v z) := by
  have hd := (hA z).hasFDerivAt.clm_apply (hv z).hasFDerivAt
  simp only [linearizedCR,hd.fderiv,add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    crOperator,frameLowerOrder,map_add,map_sub,sub_apply]
  rw [←crFrame_intertwines hB hJ]
  abel

 theorem compactSupport_fderiv_sub_const {J : E → E →L[ℝ] E} {B : E →L[ℝ] E}
    (hc : HasCompactSupport (fun x => J x-B)) :
    HasCompactSupport (fderiv ℝ J) := by
  have he : fderiv ℝ (fun x => J x-B) = fderiv ℝ J := by
    funext x
    rw [fderiv_sub_const]
  rw [←he]
  exact hc.fderiv ℝ

 theorem crFrame_compact_difference {B : E →L[ℝ] E} {J : E → E →L[ℝ] E}
    (hB : ∀ v, B (B v) = -v) (hc : HasCompactSupport (fun x => J x-B))
    {u : ℂ → E} (hu : IsProperMap u) :
    HasCompactSupport (fun z => crFrame B J u z-2 • ContinuousLinearMap.id ℝ E) := by
  have hh := compactSupport_comp_proper hc hu
  rw [hasCompactSupport_iff_eventuallyEq] at hh ⊢
  filter_upwards [hh] with z hz
  have hz' : J (u z)=B := sub_eq_zero.mp hz
  ext v
  simp only [crFrame,relativeTransition_apply,hz',one_smul,hB,
    sub_apply,smul_apply,ContinuousLinearMap.id_apply,sub_neg_eq_add,Pi.zero_apply,zero_apply]
  module

 theorem frameLowerOrder_compact {B : E →L[ℝ] E}
    {J : E → E →L[ℝ] E} (hB : ∀ v, B (B v) = -v)
    (hc : HasCompactSupport (fun x => J x-B))
    {u : ℂ → E} (hup : IsProperMap u) :
    HasCompactSupport (frameLowerOrder B J u) := by
  have hAc := crFrame_compact_difference hB hc hup
  have hDAc : HasCompactSupport (fderiv ℝ (crFrame B J u)) := by
    have he : fderiv ℝ (fun z => crFrame B J u z-2 • ContinuousLinearMap.id ℝ E) =
        fderiv ℝ (crFrame B J u) := by funext z; rw [fderiv_sub_const]
    rw [←he]
    exact hAc.fderiv ℝ
  have hDJc := compactSupport_comp_proper
    (compactSupport_fderiv_sub_const hc) hup
  rw [hasCompactSupport_iff_eventuallyEq] at hDAc hDJc ⊢
  filter_upwards [hDAc,hDJc] with z hz hz'
  ext v
  simp only [frameLowerOrder,sub_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,show fderiv ℝ (crFrame B J u) z=0 from hz,
    show fderiv ℝ J (u z)=0 from hz',zero_apply,map_zero,sub_self,Pi.zero_apply]

end HigherDimensionalBallPacking.Rigidity

end

end OAI
