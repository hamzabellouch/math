import Mathlib
import OAI.Geometry.BallPacking.Necessity.FrozenInverse

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

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
local instance C1AffineComposeLocal1 (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ V α) := inferInstance
local instance C1AffineComposeLocal2 (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ V α) := inferInstance
local instance C1AffineComposeLocal3 (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (α : ℝ) :
    NormedAddCommGroup (C1HolderSpace V α) := inferInstance
local instance C1AffineComposeLocal4 (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (α : ℝ) :
    NormedSpace ℝ (C1HolderSpace V α) := inferInstance

 def c1HolderAffineCompose (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c : E) (A : ℂ →L[ℝ] E) (v : C1HolderSpace E α) : C1HolderSpace F α := by
  let p := ((c,A),c1HolderValue α v)
  let V := holderAffineFamily α hα₀ hα₁ f hf hc p
  let D := holderAffineFamily α hα₀ hα₁ (fderiv ℝ f) (hf.fderiv_right (by simp)) (hc.fderiv ℝ) p
  let j : HolderSpace ℂ (ℂ →L[ℝ] E) α := holderConstantCLM α A+c1HolderDeriv α v
  let L := holderCLM α (holderMap α (ContinuousLinearMap.compL ℝ ℂ E F) D) j
  refine ⟨(V,L),c1HolderGraph_mem_of_hasFDerivAt α V L ?_⟩
  intro z
  have heV : holderValue α V=(fun z => f (c+A z+holderValue α (c1HolderValue α v) z)) := by
    ext z
    exact holderAffineFamily_apply α hα₀ hα₁ f hf hc p z
  rw [heV]
  change HasFDerivAt _ ((fderiv ℝ f (c+A z+holderValue α (c1HolderValue α v) z)).comp
    (A+holderValue α (c1HolderDeriv α v) z)) z
  exact (hf.differentiable (by simp) _).hasFDerivAt.comp z
    ((A.hasFDerivAt.const_add c).add (c1Holder_hasFDerivAt α v z))

 @[simp] theorem c1HolderAffineCompose_value (α : ℝ) (hα₀ : 0≤α) (hα₁ : α≤1)
    (f : E → F) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (c : E) (A : ℂ →L[ℝ] E) (v : C1HolderSpace E α) (z : ℂ) :
    holderValue α (c1HolderValue α (c1HolderAffineCompose α hα₀ hα₁ f hf hc c A v)) z=
      f (c+A z+holderValue α (c1HolderValue α v) z) :=
  holderAffineFamily_apply α hα₀ hα₁ f hf hc ((c,A),c1HolderValue α v) z

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
local instance responseHolderGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance responseHolderSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance responseCompactGroup (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance responseCompactSpace (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

 def cutoffCompact {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : ContDiffBump (0:ℂ)) : HolderSpace ℂ E ((1:ℝ)/3) →L[ℝ] CompactHolderSpace E b.rOut :=
  (holderCLM ((1:ℝ)/3) (holderLinearPost ((1:ℝ)/3) (ContinuousLinearMap.lsmul ℝ ℝ)
    (holderSourceCutoff ((1:ℝ)/3) (by norm_num) (by norm_num) b))).codRestrict (compactHolderSubmodule b.rOut) (by
      intro g z hz
      change b z • holderValue ((1:ℝ)/3) g z=0
      rw [b.zero_of_le_dist (by simpa using hz.le),zero_smul])

 @[simp] theorem cutoffCompact_value {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : ContDiffBump (0:ℂ)) (g : HolderSpace ℂ E ((1:ℝ)/3)) (z : ℂ) :
    compactHolderValue b.rOut (cutoffCompact b g) z=b z • holderValue ((1:ℝ)/3) g z := rfl

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local instance FrozenResponseLocal1 : NormedAddCommGroup (HolderSpace ℂ E ((1:ℝ)/3)) := inferInstance
local instance FrozenResponseLocal2 : NormedSpace ℝ (HolderSpace ℂ E ((1:ℝ)/3)) := inferInstance
local instance FrozenResponseLocal3 : NormedAddCommGroup (HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) := inferInstance
local instance FrozenResponseLocal4 : NormedSpace ℝ (HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) := inferInstance

 def cutoffFrozen (b : ContDiffBump (0:ℂ))
    (H : HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) :
    CompactHolderSpace E b.rOut →L[ℝ] CompactHolderSpace E b.rOut :=
  ContinuousLinearMap.id ℝ _-(cutoffCompact b).comp ((holderCLM ((1:ℝ)/3) H).comp
    ((holderJetEval ((1:ℝ)/3) 1).comp ((c1HolderDeriv ((1:ℝ)/3)).comp (compactCRInverse b.rOut))))

 theorem cutoffFrozen_value (b : ContDiffBump (0:ℂ))
    (H : HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) (g : CompactHolderSpace E b.rOut) (z : ℂ) :
    compactHolderValue b.rOut (cutoffFrozen b H g) z=compactHolderValue b.rOut g z-
      b z • holderValue ((1:ℝ)/3) H z (fderiv ℝ (compactCRInverseValue b.rOut g) z 1) := by
  have hd : fderiv ℝ (compactCRInverseValue b.rOut g) z=
      holderValue ((1:ℝ)/3) (c1HolderDeriv ((1:ℝ)/3) (compactCRInverse b.rOut g)) z :=
    (c1Holder_hasFDerivAt ((1:ℝ)/3) (compactCRInverse b.rOut g) z).fderiv
  rw [hd]
  rfl

 theorem cutoffFrozen_contDiff (b : ContDiffBump (0:ℂ)) :
    ContDiff ℝ ∞ (cutoffFrozen (E := E) b) := by
  let D : CompactHolderSpace E b.rOut →L[ℝ] HolderSpace ℂ E ((1:ℝ)/3) :=
    (holderJetEval ((1:ℝ)/3) 1).comp ((c1HolderDeriv ((1:ℝ)/3)).comp (compactCRInverse b.rOut))
  have hL : ContDiff ℝ ∞ (holderOperatorCLM (K := ℂ) (E := E) (F := E) ((1:ℝ)/3)) :=
    ContinuousLinearMap.contDiff _
  have hh : ContDiff ℝ ∞ (fun H : HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3) => (holderCLM ((1:ℝ)/3) H).comp D) :=
    hL.clm_comp contDiff_const
  exact contDiff_const.sub ((contDiff_const (c := cutoffCompact (E := E) b)).clm_comp hh)

 def frozenResponse (b : ContDiffBump (0:ℂ))
    (p : HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3) × E) : CompactHolderSpace E b.rOut :=
  (cutoffFrozen b p.1).inverse (cutoffCompact b (holderCLM ((1:ℝ)/3) p.1 (holderConstantCLM ((1:ℝ)/3) p.2)))

 theorem frozenResponse_contDiffAt (b : ContDiffBump (0:ℂ))
    (p : HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3) × E) (hi : (cutoffFrozen b p.1).IsInvertible) :
    ContDiffAt ℝ ∞ (frozenResponse b) p := by
  have hL : ContDiff ℝ ∞ (holderOperatorCLM (K := ℂ) (E := E) (F := E) ((1:ℝ)/3)) :=
    ContinuousLinearMap.contDiff _
  have hC : ContDiff ℝ ∞ (holderConstantCLM (E := E) ((1:ℝ)/3)) :=
    ContinuousLinearMap.contDiff _
  have hr : ContDiff ℝ ∞ (fun p : HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3) × E =>
      cutoffCompact b (holderCLM ((1:ℝ)/3) p.1 (holderConstantCLM ((1:ℝ)/3) p.2))) :=
    (cutoffCompact (E := E) b).contDiff.comp
      ((hL.comp contDiff_fst).clm_apply
        (hC.comp contDiff_snd))
  exact (hi.contDiffAt_map_inverse.comp p ((cutoffFrozen_contDiff (E := E) b).comp contDiff_fst).contDiffAt).clm_apply hr.contDiffAt

 theorem frozenResponse_comp_contDiffAt
    {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (b : ContDiffBump (0:ℂ))
    (H : D → HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) (a : E) (p : D)
    (hH : ContDiffAt ℝ ∞ H p) (hi : (cutoffFrozen b (H p)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun x => frozenResponse b (H x,a)) p := by
  have hp : ContDiffAt ℝ ∞ (fun x => (H x,a)) p := hH.prodMk contDiffAt_const
  exact (frozenResponse_contDiffAt b (H p,a) hi).comp p hp

 theorem frozenResponse_eq (b : ContDiffBump (0:ℂ))
    (H : HolderSpace ℂ (E →L[ℝ] E) ((1:ℝ)/3)) (a : E)
    (hi : (cutoffFrozen b H).IsInvertible) (g : CompactHolderSpace E b.rOut)
    (hg : cutoffFrozen b H g=cutoffCompact b (holderCLM ((1:ℝ)/3) H (holderConstantCLM ((1:ℝ)/3) a))) :
    frozenResponse b (H,a)=g := by
  change (cutoffFrozen b H).inverse _=g
  rw [←hg,hi.inverse_apply_self]

end HigherDimensionalBallPacking.Rigidity
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
 theorem cutoffFrozen_eq {n : ℕ} (b : ContDiffBump (0:ℂ))
    (H : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, b.rIn<‖z‖ → holderValue ((1:ℝ)/3) H z=0) :
    cutoffFrozen b H=frozenPrincipal b.rOut H (fun z hz => hs z (b.rIn_lt_rOut.trans hz)) := by
  apply ContinuousLinearMap.ext
  intro g
  apply compactHolderValue_injective
  apply BoundedContinuousFunction.ext
  intro z
  rw [cutoffFrozen_value,frozenPrincipal_value]
  by_cases hz : ‖z‖≤b.rIn
  · rw [b.one_of_mem_closedBall (by simpa using hz),one_smul]
  · rw [hs z (lt_of_not_ge hz),zero_apply,smul_zero]

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
local instance FrozenRepresentationLocal1 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance FrozenRepresentationLocal2 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance FrozenRepresentationLocal3 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :
    NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance FrozenRepresentationLocal4 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :
    NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance FrozenRepresentationLocal5 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance FrozenRepresentationLocal6 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

 theorem cutoffFrozen_invertible {n : ℕ} (b : ContDiffBump (0:ℂ))
    (H : C1HolderSpace (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, b.rIn<‖z‖ → holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) H) z=0)
    (hK : ∀ z, Compatible (standardJ n+holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) H) z)) :
    (cutoffFrozen b (c1HolderValue ((1:ℝ)/3) H)).IsInvertible := by
  rw [cutoffFrozen_eq b _ hs]
  let K := c1HolderConstantCLM ((1:ℝ)/3) (standardJ n)+H
  apply frozenPrincipal_isInvertible b.rOut K _ _
  · intro z
    rfl
  · exact hK

 theorem cutoff_curl_value {n : ℕ} (b : ContDiffBump (0:ℂ))
    (v : C1HolderSpace (Phase n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, b.rIn<‖z‖ → holderValue ((1:ℝ)/3) (c1StandardCurl v) z=0) (z : ℂ) :
    compactHolderValue b.rOut (cutoffCompact b (c1StandardCurl v)) z=
      holderValue ((1:ℝ)/3) (c1StandardCurl v) z := by
  rw [cutoffCompact_value]
  by_cases hz : ‖z‖≤b.rIn
  · rw [b.one_of_mem_closedBall (by simpa using hz),one_smul]
  · rw [hs z (lt_of_not_ge hz),smul_zero]

 theorem cutoff_curl_reconstruct {n : ℕ} (b : ContDiffBump (0:ℂ))
    (v : C1HolderSpace (Phase n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, b.rIn<‖z‖ → holderValue ((1:ℝ)/3) (c1StandardCurl v) z=0)
    (hlim : Tendsto (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) v)) (cocompact ℂ) (𝓝 0)) :
    v=compactCRInverse b.rOut (cutoffCompact b (c1StandardCurl v)) := by
  let g := cutoffCompact b (c1StandardCurl v)
  have hv : (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) v) : ℂ → Phase n)=compactCRInverseValue b.rOut g := by
    apply c1_decay_cauchy_representation b.rOut g (c1Holder_contDiff _ v) _ hlim
    intro z
    rw [cutoff_curl_value b v hs z,c1StandardCurl_value]
  apply c1HolderValue_injective
  apply holderValue_injective
  exact BoundedContinuousFunction.ext (congrFun hv)

 theorem cutoffFrozen_equation {n : ℕ} (b : ContDiffBump (0:ℂ))
    (H : HolderSpace ℂ (End n) ((1:ℝ)/3)) (a : Phase n) (g : CompactHolderSpace (Phase n) b.rOut)
    (he : ∀ z, compactHolderValue b.rOut g z=b z • holderValue ((1:ℝ)/3) H z
      (a+fderiv ℝ (compactCRInverseValue b.rOut g) z 1)) :
    cutoffFrozen b H g=cutoffCompact b (holderCLM ((1:ℝ)/3) H (holderConstantCLM ((1:ℝ)/3) a)) := by
  apply compactHolderValue_injective
  apply BoundedContinuousFunction.ext
  intro z
  rw [cutoffFrozen_value b H g z,he z,cutoffCompact_value b _ z,holderCLM_apply,holderConstantCLM_value]
  rw [map_add,smul_add,add_sub_cancel_right]

 theorem c1_frozen_response {n : ℕ} (b : ContDiffBump (0:ℂ))
    (v : C1HolderSpace (Phase n) ((1:ℝ)/3)) (a : Phase n)
    (H : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, b.rIn<‖z‖ → holderValue ((1:ℝ)/3) H z=0)
    (hi : (cutoffFrozen b H).IsInvertible)
    (hcurl : ∀ z, holderValue ((1:ℝ)/3) (c1StandardCurl v) z=
      holderValue ((1:ℝ)/3) H z (a+holderValue ((1:ℝ)/3) (c1HolderDeriv ((1:ℝ)/3) v) z 1))
    (hlim : Tendsto (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) v)) (cocompact ℂ) (𝓝 0)) :
    v=compactCRInverse b.rOut (frozenResponse b (H,a)) := by
  let g := cutoffCompact b (c1StandardCurl v)
  have hcs (z : ℂ) (hz : b.rIn<‖z‖) : holderValue ((1:ℝ)/3) (c1StandardCurl v) z=0 := by
    rw [hcurl,hs z hz,zero_apply]
  have hveq : v=compactCRInverse b.rOut g := cutoff_curl_reconstruct b v hcs hlim
  have hg : cutoffFrozen b H g=cutoffCompact b (holderCLM ((1:ℝ)/3) H (holderConstantCLM ((1:ℝ)/3) a)) := by
    apply cutoffFrozen_equation
    intro z
    change b z • holderValue ((1:ℝ)/3) (c1StandardCurl v) z=_
    rw [hcurl,hveq]
    have hd : fderiv ℝ (compactCRInverseValue b.rOut g) z=
        holderValue ((1:ℝ)/3) (c1HolderDeriv ((1:ℝ)/3) (compactCRInverse b.rOut g)) z :=
      (c1Holder_hasFDerivAt ((1:ℝ)/3) (compactCRInverse b.rOut g) z).fderiv
    rw [hd]
  rw [frozenResponse_eq b H a hi g hg]
  exact hveq

end HigherDimensionalBallPacking.Rigidity

end

end OAI
