import Mathlib
import OAI.Geometry.BallPacking.Necessity.HolderCompletion

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

namespace HigherDimensionalBallPacking.Rigidity
open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

local instance : NormedAddCommGroup (ℂ →ᵇ (ℂ →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ (ℂ →ᵇ (ℂ →L[ℝ] E)) := inferInstance

omit [CompleteSpace E] in
theorem segmentIntegrand_continuous (A : ℂ →ᵇ (ℂ →L[ℝ] E)) (x y : ℂ) :
    Continuous (fun t : ℝ => A (x+t • (y-x)) (y-x)) :=
  (A.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const

def linearSegmentIntegral (x y : ℂ) : (ℂ →ᵇ (ℂ →L[ℝ] E)) →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun A => ∫ t in (0:ℝ)..1, A (x+t • (y-x)) (y-x)
      map_add' := by
        intro A B
        exact intervalIntegral.integral_add
          ((segmentIntegrand_continuous A x y).intervalIntegrable _ _)
          ((segmentIntegrand_continuous B x y).intervalIntegrable _ _)
      map_smul' := fun c A => intervalIntegral.integral_smul c _ }
    ‖y-x‖ (fun A => by
      change ‖∫ t in (0:ℝ)..1, A (x+t • (y-x)) (y-x)‖ ≤ ‖y-x‖*‖A‖
      have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
        (fun t _ => ((A (x+t • (y-x))).le_opNorm (y-x)).trans
          (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm _) (norm_nonneg _)))
      simpa only [sub_zero,abs_one,one_mul,mul_comm] using h)

omit [CompleteSpace E] in
@[simp] theorem linearSegmentIntegral_apply (x y : ℂ) (A : ℂ →ᵇ (ℂ →L[ℝ] E)) :
    linearSegmentIntegral x y A = ∫ t in (0:ℝ)..1, A (x+t • (y-x)) (y-x) := rfl

abbrev C1HolderAmbient (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :=
  HolderSpace ℂ E α × HolderSpace ℂ (ℂ →L[ℝ] E) α

def c1HolderGraph (α : ℝ) : Submodule ℝ (C1HolderAmbient E α) where
  carrier := {p | ∀ x y : ℂ, holderValue α p.1 y - holderValue α p.1 x =
    linearSegmentIntegral x y (holderValue α p.2)}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq x y
    change (holderValue α p.1 y+holderValue α q.1 y) -
      (holderValue α p.1 x+holderValue α q.1 x) =
      linearSegmentIntegral x y (holderValue α p.2+holderValue α q.2)
    rw [map_add,← hp x y,← hq x y]
    abel
  smul_mem' := by
    intro c p hp x y
    change c • holderValue α p.1 y - c • holderValue α p.1 x =
      linearSegmentIntegral x y (c • holderValue α p.2)
    rw [map_smul,← hp x y,smul_sub]

instance c1HolderGraph_isClosed (α : ℝ) :
    IsClosed (↑(c1HolderGraph (E := E) α) : Set (C1HolderAmbient E α)) := by
  change IsClosed {p : C1HolderAmbient E α | ∀ x y : ℂ,
    holderValue α p.1 y - holderValue α p.1 x = linearSegmentIntegral x y (holderValue α p.2)}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro y
  exact isClosed_eq
    ((((BoundedContinuousFunction.evalCLM ℝ y).continuous.comp (holderValue α).continuous).comp continuous_fst).sub
      (((BoundedContinuousFunction.evalCLM ℝ x).continuous.comp (holderValue α).continuous).comp continuous_fst))
    (((linearSegmentIntegral x y).continuous.comp (holderValue α).continuous).comp continuous_snd)

abbrev C1HolderSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :=
  ↥(c1HolderGraph (E := E) α)

instance c1HolderSpace_complete (α : ℝ) : CompleteSpace (C1HolderSpace E α) :=
  IsClosed.completeSpace_coe

def c1HolderValue (α : ℝ) : C1HolderSpace E α →L[ℝ] HolderSpace ℂ E α :=
  (ContinuousLinearMap.fst ℝ _ _).comp (c1HolderGraph α).subtypeL

def c1HolderDeriv (α : ℝ) : C1HolderSpace E α →L[ℝ] HolderSpace ℂ (ℂ →L[ℝ] E) α :=
  (ContinuousLinearMap.snd ℝ _ _).comp (c1HolderGraph α).subtypeL

@[simp] theorem c1HolderValue_apply (α : ℝ) (u : C1HolderSpace E α) :
    c1HolderValue α u = u.val.1 := rfl
@[simp] theorem c1HolderDeriv_apply (α : ℝ) (u : C1HolderSpace E α) :
    c1HolderDeriv α u = u.val.2 := rfl

theorem linearSegmentIntegral_remainder (A : ℂ →ᵇ (ℂ →L[ℝ] E)) (x h : ℂ) :
    linearSegmentIntegral x (x+h) A - A x h =
      ∫ t in (0:ℝ)..1, (A (x+t • h)-A x) h := by
  rw [linearSegmentIntegral_apply,add_sub_cancel_left]
  simp only [sub_apply]
  rw [intervalIntegral.integral_sub
    (by simpa only [add_sub_cancel_left] using
      (segmentIntegrand_continuous A x (x+h)).intervalIntegrable (0:ℝ) 1)
    (continuous_const.intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const,sub_zero,one_smul]

 
theorem c1Holder_hasFDerivAt (α : ℝ) (u : C1HolderSpace E α) (x : ℂ) :
    HasFDerivAt (holderValue α (c1HolderValue α u)) (holderValue α (c1HolderDeriv α u) x) x := by
  let f := holderValue α (c1HolderValue α u)
  let A := holderValue α (c1HolderDeriv α u)
  change HasFDerivAt (f : ℂ → E) (A x) x
  rw [hasFDerivAt_iff_isLittleO_nhds_zero,Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ,hδ,hA⟩ := Metric.continuousAt_iff.mp A.continuous.continuousAt ε hε
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) hδ] with h hh
  have hh' : ‖h‖<δ := by simpa only [Metric.mem_ball,dist_zero_right] using hh
  have he : f (x+h)-f x-A x h = ∫ t in (0:ℝ)..1, (A (x+t • h)-A x) h := by
    rw [show f (x+h)-f x=linearSegmentIntegral x (x+h) A from u.property x (x+h)]
    exact linearSegmentIntegral_remainder A x h
  rw [he]
  have hb : ∀ t ∈ uIcc (0:ℝ) 1, ‖(A (x+t • h)-A x) h‖ ≤ ε*‖h‖ := by
    intro t ht
    have ht' : t ∈ Icc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using ht
    have hd : dist (x+t • h) x < δ := by
      rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht'.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) ht'.2).trans_lt hh'
    have hz : ‖A (x+t • h)-A x‖ ≤ ε := by
      simpa only [dist_eq_norm] using (hA hd).le
    exact ((A (x+t • h)-A x).le_opNorm h).trans (mul_le_mul_of_nonneg_right hz (norm_nonneg h))
  simpa only [sub_zero,abs_one,one_mul,mul_one] using intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t ht => hb t (uIoc_subset_uIcc ht))

@[simp] theorem c1Holder_fderiv (α : ℝ) (u : C1HolderSpace E α) (x : ℂ) :
    fderiv ℝ (holderValue α (c1HolderValue α u)) x = holderValue α (c1HolderDeriv α u) x :=
  (c1Holder_hasFDerivAt α u x).fderiv

theorem c1Holder_contDiff (α : ℝ) (u : C1HolderSpace E α) :
    ContDiff ℝ 1 (holderValue α (c1HolderValue α u)) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  exact ⟨holderValue α (c1HolderDeriv α u),
    (holderValue α (c1HolderDeriv α u)).continuous,c1Holder_hasFDerivAt α u⟩

end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 
lemma c1HolderValue_injective (α : ℝ) : Function.Injective (c1HolderValue (E := E) α) := by
  intro u v h
  apply Subtype.ext
  apply Prod.ext
  · exact h
  · apply holderValue_injective α
    apply BoundedContinuousFunction.ext
    intro x
    change holderValue α (c1HolderDeriv α u) x = holderValue α (c1HolderDeriv α v) x
    rw [←c1Holder_fderiv,←c1Holder_fderiv,h]

 

def c1HolderMk (α : ℝ) (f : ℂ → E) (hf : ContDiff ℝ 1 f)
    (A B K : ℝ) (hK0 : 0 ≤ K)
    (hA : ∀ x, ‖f x‖ ≤ A) (hB : ∀ x, ‖fderiv ℝ f x‖ ≤ B)
    (hKf : ∀ x y, ‖f x-f y‖ ≤ K*(dist x y)^α)
    (hKD : ∀ x y, ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ K*(dist x y)^α) :
    C1HolderSpace E α := by
  let fB : ℂ →ᵇ E := BoundedContinuousFunction.ofNormedAddCommGroup f hf.continuous A hA
  let DB : ℂ →ᵇ (ℂ →L[ℝ] E) := BoundedContinuousFunction.ofNormedAddCommGroup
    (fderiv ℝ f) (hf.continuous_fderiv (by norm_num)) B hB
  refine ⟨(holderSpaceMk α fB K hK0 hKf,holderSpaceMk α DB K hK0 hKD),?_⟩
  intro x y
  change f y-f x = linearSegmentIntegral x y DB
  rw [linearSegmentIntegral_apply]
  have hder (t : ℝ) : HasDerivAt (fun s : ℝ => f (x+s • (y-x)))
      (DB (x+t • (y-x)) (y-x)) t := by
    change HasDerivAt (fun s : ℝ => f (x+s • (y-x)))
      (fderiv ℝ f (x+t • (y-x)) (y-x)) t
    have hh := (hasDerivAt_id t).smul_const (y-x)
    have hh' := hh.const_add x
    simpa only [id_eq,one_smul,Function.comp_def] using
      ((hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t hh')
  symm
  simpa only [one_smul,zero_smul,add_zero,add_sub_cancel] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t)
      ((segmentIntegrand_continuous DB x y).intervalIntegrable (0:ℝ) 1)

@[simp] theorem c1HolderMk_value (α : ℝ) (f : ℂ → E) (hf : ContDiff ℝ 1 f)
    (A B K : ℝ) (hK0 : 0 ≤ K)
    (hA : ∀ x, ‖f x‖ ≤ A) (hB : ∀ x, ‖fderiv ℝ f x‖ ≤ B)
    (hKf : ∀ x y, ‖f x-f y‖ ≤ K*(dist x y)^α)
    (hKD : ∀ x y, ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ K*(dist x y)^α) (x : ℂ) :
    holderValue α (c1HolderValue α (c1HolderMk α f hf A B K hK0 hA hB hKf hKD)) x = f x := rfl

end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def compactHolderSubmodule (R : ℝ) : Submodule ℝ (HolderSpace ℂ E ((1:ℝ)/3)) where
  carrier := {u | ∀ x : ℂ, R < ‖x‖ → holderValue ((1:ℝ)/3) u x=0}
  zero_mem' := by simp
  add_mem' := by intro u v hu hv x hx; simpa using congrArg₂ (·+·) (hu x hx) (hv x hx)
  smul_mem' := by intro c u hu x hx; simpa using congrArg (c • ·) (hu x hx)

instance compactHolderSubmodule_isClosed (R : ℝ) :
    IsClosed (↑(compactHolderSubmodule (E := E) R) : Set (HolderSpace ℂ E ((1:ℝ)/3))) := by
  change IsClosed {u : HolderSpace ℂ E ((1:ℝ)/3) |
    ∀ x : ℂ, R < ‖x‖ → holderValue ((1:ℝ)/3) u x=0}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro _
  exact isClosed_eq (((BoundedContinuousFunction.evalCLM ℝ x).continuous).comp
    (holderValue ((1:ℝ)/3)).continuous) continuous_const

abbrev CompactHolderSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :=
  ↥(compactHolderSubmodule (E := E) R)

instance compactHolderSpace_complete [CompleteSpace E] (R : ℝ) :
    CompleteSpace (CompactHolderSpace E R) := IsClosed.completeSpace_coe

def compactHolderValue (R : ℝ) : CompactHolderSpace E R →L[ℝ] (ℂ →ᵇ E) :=
  (holderValue ((1:ℝ)/3)).comp (compactHolderSubmodule R).subtypeL

@[simp] lemma compactHolderValue_apply (R : ℝ) (u : CompactHolderSpace E R) (x : ℂ) :
    compactHolderValue R u x = holderValue ((1:ℝ)/3) u.val x := rfl

lemma compactHolderValue_support (R : ℝ) (u : CompactHolderSpace E R) :
    tsupport (compactHolderValue R u) ⊆ Metric.closedBall (0:ℂ) R := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra h
  have hx' : R < ‖x‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using h
  exact hx (u.property x hx')

lemma compactHolderValue_compactSupport (R : ℝ) (u : CompactHolderSpace E R) :
    HasCompactSupport (compactHolderValue R u) :=
  (isCompact_closedBall (0:ℂ) R).of_isClosed_subset (isClosed_tsupport _) (compactHolderValue_support R u)

lemma compactHolderValue_bound (R : ℝ) (u : CompactHolderSpace E R) (x : ℂ) :
    ‖compactHolderValue R u x‖ ≤ ‖u‖ := by
  exact ((compactHolderValue R u).norm_coe_le_norm x).trans (le_max_left _ _)

lemma compactHolderValue_holder (R : ℝ) (u : CompactHolderSpace E R) (x y : ℂ) :
    ‖compactHolderValue R u x-compactHolderValue R u y‖ ≤ ‖u‖*‖x-y‖^((1:ℝ)/3) := by
  simpa only [compactHolderValue_apply,dist_eq_norm,Submodule.norm_coe] using
    holderSpace_estimate ((1:ℝ)/3) (by norm_num) u.val x y

end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

local instance (R : ℝ) : NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance (R : ℝ) : NormedSpace ℝ (CompactHolderSpace E R) := inferInstance
local instance : NormedAddCommGroup (C1HolderSpace E ((1:ℝ)/3)) := inferInstance
local instance : NormedSpace ℝ (C1HolderSpace E ((1:ℝ)/3)) := inferInstance

lemma compactHolderCauchy_exists (R : ℝ) (u : CompactHolderSpace E R) :
    ∃ v : C1HolderSpace E ((1:ℝ)/3), ∀ x,
      holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) v) x =
        cauchyTransform (compactHolderValue R u) x := by
  have hg := (compactHolderValue R u).continuous
  have hc := compactHolderValue_compactSupport R u
  have hM := compactHolderValue_bound R u
  have hH := compactHolderValue_holder R u
  obtain ⟨A,B,K,_,_,hK,hA,hB,hKf,hKD⟩ := cauchyTransform_holder_global
    hg hc hM (norm_nonneg u) hH
  refine ⟨c1HolderMk ((1:ℝ)/3) (cauchyTransform (compactHolderValue R u))
    (cauchyTransform_holder_contDiff_oneNecessity hg hc hM (norm_nonneg u) hH) A B K hK hA hB
    (by simpa only [dist_eq_norm] using hKf) (by simpa only [dist_eq_norm] using hKD),?_⟩
  intro x
  rfl

def compactHolderCauchy (R : ℝ) (u : CompactHolderSpace E R) : C1HolderSpace E ((1:ℝ)/3) :=
  Classical.choose (compactHolderCauchy_exists R u)

@[simp] theorem compactHolderCauchy_value (R : ℝ) (u : CompactHolderSpace E R) (x : ℂ) :
    holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) (compactHolderCauchy R u)) x =
      cauchyTransform (compactHolderValue R u) x := Classical.choose_spec (compactHolderCauchy_exists R u) x

 
def compactHolderCauchyLM (R : ℝ) : CompactHolderSpace E R →ₗ[ℝ] C1HolderSpace E ((1:ℝ)/3) where
  toFun := compactHolderCauchy R
  map_add' := by
    intro u v
    apply c1HolderValue_injective
    apply holderValue_injective
    apply BoundedContinuousFunction.ext
    intro x
    simp only [compactHolderCauchy_value,map_add,BoundedContinuousFunction.add_apply]
    exact congrFun (cauchyTransform_add_compact (compactHolderValue R u).continuous
      (compactHolderValue R v).continuous (compactHolderValue_compactSupport R u)
      (compactHolderValue_compactSupport R v)) x
  map_smul' := by
    intro c u
    apply c1HolderValue_injective
    apply holderValue_injective
    apply BoundedContinuousFunction.ext
    intro x
    simp only [compactHolderCauchy_value,map_smul,BoundedContinuousFunction.smul_apply,
      RingHom.id_apply]
    exact congrFun (cauchyTransform_real_smul c (compactHolderValue R u)) x

@[simp] lemma compactHolderCauchyLM_value (R : ℝ) (u : CompactHolderSpace E R) (x : ℂ) :
    holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) (compactHolderCauchyLM R u)) x =
      cauchyTransform (compactHolderValue R u) x := compactHolderCauchy_value R u x

lemma compactHolderCauchy_continuous (R : ℝ) : Continuous (compactHolderCauchyLM (E := E) R) := by
  apply (compactHolderCauchyLM (E := E) R).continuous_of_seq_closed_graph
  intro u v w huv huw
  apply c1HolderValue_injective
  apply holderValue_injective
  apply BoundedContinuousFunction.ext
  intro x
  let ev : C1HolderSpace E ((1:ℝ)/3) →L[ℝ] E :=
    (BoundedContinuousFunction.evalCLM ℝ x).comp
      ((holderValue ((1:ℝ)/3)).comp (c1HolderValue ((1:ℝ)/3)))
  have hw := (ev.continuous.tendsto w).comp huw
  change Tendsto (fun j => holderValue ((1:ℝ)/3)
    (c1HolderValue ((1:ℝ)/3) (compactHolderCauchyLM R (u j))) x) atTop
    (𝓝 (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) w) x)) at hw
  simp only [compactHolderCauchyLM_value] at hw
  obtain ⟨M,hM⟩ := (Metric.isBounded_range_of_tendsto u huv).exists_norm_le
  have hpoint (z : ℂ) : Tendsto (fun j => compactHolderValue R (u j) z) atTop
      (𝓝 (compactHolderValue R v z)) :=
    (((BoundedContinuousFunction.evalCLM ℝ z).comp (compactHolderValue R)).continuous.tendsto v).comp huv
  have ht := cauchyTransform_tendsto_compact_data (fun j => (compactHolderValue R (u j)).continuous)
    hpoint (fun j => compactHolderValue_support R (u j)) (compactHolderValue_support R v)
    (fun j z => (compactHolderValue_bound R (u j) z).trans (hM _ ⟨j,rfl⟩)) x
  rw [compactHolderCauchyLM_value]
  exact tendsto_nhds_unique hw ht

 
def compactHolderCauchyCLM (R : ℝ) : CompactHolderSpace E R →L[ℝ] C1HolderSpace E ((1:ℝ)/3) where
  toLinearMap := compactHolderCauchyLM R
  cont := compactHolderCauchy_continuous R

@[simp] theorem compactHolderCauchyCLM_value (R : ℝ) (u : CompactHolderSpace E R) (x : ℂ) :
    holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) (compactHolderCauchyCLM R u)) x =
      cauchyTransform (compactHolderValue R u) x := compactHolderCauchy_value R u x

end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {K E F : Type*} [MetricSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

 
def holderMap (α : ℝ) (L : E →L[ℝ] F) : HolderSpace K E α →L[ℝ] HolderSpace K F α :=
  (((L.compLeftContinuousBounded K).prodMap (L.compLeftContinuousBounded (OffDiagonal K))).comp
    (holderGraph K E α).subtypeL).codRestrict (holderGraph K F α) (by
      intro u z
      change L (holderValue α u z.val.1)-L (holderValue α u z.val.2) =
        (dist z.val.1 z.val.2)^α • L (holderDifference α u z)
      rw [← map_sub,holderSpace_relation α u z.val.1 z.val.2 z.property,map_smul])

@[simp] theorem holderMap_value (α : ℝ) (L : E →L[ℝ] F) (u : HolderSpace K E α) (x : K) :
    holderValue α (holderMap α L u) x = L (holderValue α u x) := rfl

variable [CompleteSpace E] [CompleteSpace F]

def compactHolderMap (R : ℝ) (L : E →L[ℝ] F) : CompactHolderSpace E R →L[ℝ] CompactHolderSpace F R :=
  ((holderMap ((1:ℝ)/3) L).comp (compactHolderSubmodule R).subtypeL).codRestrict
    (compactHolderSubmodule R) (by
      intro u x hx
      change L (holderValue ((1:ℝ)/3) u.val x)=0
      rw [u.property x hx,map_zero])

omit [CompleteSpace E] [CompleteSpace F] in
@[simp] theorem compactHolderMap_value (R : ℝ) (L : E →L[ℝ] F) (u : CompactHolderSpace E R) (x : ℂ) :
    compactHolderValue R (compactHolderMap R L u) x = L (compactHolderValue R u x) := rfl

end HigherDimensionalBallPacking.Rigidity

open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 
def compactCRInverse (R : ℝ) : CompactHolderSpace E R →L[ℝ] C1HolderSpace E ((1:ℝ)/3) :=
  (compactHolderCauchyCLM R).comp
    (compactHolderMap R (((Complex.I/2) • ContinuousLinearMap.id ℂ E).restrictScalars ℝ))

def compactCRInverseValue (R : ℝ) (u : CompactHolderSpace E R) : ℂ →ᵇ E :=
  holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) (compactCRInverse R u))

@[simp] lemma compactCRInverseValue_apply (R : ℝ) (u : CompactHolderSpace E R) (x : ℂ) :
    compactCRInverseValue R u x = cauchyTransform (fun z => (Complex.I/2) • compactHolderValue R u z) x := by
  exact compactHolderCauchyCLM_value R _ x

lemma compactCRInverse_rightInverse (R : ℝ) (u : CompactHolderSpace E R) (x : ℂ) :
    fderiv ℝ (compactCRInverseValue R u) x Complex.I -
      Complex.I • fderiv ℝ (compactCRInverseValue R u) x 1 = compactHolderValue R u x := by
  let v := compactHolderMap R (((Complex.I/2) • ContinuousLinearMap.id ℂ E).restrictScalars ℝ) u
  have hh := cauchyTransform_holder_complexCurl (compactHolderValue R v).continuous
    (compactHolderValue_compactSupport R v) (compactHolderValue_bound R v) (norm_nonneg v)
    (compactHolderValue_holder R v) x
  have he : (compactCRInverseValue R u : ℂ → E) = cauchyTransform (compactHolderValue R v) := by
    funext z
    exact compactHolderCauchyCLM_value R v z
  rw [he]
  have hs : (2*Complex.I) • compactHolderValue R v x = -compactHolderValue R u x := by
    change (2*Complex.I) • ((Complex.I/2) • compactHolderValue R u x) = _
    rw [smul_smul,show (2*Complex.I)*(Complex.I/2)=(-1:ℂ) by ring_nf;simp,neg_one_smul]
  rw [hs] at hh
  change Complex.I • _ - _ = _ at hh
  apply neg_injective
  simpa only [neg_sub] using hh

lemma compactCRInverse_contDiff (R : ℝ) (u : CompactHolderSpace E R) :
    ContDiff ℝ 1 (compactCRInverseValue R u) := c1Holder_contDiff _ _

lemma compactCRInverse_tendsto_zero (R : ℝ) (u : CompactHolderSpace E R) :
    Tendsto (compactCRInverseValue R u) (cocompact ℂ) (𝓝 0) := by
  let v := compactHolderMap R (((Complex.I/2) • ContinuousLinearMap.id ℂ E).restrictScalars ℝ) u
  have he : (compactCRInverseValue R u : ℂ → E) = cauchyTransform (compactHolderValue R v) := by
    funext z
    exact compactHolderCauchyCLM_value R v z
  rw [he]
  exact cauchyTransform_tendsto_zero (compactHolderValue R v).continuous
    (compactHolderValue_compactSupport R v)

 

def markedCRInverse (R : ℝ) (u : CompactHolderSpace E R) (z : ℂ) : E :=
  compactCRInverseValue R u z - compactCRInverseValue R u 0 -
    z • (compactCRInverseValue R u 1-compactCRInverseValue R u 0)

@[simp] lemma markedCRInverse_zero (R : ℝ) (u : CompactHolderSpace E R) : markedCRInverse R u 0=0 := by
  simp [markedCRInverse]
@[simp] lemma markedCRInverse_one (R : ℝ) (u : CompactHolderSpace E R) : markedCRInverse R u 1=0 := by
  simp [markedCRInverse]

lemma markedCRInverse_rightInverse (R : ℝ) (u : CompactHolderSpace E R) (x : ℂ) :
    fderiv ℝ (markedCRInverse R u) x Complex.I -
      Complex.I • fderiv ℝ (markedCRInverse R u) x 1 = compactHolderValue R u x := by
  have hd := c1Holder_hasFDerivAt ((1:ℝ)/3) (compactCRInverse R u) x
  have ha := (hasFDerivAt_id (𝕜 := ℝ) x).smul_const
    (compactCRInverseValue R u 1-compactCRInverseValue R u 0)
  have ht := (hd.sub_const (compactCRInverseValue R u 0)).sub ha
  change HasFDerivAt (markedCRInverse R u) _ x at ht
  rw [ht.fderiv]
  simp only [sub_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply,one_smul,smul_sub]
  have hh := compactCRInverse_rightInverse R u x
  simp only [compactCRInverseValue,c1Holder_fderiv] at hh
  convert hh using 1
  abel

end HigherDimensionalBallPacking.Rigidity

end

end OAI
