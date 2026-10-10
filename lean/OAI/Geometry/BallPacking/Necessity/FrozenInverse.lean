import Mathlib
import OAI.Geometry.BallPacking.Necessity.FrozenOperators
import OAI.Geometry.BallPacking.Necessity.EqualDimension

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
local instance holderInverseHGroup (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ V α) := inferInstance
local instance holderInverseHSpace (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ V α) := inferInstance
local instance holderInverseCGroup (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (α : ℝ) :
    NormedAddCommGroup (C1HolderSpace V α) := inferInstance
local instance holderInverseCSpace (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (α : ℝ) :
    NormedSpace ℝ (C1HolderSpace V α) := inferInstance

 def c1HolderMap (α : ℝ) (L : E →L[ℝ] F) : C1HolderSpace E α →L[ℝ] C1HolderSpace F α :=
  (((holderMap α L).comp (c1HolderValue α)).prod
    ((holderMap α ((ContinuousLinearMap.compL ℝ ℂ E F) L)).comp (c1HolderDeriv α))).codRestrict
      (c1HolderGraph α) (by
        intro u
        apply c1HolderGraph_mem_of_hasFDerivAt α
        intro z
        exact L.hasFDerivAt.comp z (c1Holder_hasFDerivAt α u z))

 @[simp] theorem c1HolderMap_value (α : ℝ) (L : E →L[ℝ] F) (u : C1HolderSpace E α) (z : ℂ) :
    holderValue α (c1HolderValue α (c1HolderMap α L u)) z=
      L (holderValue α (c1HolderValue α u) z) := rfl

 theorem inverseField_continuous {a : ℂ → E →L[ℝ] E} (ha : Continuous a)
    (hi : ∀ z, (a z).IsInvertible) : Continuous (fun z => (a z).inverse) := by
  rw [continuous_iff_continuousAt]
  intro z
  exact ((hi z).contDiffAt_map_inverse (n := ∞)).continuousAt.comp ha.continuousAt

 theorem inverseField_bound (R : ℝ) {a : ℂ → E →L[ℝ] E} (ha : Continuous a)
    (hi : ∀ z, (a z).IsInvertible) (hout : ∀ z, R<‖z‖ → a z=ContinuousLinearMap.id ℝ E) :
    ∃ C : ℝ, 0<C ∧ ∀ z, ‖(a z).inverse‖≤C := by
  have hc := inverseField_continuous ha hi
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:ℂ) R).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C ‖ContinuousLinearMap.id ℝ E‖+1,by positivity,?_⟩
  intro z
  by_cases hz : ‖z‖≤R
  · exact (hC z (by simpa using hz)).trans ((le_max_left _ _).trans (by linarith))
  · rw [hout z (lt_of_not_ge hz),ContinuousLinearMap.inverse_id]
    exact (le_max_right _ _).trans (by linarith)

 omit [CompleteSpace E] in
 theorem inverseField_sub {a b : E →L[ℝ] E} (ha : a.IsInvertible) (hb : b.IsInvertible) :
    a.inverse-b.inverse=a.inverse.comp ((b-a).comp b.inverse) := by
  ext v
  simp only [sub_apply,ContinuousLinearMap.comp_apply,map_sub,
    hb.self_apply_inverse,ha.inverse_apply_self]

 omit [CompleteSpace E] in
 theorem inverseField_holder (α : ℝ) (hα : 0<α) (A : HolderSpace ℂ (E →L[ℝ] E) α)
    (hi : ∀ z, (holderValue α A z).IsInvertible) (C : ℝ) (hC : 0≤C)
    (hb : ∀ z, ‖(holderValue α A z).inverse‖≤C) (x y : ℂ) :
    ‖(holderValue α A x).inverse-(holderValue α A y).inverse‖≤
      (C*C*‖A‖)*(dist x y)^α := by
  rw [inverseField_sub (hi x) (hi y)]
  calc
    _ ≤ ‖(holderValue α A x).inverse‖*
        (‖holderValue α A y-holderValue α A x‖*‖(holderValue α A y).inverse‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ C*((‖A‖*(dist y x)^α)*C) :=
      mul_le_mul (hb x) (mul_le_mul (holderSpace_estimate α hα A y x) (hb y)
        (norm_nonneg _) (by positivity)) (by positivity) hC
    _ = _ := by rw [dist_comm y x]; ring

 def holderInverse (α : ℝ) (hα : 0<α) (R : ℝ) (A : HolderSpace ℂ (E →L[ℝ] E) α)
    (hi : ∀ z, (holderValue α A z).IsInvertible)
    (hout : ∀ z, R<‖z‖ → holderValue α A z=ContinuousLinearMap.id ℝ E) :
    HolderSpace ℂ (E →L[ℝ] E) α := by
  let ex := inverseField_bound R (holderValue α A).continuous hi hout
  let C := Classical.choose ex
  have hC := (Classical.choose_spec ex).1
  have hb := (Classical.choose_spec ex).2
  let f : ℂ →ᵇ (E →L[ℝ] E) := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => (holderValue α A z).inverse) (inverseField_continuous (holderValue α A).continuous hi) C hb
  exact holderSpaceMk α f (C*C*‖A‖) (by positivity) (inverseField_holder α hα A hi C hC.le hb)

 theorem holderInverse_value (α : ℝ) (hα : 0<α) (R : ℝ) (A : HolderSpace ℂ (E →L[ℝ] E) α)
    (hi : ∀ z, (holderValue α A z).IsInvertible)
    (hout : ∀ z, R<‖z‖ → holderValue α A z=ContinuousLinearMap.id ℝ E) (z : ℂ) :
    holderValue α (holderInverse α hα R A hi hout) z=(holderValue α A z).inverse := by
  rfl

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
local instance FrozenOperatorLocal1 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance FrozenOperatorLocal2 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance FrozenOperatorLocal3 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :
    NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance FrozenOperatorLocal4 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :
    NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance FrozenOperatorLocal5 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance FrozenOperatorLocal6 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

 theorem frame_product_decay {n : ℕ} (R : ℝ) (a : ℂ → End n) (v : ℂ → Phase n)
    (hout : ∀ z, R<‖z‖ → a z=ContinuousLinearMap.id ℝ (Phase n))
    (hv : Tendsto v (cocompact ℂ) (𝓝 0)) :
    Tendsto (fun z => a z (v z)) (cocompact ℂ) (𝓝 0) := by
  apply hv.congr'
  filter_upwards [(isCompact_closedBall (0:ℂ) R).compl_mem_cocompact] with z hz
  have hzR : R<‖z‖ := by simpa only [mem_compl_iff,Metric.mem_closedBall,dist_zero_right,not_le] using hz
  rw [hout z hzR,ContinuousLinearMap.id_apply]

 theorem frame_product_inhomogeneous {n : ℕ} (a : ℂ → End n) (v : ℂ → Phase n)
    (ha : ContDiff ℝ 1 a) (hv : ContDiff ℝ 1 v) (K M : ℂ → End n) (d f : ℂ → Phase n)
    (hi : ∀ z, (a z).IsInvertible)
    (hint : ∀ z x, a z (Complex.I • x)=K z (a z x))
    (hM : ∀ z x, fderiv ℝ a z Complex.I x-K z (fderiv ℝ a z 1 x)=a z (M z x))
    (hCR : ∀ z, fderiv ℝ v z Complex.I-Complex.I • fderiv ℝ v z 1=d z)
    (hd : ∀ z, d z+M z (v z)=(a z).inverse (f z)) :
    ∀ z, fderiv ℝ (fun z => a z (v z)) z Complex.I-
      K z (fderiv ℝ (fun z => a z (v z)) z 1)=f z := by
  intro z
  rw [frame_product_CR (ha.differentiable one_ne_zero z)
    (hv.differentiable one_ne_zero z) (K z) (M z) (hint z) (hM z),
      hCR z,hd z,(hi z).self_apply_inverse]

 theorem unmarked_density_equation {n : ℕ} (R : ℝ)
    (M B : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) M z=0)
    (hsurj : Surjective (fun g : CompactHolderSpace (Phase n) R => g+unmarkedLower R M hs g))
    (f : CompactHolderSpace (Phase n) R) :
    ∃ d : CompactHolderSpace (Phase n) R, ∀ z,
      compactHolderValue R d z+holderValue ((1:ℝ)/3) M z (compactCRInverseValue R d z)=
        holderValue ((1:ℝ)/3) B z (compactHolderValue R f z) := by
  obtain ⟨d,hd⟩ := hsurj (compactHolderMul R B f)
  refine ⟨d,?_⟩
  intro z
  exact congrArg (fun g => compactHolderValue R g z) hd

 theorem framed_density_equation {n : ℕ} (R : ℝ) (K : ℂ → End n)
    (hK : ∀ z, Compatible (K z)) (hKout : ∀ z : ℂ, R<‖z‖ → K z=standardJ n)
    (A : C1HolderSpace (End n) ((1:ℝ)/3)) (M : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) M z=0)
    (hAout : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z=ContinuousLinearMap.id ℝ _)
    (hi : ∀ z, (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z).IsInvertible)
    (hint : ∀ z x, holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z (Complex.I • x)=
      K z (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z x))
    (hM : ∀ z x, fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) z Complex.I x-
      K z (fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) z 1 x)=
      holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z (holderValue ((1:ℝ)/3) M z x))
    (f : CompactHolderSpace (Phase n) R) :
    ∃ d : CompactHolderSpace (Phase n) R, ∀ z,
      compactHolderValue R d z+holderValue ((1:ℝ)/3) M z (compactCRInverseValue R d z)=
        (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z).inverse (compactHolderValue R f z) := by
  let B : HolderSpace ℂ (End n) ((1:ℝ)/3) :=
    holderInverse (E := Phase n) ((1:ℝ)/3) (by norm_num) R
      (c1HolderValue (E := End n) ((1:ℝ)/3) A) hi hAout
  have hsurj : Surjective (fun g : CompactHolderSpace (Phase n) R =>
      g+unmarkedLower R M hs g) := framed_unmarked_surjective (n := n) R K hK hKout A M hs hAout
    (fun z => (hi z).injective) hint hM
  obtain ⟨d,hd⟩ := unmarked_density_equation (n := n) R M B hs hsurj f
  refine ⟨d,?_⟩
  intro z
  exact (hd z).trans (congrArg (fun operator : End n => operator (compactHolderValue R f z))
    (holderInverse_value (E := Phase n) ((1:ℝ)/3) (by norm_num) R
      (c1HolderValue (E := End n) ((1:ℝ)/3) A) hi hAout z))

 theorem framed_frozen_solution {n : ℕ} (R : ℝ) (K : ℂ → End n)
    (hK : ∀ z, Compatible (K z)) (hKout : ∀ z : ℂ, R<‖z‖ → K z=standardJ n)
    (A : C1HolderSpace (End n) ((1:ℝ)/3)) (M : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) M z=0)
    (hAout : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z=ContinuousLinearMap.id ℝ _)
    (hi : ∀ z, (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z).IsInvertible)
    (hint : ∀ z x, holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z (Complex.I • x)=
      K z (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z x))
    (hM : ∀ z x, fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) z Complex.I x-
      K z (fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) z 1 x)=
      holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z (holderValue ((1:ℝ)/3) M z x))
    (f : CompactHolderSpace (Phase n) R) :
    ∃ U : C1HolderSpace (Phase n) ((1:ℝ)/3),
      let u := holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) U)
      (∀ z, fderiv ℝ u z Complex.I-K z (fderiv ℝ u z 1)=compactHolderValue R f z) ∧
        Tendsto u (cocompact ℂ) (𝓝 0) := by
  obtain ⟨d,hd⟩ := framed_density_equation R K hK hKout A M hs hAout hi hint hM f
  let U := c1HolderMultiply ((1:ℝ)/3) A (compactCRInverse R d)
  refine ⟨U,?_,?_⟩
  · exact frame_product_inhomogeneous
      (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) (compactCRInverseValue R d)
      (c1Holder_contDiff _ A) (compactCRInverse_contDiff R d) K
      (holderValue ((1:ℝ)/3) M) (compactHolderValue R d) (compactHolderValue R f)
      hi hint hM (compactCRInverse_rightInverse R d) hd
  · exact frame_product_decay R _ (compactCRInverseValue R d) hAout (compactCRInverse_tendsto_zero R d)

 def frozenPrincipal {n : ℕ} (R : ℝ) (H : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) H z=0) :
    CompactHolderSpace (Phase n) R →L[ℝ] CompactHolderSpace (Phase n) R :=
  ContinuousLinearMap.id ℝ _-
    (((holderCLM ((1:ℝ)/3) H).comp
      (((holderJetEval ((1:ℝ)/3) 1).comp (c1HolderDeriv ((1:ℝ)/3))).comp (compactCRInverse R))).codRestrict
        (compactHolderSubmodule R) (by
          intro g z hz
          change holderValue ((1:ℝ)/3) H z (holderValue ((1:ℝ)/3)
            (c1HolderDeriv ((1:ℝ)/3) (compactCRInverse R g)) z 1)=0
          rw [hs z hz,zero_apply]))

 theorem frozenPrincipal_value {n : ℕ} (R : ℝ) (H : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) H z=0)
    (g : CompactHolderSpace (Phase n) R) (z : ℂ) :
    compactHolderValue R (frozenPrincipal R H hs g) z=compactHolderValue R g z-
      holderValue ((1:ℝ)/3) H z (fderiv ℝ (compactCRInverseValue R g) z 1) := by
  have hd : fderiv ℝ (compactCRInverseValue R g) z=
      holderValue ((1:ℝ)/3) (c1HolderDeriv ((1:ℝ)/3) (compactCRInverse R g)) z :=
    (c1Holder_hasFDerivAt ((1:ℝ)/3) (compactCRInverse R g) z).fderiv
  rw [hd]
  rfl

 theorem compactHolderValue_injective {n : ℕ} (R : ℝ) :
    Injective (compactHolderValue (E := Phase n) R) := by
  intro g h he
  apply Subtype.ext
  exact holderValue_injective ((1:ℝ)/3) he

 theorem c1_potential_yields_frozen_density {n : ℕ} (R : ℝ)
    (H : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) H z=0)
    (f : CompactHolderSpace (Phase n) R) (U : C1HolderSpace (Phase n) ((1:ℝ)/3))
    (hCR : ∀ z, fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) U)) z Complex.I-
      (standardJ n+holderValue ((1:ℝ)/3) H z)
        (fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) U)) z 1)=compactHolderValue R f z)
    (hlim : Tendsto (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) U)) (cocompact ℂ) (𝓝 0)) :
    ∃ g : CompactHolderSpace (Phase n) R, frozenPrincipal R H hs g=f := by
  let u := holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) U)
  have hu : ContDiff ℝ 1 u := c1Holder_contDiff _ U
  have hc (z : ℂ) : holderValue ((1:ℝ)/3) (c1StandardCurl U) z=
      compactHolderValue R f z+holderValue ((1:ℝ)/3) H z (fderiv ℝ u z 1) := by
    rw [c1StandardCurl_value]
    have hh := hCR z
    change fderiv ℝ u z Complex.I-(Complex.I • fderiv ℝ u z 1+holderValue ((1:ℝ)/3) H z (fderiv ℝ u z 1))=_ at hh
    change fderiv ℝ u z Complex.I-Complex.I • fderiv ℝ u z 1=_
    rw [sub_add_eq_sub_sub] at hh
    exact sub_eq_iff_eq_add.mp hh
  let g : CompactHolderSpace (Phase n) R := ⟨c1StandardCurl U,by
    intro z hz
    have hf0 : compactHolderValue R f z=0 := f.property z hz
    rw [hc z,hs z hz,hf0,zero_apply,add_zero]⟩
  have hrep : (u : ℂ → Phase n)=compactCRInverseValue R g :=
    c1_decay_cauchy_representation R g hu (fun z => (c1StandardCurl_value U z).symm) hlim
  refine ⟨g,compactHolderValue_injective R ?_⟩
  apply BoundedContinuousFunction.ext
  intro z
  rw [frozenPrincipal_value]
  change holderValue ((1:ℝ)/3) (c1StandardCurl U) z-_=_
  rw [hc z,←hrep,add_sub_cancel_right]

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
open SymplecticBallPacking.Hamiltonian
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
local instance frameFieldInst1 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance frameFieldInst2 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance frameFieldInst3 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :
    NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance frameFieldInst4 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :
    NormedSpace ℝ (C1HolderSpace E α) := inferInstance

 def normalizedHolderFrame {n : ℕ} (K : C1HolderSpace (End n) ((1:ℝ)/3)) :
    C1HolderSpace (End n) ((1:ℝ)/3) :=
  c1HolderConstantCLM ((1:ℝ)/3) ((1/2:ℝ) • ContinuousLinearMap.id ℝ (Phase n))-
    c1HolderMap ((1:ℝ)/3)
      ((1/2:ℝ) • (ContinuousLinearMap.compL ℝ (Phase n) (Phase n) (Phase n)).flip (standardJ n)) K

 theorem normalizedHolderFrame_value {n : ℕ} (K : C1HolderSpace (End n) ((1:ℝ)/3)) (z : ℂ) :
    holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) (normalizedHolderFrame K)) z=
      (1/2:ℝ) • relativeTransition 1 (standardJ n) (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) K) z) := by
  change (1/2:ℝ) • ContinuousLinearMap.id ℝ (Phase n)-
    (1/2:ℝ) • (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) K) z).comp (standardJ n)=_
  simp only [relativeTransition,one_smul,smul_sub]

 theorem normalizedFrame_intertwines {n : ℕ} {K : End n} (hK : Compatible K) (x : Phase n) :
    ((1/2:ℝ) • relativeTransition 1 (standardJ n) K) (Complex.I • x)=
      K (((1/2:ℝ) • relativeTransition 1 (standardJ n) K) x) := by
  simp only [smul_apply,relativeTransition_apply,one_smul]
  change (1/2:ℝ) • (standardJ n x-K (standardJ n (standardJ n x)))=
    K ((1/2:ℝ) • (x-K (standardJ n x)))
  rw [standardJ_sq,map_neg,map_smul,map_sub,hK.1]
  module

 theorem normalizedFrame_invertible {n : ℕ} {K : End n} (hK : Compatible K) :
    ((1/2:ℝ) • relativeTransition 1 (standardJ n) K).IsInvertible := by
  have ht := relativeTransition_isInvertible (compatible_standardJ n).compatibleWith_stdOmega
    hK.compatibleWith_stdOmega (t := 1) (by norm_num)
  let A : End n := (1/2:ℝ) • relativeTransition 1 (standardJ n) K
  have hi : Injective A := by
    intro x y hxy
    apply ht.injective
    exact (smul_right_injective (Phase n) (by norm_num : (1/2:ℝ)≠0)) hxy
  exact ⟨(LinearEquiv.ofBijective A.toLinearMap ⟨hi,LinearMap.surjective_of_injective hi⟩).toContinuousLinearEquiv,rfl⟩

 theorem normalizedFrame_standard {n : ℕ} :
    (1/2:ℝ) • relativeTransition 1 (standardJ n) (standardJ n)=ContinuousLinearMap.id ℝ (Phase n) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [smul_apply,relativeTransition_apply,one_smul,ContinuousLinearMap.id_apply]
  change (1/2:ℝ) • (x-standardJ n (standardJ n x))=x
  rw [standardJ_sq]
  module

 theorem constant_outside_fderiv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℝ) {a : ℂ → E} {c : E} (hout : ∀ z, R<‖z‖ → a z=c) {z : ℂ} (hz : R<‖z‖) :
    fderiv ℝ a z=0 := by
  have he : a=ᶠ[𝓝 z] fun _ => c := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w hw
    exact hout w hw
  rw [he.fderiv_eq,fderiv_const_apply]

 def holderComp {n : ℕ} (A B : HolderSpace ℂ (End n) ((1:ℝ)/3)) :
    HolderSpace ℂ (End n) ((1:ℝ)/3) :=
  holderCLM ((1:ℝ)/3) (holderMap ((1:ℝ)/3) (ContinuousLinearMap.compL ℝ (Phase n) (Phase n) (Phase n)) A) B

 @[simp] theorem holderComp_value {n : ℕ} (A B : HolderSpace ℂ (End n) ((1:ℝ)/3)) (z : ℂ) :
    holderValue ((1:ℝ)/3) (holderComp A B) z=
      (holderValue ((1:ℝ)/3) A z).comp (holderValue ((1:ℝ)/3) B z) := rfl

 def principalFrameLower {n : ℕ} (R : ℝ) (K : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (A : C1HolderSpace (End n) ((1:ℝ)/3))
    (hi : ∀ z, (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z).IsInvertible)
    (hout : ∀ z, R<‖z‖ → holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z=ContinuousLinearMap.id ℝ (Phase n)) :
    HolderSpace ℂ (End n) ((1:ℝ)/3) :=
  holderComp (holderInverse ((1:ℝ)/3) (by norm_num) R (c1HolderValue ((1:ℝ)/3) A) hi hout)
    ((holderJetEval ((1:ℝ)/3) Complex.I (c1HolderDeriv ((1:ℝ)/3) A))-
      holderComp K (holderJetEval ((1:ℝ)/3) 1 (c1HolderDeriv ((1:ℝ)/3) A)))

 theorem principalFrameLower_value {n : ℕ} (R : ℝ) (K : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (A : C1HolderSpace (End n) ((1:ℝ)/3))
    (hi : ∀ z, (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z).IsInvertible)
    (hout : ∀ z, R<‖z‖ → holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z=ContinuousLinearMap.id ℝ (Phase n))
    (z : ℂ) (x : Phase n) :
    holderValue ((1:ℝ)/3) (principalFrameLower R K A hi hout) z x=
      (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z).inverse
      (fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) z Complex.I x-
        holderValue ((1:ℝ)/3) K z (fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) z 1 x)) := by
  rw [(c1Holder_hasFDerivAt ((1:ℝ)/3) A z).fderiv]
  rfl

 theorem principalFrameLower_support {n : ℕ} (R : ℝ) (K : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (A : C1HolderSpace (End n) ((1:ℝ)/3))
    (hi : ∀ z, (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z).IsInvertible)
    (hout : ∀ z, R<‖z‖ → holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z=ContinuousLinearMap.id ℝ (Phase n))
    (z : ℂ) (hz : R<‖z‖) : holderValue ((1:ℝ)/3) (principalFrameLower R K A hi hout) z=0 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [principalFrameLower_value,constant_outside_fderiv R hout hz]
  simp

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
open HigherDimensionalBallPacking.Rigidity
local instance FrozenIsomorphismLocal1 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedAddCommGroup (HolderSpace ℂ E α) := inferInstance
local instance FrozenIsomorphismLocal2 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (α : ℝ) :
    NormedSpace ℝ (HolderSpace ℂ E α) := inferInstance
local instance FrozenIsomorphismLocal3 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :
    NormedAddCommGroup (C1HolderSpace E α) := inferInstance
local instance FrozenIsomorphismLocal4 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (α : ℝ) :
    NormedSpace ℝ (C1HolderSpace E α) := inferInstance
local instance FrozenIsomorphismLocal5 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedAddCommGroup (CompactHolderSpace E R) := inferInstance
local instance FrozenIsomorphismLocal6 (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (R : ℝ) :
    NormedSpace ℝ (CompactHolderSpace E R) := inferInstance

 theorem principalFrameLower_equation {n : ℕ} (R : ℝ) (K : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (A : C1HolderSpace (End n) ((1:ℝ)/3))
    (hi : ∀ z, (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z).IsInvertible)
    (hout : ∀ z, R<‖z‖ → holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z=ContinuousLinearMap.id ℝ (Phase n))
    (z : ℂ) (x : Phase n) :
    fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) z Complex.I x-
      holderValue ((1:ℝ)/3) K z (fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) z 1 x)=
        holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z
          (holderValue ((1:ℝ)/3) (principalFrameLower R K A hi hout) z x) := by
  let B := holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z
  let y := fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) z Complex.I x-
    holderValue ((1:ℝ)/3) K z (fderiv ℝ (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A)) z 1 x)
  have hh : holderValue ((1:ℝ)/3) (principalFrameLower R K A hi hout) z x=B.inverse y :=
    principalFrameLower_value R K A hi hout z x
  change y=B (holderValue ((1:ℝ)/3) (principalFrameLower R K A hi hout) z x)
  rw [hh]
  exact ((hi z).self_apply_inverse y).symm

 theorem normalizedHolderFrame_intertwines {n : ℕ} (K : C1HolderSpace (End n) ((1:ℝ)/3))
    (hK : ∀ z, Compatible (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) K) z)) (z : ℂ) (x : Phase n) :
    holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) (normalizedHolderFrame K)) z (Complex.I • x)=
      holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) K) z
        (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) (normalizedHolderFrame K)) z x) := by
  rw [normalizedHolderFrame_value]
  exact normalizedFrame_intertwines (hK z) x

 theorem compatible_frozen_solution {n : ℕ} (R : ℝ)
    (K : C1HolderSpace (End n) ((1:ℝ)/3))
    (hK : ∀ z, Compatible (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) K) z))
    (hout : ∀ z, R<‖z‖ → holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) K) z=standardJ n)
    (f : CompactHolderSpace (Phase n) R) :
    ∃ U : C1HolderSpace (Phase n) ((1:ℝ)/3),
      let u := holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) U)
      (∀ z, fderiv ℝ u z Complex.I-
        holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) K) z (fderiv ℝ u z 1)=compactHolderValue R f z) ∧
        Tendsto u (cocompact ℂ) (𝓝 0) := by
  let A := normalizedHolderFrame K
  have hAout : ∀ z, R<‖z‖ → holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z=ContinuousLinearMap.id ℝ (Phase n) := by
    intro z hz
    rw [normalizedHolderFrame_value,hout z hz,normalizedFrame_standard]
  have hi : ∀ z, (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) A) z).IsInvertible := by
    intro z
    rw [normalizedHolderFrame_value]
    exact normalizedFrame_invertible (hK z)
  let M := principalFrameLower R (c1HolderValue ((1:ℝ)/3) K) A hi hAout
  exact framed_frozen_solution R _ hK hout A M
    (principalFrameLower_support R _ A hi hAout) hAout hi
    (normalizedHolderFrame_intertwines K hK)
    (principalFrameLower_equation R _ A hi hAout) f

 theorem frozenPrincipal_injective {n : ℕ} (R : ℝ)
    (H : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) H z=0)
    (hK : ∀ z, Compatible (standardJ n+holderValue ((1:ℝ)/3) H z)) :
    Injective (frozenPrincipal R H hs) := by
  apply (LinearMap.ker_eq_bot (f := (frozenPrincipal R H hs).toLinearMap)).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro g hg
  apply compactCRInverse_frozen_kernel R (fun z => standardJ n+holderValue ((1:ℝ)/3) H z) hK g
  intro z
  change frozenPrincipal R H hs g=0 at hg
  have he := congrArg (fun g => compactHolderValue R g z) hg
  rw [frozenPrincipal_value] at he
  have hr := compactCRInverse_rightInverse R g z
  change fderiv ℝ (compactCRInverseValue R g) z Complex.I-
    standardJ n (fderiv ℝ (compactCRInverseValue R g) z 1)=_ at hr
  change compactHolderValue R g z-holderValue ((1:ℝ)/3) H z (fderiv ℝ (compactCRInverseValue R g) z 1)=0 at he
  rw [add_apply]
  have hh := sub_eq_zero.mp he
  rw [←hr] at hh
  exact sub_eq_iff_eq_add.mp hh |>.trans (add_comm _ _)

 theorem frozenPrincipal_surjective {n : ℕ} (R : ℝ)
    (K : C1HolderSpace (End n) ((1:ℝ)/3))
    (H : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) H z=0)
    (he : ∀ z, holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) K) z=standardJ n+holderValue ((1:ℝ)/3) H z)
    (hK : ∀ z, Compatible (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) K) z)) :
    Surjective (frozenPrincipal R H hs) := by
  intro f
  have ho (z : ℂ) (hz : R<‖z‖) :
      holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) K) z=standardJ n := by rw [he z,hs z hz,add_zero]
  obtain ⟨U,hU,hlim⟩ := compatible_frozen_solution R K hK ho f
  apply c1_potential_yields_frozen_density R H hs f U _ hlim
  intro z
  rw [←he z]
  exact hU z

 theorem frozenPrincipal_isInvertible {n : ℕ} (R : ℝ)
    (K : C1HolderSpace (End n) ((1:ℝ)/3))
    (H : HolderSpace ℂ (End n) ((1:ℝ)/3))
    (hs : ∀ z : ℂ, R<‖z‖ → holderValue ((1:ℝ)/3) H z=0)
    (he : ∀ z, holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) K) z=standardJ n+holderValue ((1:ℝ)/3) H z)
    (hK : ∀ z, Compatible (holderValue ((1:ℝ)/3) (c1HolderValue ((1:ℝ)/3) K) z)) :
    (frozenPrincipal R H hs).IsInvertible := by
  have hinj := frozenPrincipal_injective R H hs (fun z => he z ▸ hK z)
  have hsurj := frozenPrincipal_surjective R K H hs he hK
  exact ⟨ContinuousLinearEquiv.ofBijective (frozenPrincipal R H hs)
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj),rfl⟩

end HigherDimensionalBallPacking.Rigidity

end

end OAI
