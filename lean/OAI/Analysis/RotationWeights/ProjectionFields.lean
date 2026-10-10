import OAI.Analysis.RotationWeights.Covariance

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set

open MeasureTheory Filter Set
open scoped ENNReal NNReal ComplexInnerProductSpace
local instance : MeasurableSpace FiberHilbert := borel FiberHilbert
local instance : BorelSpace FiberHilbert := ⟨rfl⟩
local instance : TopologicalSpace.SeparableSpace FiberHilbert := by
  apply TopologicalSpace.isSeparable_univ_iff.mp
  have h := ((Set.countable_range fiberBasis).isSeparable.span (R:=ℂ)).closure
  change TopologicalSpace.IsSeparable ((Submodule.span ℂ (Set.range fiberBasis)).topologicalClosure : Set FiberHilbert) at h
  simpa only [fiberBasis.dense_span,Submodule.top_coe] using h

lemma measurable_projection_version (T : CircleX → FiberOperator)
    (hm : ∀ k : ℤ,AEStronglyMeasurable (fun x => T x (lp.single 2 k 1)) AddCircle.haarAddCircle)
    (hp : ∀ᵐ x ∂AddCircle.haarAddCircle,IsStarProjection (T x)) :
    ∃ P : CircleX → FiberOperator, P=ᵐ[AddCircle.haarAddCircle] T ∧
      (∀ x,IsStarProjection (P x)) ∧ (∀ x,‖P x‖≤1) ∧
      ∀ k : ℤ,Measurable (fun x => P x (lp.single 2 k 1)) := by
  classical
  let F : ℤ → CircleX → FiberHilbert := fun k => (hm k).mk (fun x => T x (lp.single 2 k 1))
  have hgood : ∀ᵐ x ∂AddCircle.haarAddCircle,(∀ k : ℤ,T x (lp.single 2 k 1)=F k x) ∧ IsStarProjection (T x) := by
    filter_upwards [ae_all_iff.mpr (fun k => (hm k).ae_eq_mk),hp] with x hx hpx
    exact ⟨hx,hpx⟩
  obtain ⟨N,hN,hmN,hzN⟩ := exists_measurable_superset_of_null (ae_iff.mp hgood)
  have hn (x : CircleX) (hx : x∉N) : (∀ k : ℤ,T x (lp.single 2 k 1)=F k x) ∧ IsStarProjection (T x) := by
    by_contra h
    exact hx (hN h)
  let P : CircleX → FiberOperator := fun x => if x∈N then 0 else T x
  have hPP (x : CircleX) : IsStarProjection (P x) := by
    by_cases hx : x∈N
    · simp only [P,ite_eq_left hx]; exact IsStarProjection.zero _
    · simpa only [P,ite_eq_right hx] using (hn x hx).2
  refine ⟨P,?_,hPP,fun x => (hPP x).norm_le,?_⟩
  · filter_upwards [(show ∀ᵐ x ∂AddCircle.haarAddCircle,x∉N from (ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hzN)))] with x hx
    exact ite_eq_right hx
  · intro k
    have he : (fun x => P x (lp.single 2 k 1))=(fun x => if x∈N then 0 else F k x) := by
      funext x
      by_cases hx : x∈N
      · simp [P,hx]
      · simpa only [P,ite_eq_right hx] using (hn x hx).1 k
    rw [he]
    exact Measurable.ite hmN measurable_const (hm k).measurable_mk

lemma fiber_commutes_indicators (θ : ℝ) (A : CircleFiberOperator)
    (hA : ∀ B∈fiberCommutant θ,Commute A B) (s : Set CircleX) (hs : MeasurableSet s) :
    A.comp (indicatorV2 AddCircle.haarAddCircle s hs)=(indicatorV2 AddCircle.haarAddCircle s hs).comp A := by
  have h := regular_doubleCentralizer_indicators θ (fiberConjugacy.symm A) (regularAlgebra_of_commutes θ A hA) s hs
  change fiberConjugacy (fiberConjugacy.symm A)*_=_*fiberConjugacy (fiberConjugacy.symm A) at h
  change A*indicatorV2 AddCircle.haarAddCircle s hs=indicatorV2 AddCircle.haarAddCircle s hs*A
  simpa only [fiberConjugacy.apply_symm_apply] using h
lemma fiber_commutes_circleJ (θ : ℝ) (A : CircleFiberOperator)
    (hA : ∀ B∈fiberCommutant θ,Commute A B) (n : ℤ) : A*circleJ (θ:CircleX) n=circleJ (θ:CircleX) n*A := by
  have h := regular_doubleCentralizer_circleJ θ (fiberConjugacy.symm A) (regularAlgebra_of_commutes θ A hA) n
  change fiberConjugacy (fiberConjugacy.symm A)*_=_*fiberConjugacy (fiberConjugacy.symm A) at h
  simpa only [fiberConjugacy.apply_symm_apply] using h

theorem extract_projection_field (θ : ℝ) (A : CircleFiberOperator) (hA : IsStarProjection A)
    (hcomm : ∀ B∈fiberCommutant θ,Commute A B) :
    ∃ P : CircleX → FiberOperator,
      (∀ x,IsStarProjection (P x)) ∧ (∀ x,‖P x‖≤1) ∧
      (∀ k : ℤ,Measurable (fun x => P x (lp.single 2 k 1))) ∧
      (∀ u : CircleFiberL2,∀ᵐ x ∂AddCircle.haarAddCircle,(A u) x=P x (u x)) ∧
      ∀ n : ℤ,∀ᵐ x ∂AddCircle.haarAddCircle,
        P x*(fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap=
          (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap*P (x+n•(θ:CircleX)) := by
  obtain ⟨T,_hbound,hm,hT⟩ := commutes_indicators_decomposable AddCircle.haarAddCircle A (fiber_commutes_indicators θ A hcomm)
  have hTproj : ∀ᵐ x ∂AddCircle.haarAddCircle,IsStarProjection (T x) := by
    filter_upwards [decomposable_idempotent AddCircle.haarAddCircle A T hT hA.isIdempotentElem,
      decomposable_selfAdjoint AddCircle.haarAddCircle A T hT (fiber_commutes_indicators θ A hcomm) hA.isSelfAdjoint] with x h1 h2
    exact ⟨h1,h2⟩
  obtain ⟨P,hPT,hPproj,hPbound,hPmeas⟩ := measurable_projection_version T (fun k => hm _) hTproj
  have hP (u : CircleFiberL2) : ∀ᵐ x ∂AddCircle.haarAddCircle,(A u) x=P x (u x) := by
    filter_upwards [hT u,hPT] with x hx hpx
    rw [hpx]; exact hx
  refine ⟨P,hPproj,hPbound,hPmeas,hP,fun n => ?_⟩
  exact decomposable_covariance AddCircle.haarAddCircle (fun x : CircleX => x+n•(θ:CircleX))
    (measurePreserving_add_right AddCircle.haarAddCircle (n•(θ:CircleX))) _ A P hP (fiber_commutes_circleJ θ A hcomm n)

def borelWeightedField (θ : CircleX) (g : RealBorel) (x : CircleX) : FiberOperator :=
  (fiberShift 1).toContinuousLinearEquiv.toContinuousLinearMap * realPiField θ g x
lemma borelWeightedField_coe (θ : CircleX) (g : RealBorel) (u : CircleFiberL2) :
    (fiberShiftL2 1*realPi θ g) u=ᵐ[AddCircle.haarAddCircle] fun x => borelWeightedField θ g x (u x) := by
  filter_upwards [fiberShiftL2_coe 1 (realPi θ g u),realPi_coe θ g u] with x h1 h2
  change (fiberShiftL2 1 (realPi θ g u)) x=_
  rw [h1,h2]
  rfl
lemma decomposable_one_sub (A : CircleFiberOperator) (P : CircleX → FiberOperator)
    (hP : ∀ u : CircleFiberL2,∀ᵐ x ∂AddCircle.haarAddCircle,(A u) x=P x (u x))
    (u : CircleFiberL2) : ∀ᵐ x ∂AddCircle.haarAddCircle,((1-A) u) x=(1-P x) (u x) := by
  filter_upwards [Lp.coeFn_sub u (A u),hP u] with x h1 h2
  change (u-A u) x=_
  rw [h1]
  simp only [Pi.sub_apply,h2]
  rfl
lemma decomposable_invariant (A : CircleFiberOperator) (P : CircleX → FiberOperator)
    (hP : ∀ u : CircleFiberL2,∀ᵐ x ∂AddCircle.haarAddCircle,(A u) x=P x (u x))
    (θ : CircleX) (g : RealBorel) (hinv : (1-A)*(fiberShiftL2 1*realPi θ g)*A=0) :
    ∀ᵐ x ∂AddCircle.haarAddCircle,(1-P x)*borelWeightedField θ g x*P x=0 := by
  apply ae_field_eq_of_dense AddCircle.haarAddCircle
  intro u
  have h := decomposable_mul AddCircle.haarAddCircle ((1-A)*(fiberShiftL2 1*realPi θ g)) A
    (fun x => (1-P x)*borelWeightedField θ g x) P
    (decomposable_mul AddCircle.haarAddCircle _ _ _ _ (decomposable_one_sub A P hP) (borelWeightedField_coe θ g)) hP
  have hc := decomposable_const AddCircle.haarAddCircle _ _ h u
  filter_upwards [hc,Lp.coeFn_zero FiberHilbert 2 AddCircle.haarAddCircle] with x hx hz
  rw [hinv] at hx
  exact hx.symm.trans hz

lemma realPiField_proj_eigen (θ : CircleX) (g : RealBorel) (x : CircleX) :
    realPiField θ g x (lp.single 2 0 1)=(g x:ℂ)•lp.single 2 0 1 ∧
    (star (realPiField θ g x)) (lp.single 2 0 1)=(g x:ℂ)•lp.single 2 0 1 := by
  have h1 : realPiField θ g x (lp.single 2 0 1)=(g x:ℂ)•lp.single 2 0 1 := by
    ext k
    by_cases hk : k=0
    · subst k; simp only [realPiField_apply,zero_zsmul,add_zero,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.single_apply,Pi.single_eq_same,mul_one]
    · simp only [realPiField_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.single_apply,Pi.single_eq_of_ne hk,mul_zero]
  refine ⟨h1,?_⟩
  have hs : IsSelfAdjoint (realPiField θ g x) := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (realPiField_symmetric θ g x)
  rw [hs.star_eq]
  exact h1
lemma weighted_invariant_diagonal (P Q D : FiberOperator)
    (hcov : P*(fiberShift 1).toContinuousLinearEquiv.toContinuousLinearMap=
      (fiberShift 1).toContinuousLinearEquiv.toContinuousLinearMap*Q)
    (hinv : (1-P)*((fiberShift 1).toContinuousLinearEquiv.toContinuousLinearMap*D)*P=0) :
    (1-Q)*D*P=0 := by
  have he : (1-P)*((fiberShift 1).toContinuousLinearEquiv.toContinuousLinearMap*D)*P=
      (fiberShift 1).toContinuousLinearEquiv.toContinuousLinearMap*((1-Q)*D*P) := by
    simp only [sub_mul,mul_sub,one_mul,mul_assoc]
    rw [←mul_assoc P, hcov, mul_assoc]
  rw [he] at hinv
  apply ContinuousLinearMap.ext
  intro u
  apply (fiberShift 1).injective
  exact (DFunLike.congr_fun hinv u).trans (map_zero _).symm

lemma borel_invariant_diagonal_strict (θ : ℝ)
    (hθ : Ergodic (fun x : CircleX => x+(θ:CircleX)) AddCircle.haarAddCircle)
    (A : CircleFiberOperator) (P : CircleX → FiberOperator)
    (hP : ∀ u : CircleFiberL2,∀ᵐ x ∂AddCircle.haarAddCircle,(A u) x=P x (u x))
    (hproj : ∀ x,IsStarProjection (P x))
    (hcov : ∀ n : ℤ,∀ᵐ x ∂AddCircle.haarAddCircle,P x*(fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap=
      (fiberShift n).toContinuousLinearEquiv.toContinuousLinearMap*P (x+n•(θ:CircleX)))
    (g : RealBorel) (hg : ∀ x,g x≠0)
    (hinv : (1-A)*(fiberShiftL2 1*realPi (θ:CircleX) g)*A=0) (hA0 : A≠0) (hA1 : A≠1) :
    ∀ᵐ x ∂AddCircle.haarAddCircle,0<(inner ℂ (lp.single 2 0 1) (P x (lp.single 2 0 1))).re ∧
      (inner ℂ (lp.single 2 0 1) (P x (lp.single 2 0 1))).re<1 := by
  apply invariant_covariant_diagonal_strict (θ:CircleX) hθ A P hP (Eventually.of_forall hproj) hcov
    (realPiField (θ:CircleX) g) (fun x => (g x:ℂ))
    (Eventually.of_forall (fun x => Complex.ofReal_ne_zero.mpr (hg x)))
    (Eventually.of_forall (realPiField_proj_eigen (θ:CircleX) g)) _ hA0 hA1
  filter_upwards [decomposable_invariant A P hP (θ:CircleX) g hinv,hcov 1] with x hi hc
  rw [one_zsmul] at hc
  exact weighted_invariant_diagonal _ _ _ hc hi


end ContinuousCircleWeight

end

end OAI
