import Mathlib
import OAI.Probability.Ballisticity.Estimates.FinitePastDecorrelation

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def jointPastGapMap {q : ℕ} : C(RealPathPair × JointPastTimes q,ℝ) where
  toFun z := z.1.1 z.2.2.1-z.1.2 z.2.2.1
  continuous_toFun := (continuous_eval.comp (continuous_fst.fst.prodMk continuous_snd.snd.fst)).sub
    (continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd.snd.fst))

noncomputable def jointCrossPastTest {q : ℕ} (F : (Fin q → ℝ × ℝ) →ᵇ ℝ)
    (G g : ℝ →ᵇ ℝ) : (RealPathPair × JointPastTimes q) →ᵇ ℝ :=
  ((jointPastProductTest F G 0).compContinuous (jointPastIncrementMap false))*
  (G.compContinuous ⟨fun z => (jointPastIncrementMap true z).2,
    continuous_snd.comp (jointPastIncrementMap true).continuous⟩)*
  (g.compContinuous jointPastGapMap)

lemma jointCrossPastTest_apply {q : ℕ} (F : (Fin q → ℝ × ℝ) →ᵇ ℝ)
    (G g : ℝ →ᵇ ℝ) (P : RealPathPair) (a : JointPastTimes q) :
    jointCrossPastTest F G g (P,a)=F (fun z => (P.1 (a.1 z),P.2 (a.1 z)))*
      (g (P.1 a.2.1-P.2 a.2.1)*(G (P.1 a.2.2-P.1 a.2.1)*G (P.2 a.2.2-P.2 a.2.1))) := by
  simp only [jointCrossPastTest,BoundedContinuousFunction.mul_apply,BoundedContinuousFunction.compContinuous_apply,
    jointPastProductTest,BoundedContinuousFunction.sub_apply,BoundedContinuousFunction.const_apply,
    jointPastIncrementMap,jointPastGapMap,ContinuousMap.coe_mk,Bool.false_eq_true,ite_false,ite_true,sub_zero]
  ring

lemma weak_joint_cross_past_integral {q : ℕ} (μ : ℕ → ProbabilityMeasure RealPathPair)
    (V : ProbabilityMeasure RealPathPair) (hμ : Tendsto μ atTop (𝓝 V))
    (a : ℕ → JointPastTimes q) (a₀ : JointPastTimes q) (ha : Tendsto a atTop (𝓝 a₀))
    (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (G g : ℝ →ᵇ ℝ) :
    Tendsto (fun i => ∫ P, jointCrossPastTest F G g (P,a i) ∂(μ i : Measure RealPathPair))
      atTop (𝓝 (∫ P, jointCrossPastTest F G g (P,a₀) ∂(V : Measure RealPathPair))) := by
  have hm := weak_map_varying_parameter μ V hμ a a₀ ha (fun z : RealPathPair × JointPastTimes q => z) continuous_id
  have hh := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hm) (jointCrossPastTest F G g)
  have he (U : ProbabilityMeasure RealPathPair) (u : JointPastTimes q) :
      (∫ z, jointCrossPastTest F G g z ∂(U.map (fun path => (path,u)) : Measure _)) =
      ∫ P, jointCrossPastTest F G g (P,u) ∂(U : Measure RealPathPair) := by
    change (∫ z, jointCrossPastTest F G g z ∂(U : Measure RealPathPair).map (fun P => (P,u))) = _
    exact integral_map ((continuous_id.prodMk continuous_const).measurable.aemeasurable)
      (jointCrossPastTest F G g).continuous.aestronglyMeasurable
  simpa only [he] using hh

lemma jointPastGapMap_grid {d q : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r n T : ℝ) (h : 0≤T*n) (x : Lattice d) (P : Path d × Path d)
    (H : ℕ) (a : JointPastTimes q) (hH : T*n*(a.2.1:ℝ)=H) :
    jointPastGapMap (sharedLinearPairPath ℓ f θ r n T x x P,a)=
      physicalFirstHitGap ℓ f x x H P/r := by
  change recordLinearPath ℓ f θ r n T (fun j => P.1 j-x) a.2.1-
    recordLinearPath ℓ f θ r n T (fun j => P.2 j-x) a.2.1 = _
  rw [recordLinearPath_grid ℓ f θ r n T h x P.1 H _ hH,
    recordLinearPath_grid ℓ f θ r n T h x P.2 H _ hH]
  have hz : signedCoordinate f (0 : Lattice d)=0 := by simp [signedCoordinate]
  simp only [physicalFirstHitGap,firstHitPairGap,sub_self,centeredFirstHit,hz,zero_add]
  simp only [sub_eq_add_neg,add_comm]
  ring

lemma jointCrossPastTest_grid {d q : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ r n T : ℝ) (h : 0≤T*n) (x : Lattice d) (P : Path d × Path d)
    (j : Fin q → ℕ) (H k : ℕ) (a : JointPastTimes q)
    (hj : ∀ z, T*n*(a.1 z:ℝ)=j z) (hH : T*n*(a.2.1:ℝ)=H)
    (hk : T*n*(a.2.2:ℝ)=H+k) (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (G g : ℝ →ᵇ ℝ) :
    jointCrossPastTest F G g (sharedLinearPairPath ℓ f θ r n T x x P,a)=
      F (centeredPastCoordinates ℓ f θ r j x x P)*
        (g (physicalFirstHitGap ℓ f x x H P/r)*
        (G (centeredHitIncrement ℓ f θ r H k x P.1)*G (centeredHitIncrement ℓ f θ r H k x P.2))) := by
  simp only [jointCrossPastTest,BoundedContinuousFunction.mul_apply,BoundedContinuousFunction.compContinuous_apply,
    ContinuousMap.coe_mk]
  rw [jointPastIncrementMap_grid ℓ f θ r n T h x x P j H k a hj hH hk false,
    jointPastIncrementMap_grid ℓ f θ r n T h x x P j H k a hj hH hk true,
    jointPastGapMap_grid ℓ f θ r n T h x P H a hH]
  simp only [jointPastProductTest,BoundedContinuousFunction.mul_apply,BoundedContinuousFunction.compContinuous_apply,
    BoundedContinuousFunction.sub_apply,BoundedContinuousFunction.const_apply,ContinuousMap.coe_mk,
    sub_zero,pairSide,Bool.false_eq_true,ite_false,ite_true]
  ring

end DirectionalTransience

end

end

end OAI
