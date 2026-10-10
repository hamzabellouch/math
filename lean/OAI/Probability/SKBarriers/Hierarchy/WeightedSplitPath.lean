import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarEarlyMoment
import OAI.Probability.SKBarriers.Replicas.TripleBaseFactor
import OAI.Probability.SKBarriers.Scalar.ScalarLevelRepresentation

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section Product
variable {E F : Type} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]

theorem vectorIncrementChain_prod_left (l : List (ℝ × E)) {f : E → ℝ} (hf : BoundedDerivs f) (g : F → ℝ) :
    vectorIncrementChain (l.map (fun p => (p.1,(p.2,(0:F))))) (fun p : E × F => f p.1+g p.2)=
      fun p => vectorIncrementChain l f p.1+g p.2 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons,vectorIncrementChain,ih]
    exact vectorStep_prod_left (vectorIncrementChain_regular l hf) _ _ _

theorem vectorIncrementAverage_prod_left (l : List (ℝ × E)) {f : E → ℝ} (hf : BoundedDerivs f)
    (g : F → ℝ) (a : E → ℝ) (b : F → ℝ) :
    vectorIncrementAverage (l.map (fun p => (p.1,(p.2,(0:F))))) (fun p : E × F => f p.1+g p.2)
      (fun p => a p.1*b p.2)=fun p => vectorIncrementAverage l f a p.1*b p.2 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons,vectorIncrementAverage,ih,vectorIncrementChain_prod_left l hf g]
    exact vectorStepAverage_prod_left _ _ _ _ _ _
end Product

abbrev MarkedWeightedState := (ℝ × ℝ) × ℝ

def weightedMarker : (ℝ × ℝ) →L[ℝ] MarkedWeightedState :=
  (ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod (ContinuousLinearMap.fst ℝ ℝ ℝ)

@[simp] theorem weightedMarker_apply (p : ℝ × ℝ) : weightedMarker p=(p,p.1) := rfl

def markedWeightedChain (c w : List (ℝ × (ℝ × ℝ))) : List (ℝ × MarkedWeightedState) :=
  c.map (fun p => (p.1,weightedMarker p.2))++w.map (fun p => (p.1,(p.2,0)))

theorem markedWeightedChain_average (c w : List (ℝ × (ℝ × ℝ)))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (g : ℝ × ℝ → ℝ) (U : ℝ → ℝ) (x : ℝ) :
    vectorIncrementAverage (markedWeightedChain c w) (fun p => f p.1.1) (fun p => g p.1*U p.2) ((x,0),x)=
      vectorIncrementAverage c (fun p => scalarIncrementChain (weightedUnderlying w) f p.1)
        (fun p => vectorIncrementAverage w (fun p => f p.1) g p*U p.1) (x,0) := by
  have hp : BoundedDerivs (fun p : ℝ × ℝ => f p.1) := hf.compCLM (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have he : (fun p : MarkedWeightedState => f p.1.1)=fun p => (fun q : ℝ × ℝ => f q.1) p.1+(fun _ : ℝ => 0) p.2 := by
    funext p; simp
  rw [markedWeightedChain,vectorIncrementAverage_append,he,vectorIncrementChain_prod_left w hp (fun _ : ℝ => 0),
    vectorIncrementAverage_prod_left w hp (fun _ : ℝ => 0)]
  simp only [add_zero,weightedBranch_value]
  have H := congrFun (vectorIncrementAverage_pullback weightedMarker c
    (fun p : MarkedWeightedState => scalarIncrementChain (weightedUnderlying w) f p.1.1)
    (fun p => vectorIncrementAverage w (fun q => f q.1) g p.1*U p.2)) (x,0)
  exact H.symm

theorem scalarLevelField_eq_prefix (n : ℕ) (v : Fin n → ℝ) (j : Fin (n+1)) (z : ParameterSpace n) :
    scalarLevelField n v j z=parameter n z+coordinateLinear n (scalarPrefixVector n v j) z := by
  induction n with
  | zero => simp [scalarLevelField,parameter,coordinateLinear]
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [scalarLevelField_last]
      change parameter (n+1) z+coordinateLinear (n+1) v z=_
      congr 2
      congr 1
      funext i
      simp only [scalarPrefixVector,Fin.val_last]
      exact (ite_eq_left (by omega)).symm
    · simp only [scalarLevelField,Fin.lastCases_castSucc,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ih]
      change parameter n z.1+coordinateLinear n _ z.1=parameter n z.1+coordinateLinear (n+1) _ z
      rw [coordinateLinear_apply,coordinateLinear_apply,Fin.sum_univ_castSucc]
      simp only [scalarPrefixVector,Fin.val_castSucc,Fin.val_last,ite_eq_right (show ¬ n<j.val by omega),zero_mul,add_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [coordinateProjection_castSucc]

end SK.Analytic

end
end

end OAI
