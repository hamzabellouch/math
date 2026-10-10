import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarWeightedMean
import OAI.Probability.SKBarriers.Hierarchy.WeightedSplitPath

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def markedScalarVector (n : ℕ) (v a : Fin n → ℝ) (j : Fin (n+1)) (i : Fin n) : MarkedWeightedState :=
  ((v i,a i),scalarPrefixVector n v j i)

theorem markedScalarField_eq (n : ℕ) (v a : Fin n → ℝ) (j : Fin (n+1)) (z : ParameterSpace n) :
    ((parameter n z,0),parameter n z)+∑ i,coordinateProjection n i z • markedScalarVector n v a j i=
      ((scalarSpinField n v z,coordinateLinear n a z),scalarLevelField n v j z) := by
  apply Prod.ext
  · have H := map_sum (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)
      (fun i => coordinateProjection n i z • markedScalarVector n v a j i) Finset.univ
    calc
      _ = (parameter n z,0)+∑ i,coordinateProjection n i z • (v i,a i) := by
        simpa only [ContinuousLinearMap.coe_fst',Prod.smul_fst,markedScalarVector,Prod.fst_add]
          using congrArg ((parameter n z,0)+·) H
      _ = _ := scalarWeightedField_eq n v a z
  · have H := map_sum (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ)
      (fun i => coordinateProjection n i z • markedScalarVector n v a j i) Finset.univ
    simpa only [ContinuousLinearMap.coe_snd',Prod.smul_snd,markedScalarVector,Prod.snd_add,smul_eq_mul,
      scalarLevelField_eq_prefix,coordinateLinear_apply,mul_comm] using congrArg (parameter n z+·) H

theorem markedScalarTest_integral (n : ℕ) (m v a : Fin n → ℝ) (j : Fin (n+1))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) {g : MarkedWeightedState → ℝ}
    (hg : Continuous g) (hE : HasExpGrowth g) (x : ℝ) :
    vectorHierarchyAverage n m (markedScalarVector n v a j) (fun p => f p.1.1) g ((x,0),x)=
      ∫ z,g ((scalarSpinField n v z,coordinateLinear n a z),scalarLevelField n v j z)
        ∂hierarchyPathLaw n m (f ∘ scalarSpinField n v) x := by
  have H := congrFun (hierarchyAverage_vector_linear n m (markedScalarVector n v a j)
    (fun p => f p.1.1) g (fun x => ((x,0),x))) x
  simp only [markedScalarField_eq] at H
  rw [← H]
  exact hierarchyAverage_eq_integral_exp n m _ (hf.compCLM (scalarSpinField n v)) _
    (hg.comp (((scalarSpinField n v).prod (coordinateLinear n a)).prod (scalarLevelField n v j)).continuous)
    (hE.compCLM (((scalarSpinField n v).prod (coordinateLinear n a)).prod (scalarLevelField n v j))) x

theorem markedWeightedChain_ofFn (c w : List (ℝ × (ℝ × ℝ))) :
    markedWeightedChain c w=List.ofFn (fun i : Fin (c++w).length =>
      ((c++w).get i |>.1,markedScalarVector (c++w).length
        (fun i => ((c++w).get i).2.1) (fun i => ((c++w).get i).2.2)
        ⟨c.length,by simp only [List.length_append]; omega⟩ i)) := by
  apply List.ext_getElem
  · simp [markedWeightedChain]
  · intro i hi hj
    simp only [List.getElem_ofFn,markedScalarVector,scalarPrefixVector,List.get_eq_getElem]
    by_cases h : i<c.length
    · simp only [markedWeightedChain]
      rw [List.getElem_append_left (by simpa only [List.length_map] using h)]
      simp only [List.getElem_map,List.getElem_append_left h,ite_eq_left h,weightedMarker_apply,Prod.mk.eta]
    · have h' : c.length ≤ i := by omega
      simp only [markedWeightedChain]
      rw [List.getElem_append_right (by simpa only [List.length_map] using h')]
      simp only [List.getElem_map,List.length_map,List.getElem_append_right h',ite_eq_right h,Prod.mk.eta]

theorem weightedSplit_integral (c w : List (ℝ × (ℝ × ℝ)))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (g : ℝ × ℝ → ℝ) (U : ℝ → ℝ)
    (hg : Continuous (fun p : MarkedWeightedState => g p.1*U p.2))
    (hE : HasExpGrowth (fun p : MarkedWeightedState => g p.1*U p.2)) (x : ℝ) :
    vectorIncrementAverage c (fun p => scalarIncrementChain (weightedUnderlying w) f p.1)
      (fun p => vectorIncrementAverage w (fun p => f p.1) g p*U p.1) (x,0)=
      ∫ z, g (scalarSpinField (c++w).length (fun i => ((c++w).get i).2.1) z,
          coordinateLinear (c++w).length (fun i => ((c++w).get i).2.2) z)*
        U (scalarLevelField (c++w).length (fun i => ((c++w).get i).2.1)
          ⟨c.length,by simp only [List.length_append]; omega⟩ z)
        ∂hierarchyPathLaw (c++w).length (fun i => ((c++w).get i).1)
          (f ∘ scalarSpinField (c++w).length (fun i => ((c++w).get i).2.1)) x := by
  rw [← markedWeightedChain_average c w hf g U x,markedWeightedChain_ofFn,vectorIncrementAverage_ofFn]
  exact markedScalarTest_integral _ _ _ _ _ hf hg hE x

end SK.Analytic

end
end

end OAI
