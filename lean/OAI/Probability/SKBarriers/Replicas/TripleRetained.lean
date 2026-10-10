import Mathlib
import OAI.Probability.SKBarriers.Replicas.TripleSchedule
import OAI.Probability.SKBarriers.Replicas.TripleRecursiveExpansion

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

abbrev TripleRetainedState := (ℝ × ℝ) × ℝ

def retainedSingleton : TripleRetainedState →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)
def retainedNoise : TripleRetainedState →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)
def retainedPair : TripleRetainedState →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ

def tripleRetainedEmbedding (δ : ℝ) : TripleRetainedState →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![retainedSingleton,retainedPair+δ • retainedNoise,retainedPair-δ • retainedNoise]

@[simp] theorem tripleRetainedEmbedding_apply (δ : ℝ) (x : TripleRetainedState) :
    tripleRetainedEmbedding δ x=![x.1.1,x.2+δ*x.1.2,x.2-δ*x.1.2] := by
  funext i; fin_cases i <;> rfl

def tripleRetainedCommon (c : List (ℝ × ℝ)) : List (ℝ × TripleRetainedState) :=
  c.map (fun p => (p.1/3,((p.2,0),p.2)))

def tripleRetainedMiddle (l : List TripleMiddleIncrement) : List (ℝ × TripleRetainedState) :=
  l.map (fun p => (productMass p,productVector p))

theorem tripleRetainedCommon_image (δ : ℝ) (c : List (ℝ × ℝ)) :
    (tripleRetainedCommon c).map (fun p => (p.1,tripleRetainedEmbedding δ p.2))=tripleCommonSchedule c := by
  simp [tripleRetainedCommon,tripleCommonSchedule,List.map_map,Function.comp_def]

theorem tripleRetainedMiddle_image (δ : ℝ) (l : List TripleMiddleIncrement) :
    (tripleRetainedMiddle l).map (fun p => (p.1,tripleRetainedEmbedding δ p.2))=tripleMiddleSchedule δ l := by
  simp only [tripleRetainedMiddle,tripleMiddleSchedule,List.map_map]
  apply List.map_congr_left
  intro p hp
  cases p <;> simp [productVector,tripleMiddleVector,tripleRetainedEmbedding_apply]

theorem retained_sum_coordinates (n : ℕ) (v : Fin n → TripleRetainedState) (z : ParameterSpace n) :
    (∑ i,coordinateProjection n i z • v i)=
      ((coordinateLinear n (fun i => (v i).1.1) z,coordinateLinear n (fun i => (v i).1.2) z),
        coordinateLinear n (fun i => (v i).2) z) := by
  apply Prod.ext
  · apply Prod.ext
    · simpa only [retainedSingleton,retainedNoise,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',
        Prod.smul_fst,smul_eq_mul,coordinateLinear_apply,mul_comm] using
          map_sum retainedSingleton (fun i => coordinateProjection n i z • v i) Finset.univ
    · simpa only [retainedSingleton,retainedNoise,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd',Prod.smul_fst,Prod.smul_snd,smul_eq_mul,coordinateLinear_apply,mul_comm] using
          map_sum retainedNoise (fun i => coordinateProjection n i z • v i) Finset.univ
  · simpa only [retainedPair,ContinuousLinearMap.coe_snd',Prod.smul_snd,smul_eq_mul,coordinateLinear_apply,mul_comm] using
      map_sum retainedPair (fun i => coordinateProjection n i z • v i) Finset.univ

theorem tripleRetained_pressure (n : ℕ) (m : Fin n → ℝ) (v : Fin n → TripleRetainedState)
    (f : ℝ → ℝ) (δ : ℝ) :
    vectorHierarchy n m (fun i => tripleRetainedEmbedding δ (v i))
      (fun x : Fin 3 → ℝ => f (x 0)+f (x 1)+f (x 2)) 0=
      hierarchyPressure n m (tripleModifiedBoundary f (coordinateLinear n (fun i => (v i).1.1))
        (coordinateLinear n (fun i => (v i).2)) (coordinateLinear n (fun i => (v i).1.2)) δ) 0 := by
  have H := congrFun (hierarchyPressure_vector_linear n m v
    (fun x : TripleRetainedState => f x.1.1+f (x.2+δ*x.1.2)+f (x.2-δ*x.1.2)) (fun _ => 0)) 0
  simp only [zero_add,retained_sum_coordinates] at H
  have HT := congrFun (vectorHierarchy_pullback (tripleRetainedEmbedding δ) n m v
    (fun x : Fin 3 → ℝ => f (x 0)+f (x 1)+f (x 2))) 0
  simp only [Function.comp_def,tripleRetainedEmbedding_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,map_zero] at HT
  unfold tripleModifiedBoundary
  simpa only [tripleRetainedEmbedding_apply] using HT.symm.trans H.symm

end SK.Analytic

end
end

end OAI
