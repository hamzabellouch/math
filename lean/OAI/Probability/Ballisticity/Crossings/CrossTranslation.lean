import Mathlib
import OAI.Probability.Ballisticity.Estimates.PairPrefix

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma cross_translation {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ) :
    (fun X : Path d => fun n => X n-x) ⁻¹' Cross ℓ 0 H = Cross ℓ x H := by
  ext X
  have hzero : dot (realPosition (0 : Lattice d)) ℓ = 0 := by simp [dot,realPosition]
  simp only [Cross,Set.mem_preimage,Set.mem_ofPred_eq,hzero,zero_add,dot_realPosition_sub]
  constructor
  · rintro ⟨n,hn,hpre⟩
    exact ⟨n,by linarith,fun j hj => by have := hpre j hj; linarith⟩
  · rintro ⟨n,hn,hpre⟩
    exact ⟨n,by linarith,fun j hj => by have := hpre j hj; linarith⟩

lemma annealedFrom_cross_error_translation {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x : Lattice d) (H : ℝ) :
    annealedFrom ν x (Cross ℓ x H \ NoDrop ℓ x) =
      annealedLaw ν (Cross ℓ 0 H \ NoDrop ℓ 0) := by
  have hm := (measurableSet_cross ℓ 0 H).diff (measurableSet_noDrop ℓ 0)
  have hp : (fun X : Path d => fun n => X n-x) ⁻¹' (Cross ℓ 0 H \ NoDrop ℓ 0) =
      Cross ℓ x H \ NoDrop ℓ x := by
    rw [Set.preimage_sdiff,cross_translation,noDrop_translation]
    simp only [add_zero]
  rw [annealedFrom_apply ν x _ ((measurableSet_cross ℓ x H).diff (measurableSet_noDrop ℓ x)),← hp]
  exact annealed_event_translation ν x _ hm

lemma cross_error_tendsto_zero {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) :
    Tendsto (fun H : ℕ => annealedLaw ν (Cross ℓ 0 H \ NoDrop ℓ 0)) atTop (𝓝 0) := by
  have he : (⋂ H : ℕ, Cross ℓ 0 H \ NoDrop ℓ 0) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro X hX
    exact (Set.mem_iInter.mp hX 0).2 (iInter_cross_subset_noDrop ℓ 0
      (Set.mem_iInter.mpr fun H => (Set.mem_iInter.mp hX H).1))
  have hh := tendsto_measure_iInter_atTop (μ := annealedLaw ν)
    (s := fun H : ℕ => Cross ℓ 0 H \ NoDrop ℓ 0)
    (fun H => ((measurableSet_cross ℓ 0 H).diff (measurableSet_noDrop ℓ 0)).nullMeasurableSet)
    (fun H K h => Set.sdiff_subset_sdiff_left (cross_antitone ℓ 0 (Nat.cast_le.mpr h)))
    ⟨0,measure_ne_top _ _⟩
  simpa only [he,measure_empty,Function.comp_def] using hh

lemma pair_cross_noDrop_error_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x y : Lattice d) (H : ℝ) (μ : Measure (Path d × Path d))
    (hx : μ.map Prod.fst = annealedFrom ν x) (hy : μ.map Prod.snd = annealedFrom ν y) :
    μ ((Cross ℓ x H ×ˢ Cross ℓ y H) \ (NoDrop ℓ x ×ˢ NoDrop ℓ y)) ≤
      2*annealedLaw ν (Cross ℓ 0 H \ NoDrop ℓ 0) := by
  have hm z := (measurableSet_cross ℓ z H).diff (measurableSet_noDrop ℓ z)
  calc
    _ ≤ μ (Prod.fst ⁻¹' (Cross ℓ x H \ NoDrop ℓ x)) +
        μ (Prod.snd ⁻¹' (Cross ℓ y H \ NoDrop ℓ y)) := by
      apply (measure_mono (s := _) (t := (Prod.fst ⁻¹' (Cross ℓ x H \ NoDrop ℓ x)) ∪
        (Prod.snd ⁻¹' (Cross ℓ y H \ NoDrop ℓ y))) ?_).trans (measure_union_le _ _)
      intro P hP
      by_cases hD : P.1 ∈ NoDrop ℓ x
      · exact Or.inr ⟨hP.1.2,fun h => hP.2 ⟨hD,h⟩⟩
      · exact Or.inl ⟨hP.1.1,hD⟩
    _ = annealedFrom ν x (Cross ℓ x H \ NoDrop ℓ x) +
        annealedFrom ν y (Cross ℓ y H \ NoDrop ℓ y) := by
      rw [← Measure.map_apply measurable_fst (hm x),← Measure.map_apply measurable_snd (hm y),hx,hy]
    _ = _ := by rw [annealedFrom_cross_error_translation,annealedFrom_cross_error_translation,two_mul]

lemma shared_cross_noDrop_error_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x y : Lattice d) (H : ℝ) :
    sharedPairLaw ν x y ((Cross ℓ x H ×ˢ Cross ℓ y H) \ (NoDrop ℓ x ×ˢ NoDrop ℓ y)) ≤
      2*annealedLaw ν (Cross ℓ 0 H \ NoDrop ℓ 0) :=
  pair_cross_noDrop_error_bound ν ℓ x y H _ (sharedPairLaw_fst ν x y) (sharedPairLaw_snd ν x y)

lemma independent_cross_noDrop_error_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x y : Lattice d) (H : ℝ) :
    ((annealedFrom ν x).prod (annealedFrom ν y))
      ((Cross ℓ x H ×ˢ Cross ℓ y H) \ (NoDrop ℓ x ×ˢ NoDrop ℓ y)) ≤
      2*annealedLaw ν (Cross ℓ 0 H \ NoDrop ℓ 0) := by
  apply pair_cross_noDrop_error_bound ν ℓ x y H
  · simp only [Measure.map_fst_prod,measure_univ,one_smul]
  · simp only [Measure.map_snd_prod,measure_univ,one_smul]

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
