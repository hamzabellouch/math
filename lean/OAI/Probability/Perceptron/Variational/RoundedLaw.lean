import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityLabelArray
import OAI.Probability.Perceptron.Variational.OrderedCode
import OAI.Probability.Perceptron.Variational.DepthGG
import OAI.Probability.Perceptron.Cascade.DepthWeights
import OAI.Probability.Perceptron.Interpolation.ArrayLawExt

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction

def roundedLevelCode (q : BoundedField 1) (n : ℕ) (r : Time) :
    Fin ((strictRoundModel q n).depth+1) :=
  orderedLevelCode (strictRoundModel q n).value (roundLower n r)

lemma roundedLevelCode_measurable (q : BoundedField 1) (n : ℕ) :
    Measurable (roundedLevelCode q n) :=
  (orderedLevelCode_measurable _).comp ((roundLower_measurable n).comp measurable_subtype_coe)

lemma roundedLevelCode_mono (q : BoundedField 1) (n : ℕ) : Monotone (roundedLevelCode q n) :=
  (orderedLevelCode_mono _).comp ((roundLower_monotone n).comp (Subtype.mono_coe _))

theorem indexedDepthLaw_eq_rounded_bulk
    (μ : ProbabilityMeasure (CompactArray Time)) (q : Time → Time) (hq : Monotone q)
    (hpair : (μ : Measure (CompactArray Time)).map (fun Q => Q 0 1) = timeLaw.map q)
    (hGG : ∀ n (i : Fin n) (F : CompactBlock Time n →ᵇ ℝ) (g : Time →ᵇ ℝ),
      compactGGDefect μ n i F g = 0)
    (hgeo : ∀ᵐ Q ∂(μ : Measure (CompactArray Time)),
      (∀ i j, Q i j = Q j i) ∧ (∀ i, Q i i = 1) ∧
      ∀ i j l, min (Q i j) (Q i l) ≤ Q j l) (n : ℕ) :
    (indexedDepthLaw (strictRoundModel (unitQuantileField q hq) n).depth
      (stepCumulative (strictRoundModel (unitQuantileField q hq) n).weight) :
        Measure (FiniteOverlap (Fin ((strictRoundModel (unitQuantileField q hq) n).depth+1)))) =
      (μ : Measure (CompactArray Time)).map (finiteCodeArray (roundedLevelCode (unitQuantileField q hq) n)) := by
  let f := unitQuantileField q hq
  let M := strictRoundModel f n
  let χ := roundedLevelCode f n
  let ν := (μ : Measure (CompactArray Time)).map (finiteCodeArray χ)
  let ρ := (indexedDepthLaw M.depth (stepCumulative M.weight) :
    Measure (FiniteOverlap (Fin (M.depth+1))))
  have hm := finiteCodeArray_measurable (roundedLevelCode_measurable f n)
  have : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  have hν : ∀ᵐ R ∂ν, (∀ i j, R i j = R j i) ∧ (∀ i, R i i = Fin.last M.depth) ∧
      ∀ i j l, min (R i j) (R i l) ≤ R j l := by
    apply (ae_map_iff hm.aemeasurable (by measurability)).mpr
    filter_upwards [hgeo] with Q hQ
    refine ⟨fun i j => congrArg χ (hQ.1 i j),?_,?_⟩
    · intro i
      change χ (Q i i) = _
      rw [hQ.2.1 i]
      exact orderedRoundCode_one f n
    · intro i j l
      have hχ : Monotone χ := roundedLevelCode_mono f n
      have hx := hχ (hQ.2.2 i j l)
      change min (χ (Q i j)) (χ (Q i l)) ≤ χ (Q j l)
      by_cases hab : Q i j ≤ Q i l
      · simpa only [min_eq_left hab,min_eq_left (hχ hab)] using hx
      · have hba := le_of_not_ge hab
        simpa only [min_eq_right hba,min_eq_right (hχ hba)] using hx
  have hp : ν.map (fun R => R 0 1) = timeLaw.map M.label := by
    change ((μ : Measure (CompactArray Time)).map (finiteCodeArray χ)).map _ = _
    rw [Measure.map_map (by fun_prop) hm]
    have he : (fun R : FiniteOverlap (Fin (M.depth+1)) => R 0 1) ∘ finiteCodeArray χ =
        χ ∘ (fun Q : CompactArray Time => Q 0 1) := rfl
    rw [he,← Measure.map_map (roundedLevelCode_measurable f n) (by fun_prop),hpair,
      Measure.map_map (roundedLevelCode_measurable f n) hq.measurable]
    apply Measure.map_congr
    exact orderedRoundCode_label f n
  have hpa (c : Fin (M.depth+1)) : ρ.real {R | R 0 1 = c} = ν.real {R | R 0 1 = c} := by
    have hh := congrArg (fun η : Measure (Fin (M.depth+1)) => η.real {c}) hp
    rw [map_measureReal_apply (by fun_prop) (measurableSet_singleton c),
      map_measureReal_apply M.measurable_label (measurableSet_singleton c)] at hh
    rw [indexedDepthLaw_pair_weights M.depth M.weight M.weight_pos M.weight_sum]
    exact hh.symm
  apply array_law_eq_of_blocks ρ ν
  exact finiteGG_block_law_unique ρ ν (Fin.last M.depth)
    (indexedDepthLaw_geometry M.depth _) hν
    (indexedDepthLaw_finiteGG M.depth _ (stepCumulative_strictMono M.weight M.weight_pos)
      (stepCumulative_pos M.weight M.weight_pos) (stepCumulative_lt_one M.weight M.weight_pos M.weight_sum))
    (compactGG_finite_pushforward_general μ hGG (roundedLevelCode_measurable f n)) hpa

def depthMarkedDecode {K : Type*} {k : ℕ} (p : Fin (k+1) → K) (D : K)
    (R : FiniteOverlap (Fin (k+1))) : CompactArray K :=
  fun i j => if i = j then D else p (R i j)

lemma depthMarkedDecode_measurable {K : Type*} [MeasurableSpace K] {k : ℕ}
    (p : Fin (k+1) → K) (D : K) : Measurable (depthMarkedDecode p D) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  unfold depthMarkedDecode
  split_ifs
  · exact measurable_const
  · exact (measurable_of_countable p).comp ((measurable_pi_apply j).comp (measurable_pi_apply i))

lemma gibbsProbabilityKernel_zero {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
    (κ : Kernel A S) [IsMarkovKernel κ] :
    gibbsProbabilityKernel κ (fun _ _ => 0) = κ := by
  ext a : 1
  rw [gibbsProbabilityKernel_of_integrable κ (fun _ _ => 0) measurable_const a (integrable_const _)]
  simp only [tiltLaw,tiltPartition,mul_zero,Real.exp_zero,integral_const,probReal_univ,one_smul,
    ENNReal.ofReal_one,inv_one]
  exact withDensity_one

lemma annealedInfiniteReplicaMeasure_zero {A S : Type*} [MeasurableSpace A] [MeasurableSpace S]
    (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P] :
    annealedInfiniteReplicaMeasure κ P (fun _ _ => 0) measurable_const =
      P ⊗ₘ kernelInfiniteReplica κ ℕ := by
  simp only [annealedInfiniteReplicaMeasure,gibbsProbabilityKernel_zero]

theorem cavityLabelMarkedLaw_eq_depth {K : ℝ} {k : ℕ}
    (p : Fin (k+1) → BulkPairRange K) (D : BulkPairRange K) (z : Fin k → ℝ) :
    (cavityLabelMarkedLaw p D z : Measure (CompactArray (BulkPairRange K))) =
      (indexedDepthLaw k z : Measure (FiniteOverlap (Fin (k+1)))).map (depthMarkedDecode p D) := by
  change Measure.map (fun a : IndexedCascadeBase k × (ℕ → IndexedLeaf k) =>
      cavityLabelMarkedArray p D a.2)
    (annealedInfiniteReplicaMeasure (indexedLeafKernel k)
      (indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)) (fun _ _ => 0) _) = _
  rw [annealedInfiniteReplicaMeasure_zero]
  change _ = ((indexedInfiniteLeafMeasure k z).map (fun a => indexedDepthArray k a.2)).map _
  have hm : Measurable (fun a : IndexedCascadeBase k × (ℕ → IndexedLeaf k) =>
    indexedDepthArray k a.2) := (indexedDepthArray_measurable k).comp measurable_snd
  rw [Measure.map_map (depthMarkedDecode_measurable p D) hm]
  apply congrArg (fun F => (indexedInfiniteLeafMeasure k z).map F)
  funext a i j
  simp only [Function.comp_def,cavityLabelMarkedArray,depthMarkedDecode,indexedDepthArray,
    indexedCommonDepth_comm k (a.2 i) (a.2 j)]

end SphericalPerceptronFreeEnergy
end

end OAI
