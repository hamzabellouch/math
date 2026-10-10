import OAI.Analysis.FiniteFactor.Sampling.WeightedCoordinate
import OAI.Analysis.FiniteFactor.CrossedProduct.TailTrimming

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped ENNReal
noncomputable section

/-- The actual prefix-weighted summand loses at most the source tail budget
relative to its own mass. Coordinate independence is applied before the
countable union bound; a Haar estimate alone would not prove this statement. -/
theorem sourceSampling_weighted_tail_loss (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (n : ℕ) :
    sourceSamplingWeightedMeasure I s θ (n : ℤ) (sourceTailOrderFailure θ (s+1) n) ≤
      sourceSamplingWeightedMeasure I s θ (n : ℤ) Set.univ *
        ENNReal.ofReal (4*(n : ℝ)/((sourceStageState (s+1)).K : ℝ)) := by
  let ν := sourceSamplingWeightedMeasure I s θ (n : ℤ)
  let M := ν Set.univ
  have hcoord (i : SourceCoordinate) (hi : s < i.1) :
      ν {x | Int.fract (x i+(n : ℝ)*θ i) < x i} ≤ M*ENNReal.ofReal ((n : ℝ)*θ i) := by
    have hE : MeasurableSet {t : ℝ | Int.fract (t+(n : ℝ)*θ i) < t} :=
      measurableSet_lt (sourceFract_measurable.comp (measurable_id.add measurable_const)) measurable_id
    have he := sourceSampling_tail_coordinate_mass I s θ (n : ℤ) i hi _ hE
    change ν {x | Int.fract (x i+(n : ℝ)*θ i) < x i} =
      M*unitIntervalMeasure {t | Int.fract (t+(n : ℝ)*θ i) < t} at he
    rw [he]
    have hh := unitInterval_order_failure ((n : ℝ)*θ i) (mul_nonneg (Nat.cast_nonneg _) (hθ.nonneg _))
    gcongr
  have hblock (r : ℕ) :
      ν (⋃ i : Fin (sourceBlockSize (s+1+r)),
        {x | Int.fract (x ⟨s+1+r,i⟩+(n : ℝ)*θ ⟨s+1+r,i⟩) < x ⟨s+1+r,i⟩}) ≤
      M*ENNReal.ofReal ((n : ℝ)*(∑ i : Fin (sourceBlockSize (s+1+r)), θ ⟨s+1+r,i⟩)) := by
    apply (measure_iUnion_le _).trans
    calc
      _ ≤ ∑' i : Fin (sourceBlockSize (s+1+r)), M*ENNReal.ofReal ((n : ℝ)*θ ⟨s+1+r,i⟩) :=
        ENNReal.tsum_le_tsum (fun i => hcoord ⟨s+1+r,i⟩ (by simp; omega))
      _ = _ := by
        rw [tsum_fintype, ← Finset.mul_sum,
          ← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hθ.nonneg _)),
          ← Finset.mul_sum]
  calc
    _ ≤ ∑' r : ℕ, ν (⋃ i : Fin (sourceBlockSize (s+1+r)),
        {x | Int.fract (x ⟨s+1+r,i⟩+(n : ℝ)*θ ⟨s+1+r,i⟩) < x ⟨s+1+r,i⟩}) := measure_iUnion_le _
    _ ≤ ∑' r : ℕ, M*ENNReal.ofReal ((n : ℝ)*(∑ i : Fin (sourceBlockSize (s+1+r)), θ ⟨s+1+r,i⟩)) :=
      ENNReal.tsum_le_tsum hblock
    _ = M*ENNReal.ofReal ((n : ℝ)*sourceTailAngleSum θ (s+1)) := by
      rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg
        (fun r => mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun i _ => hθ.nonneg _)))
        ((hθ.tail_block_summable (s+1)).mul_left (n : ℝ)),tsum_mul_left]
      rfl
    _ ≤ _ := by
      gcongr 1
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_left (hθ.tail_sum_bound (s+1)) (Nat.cast_nonneg n)
      simpa [mul_div_assoc,mul_comm,mul_left_comm] using hh

/-- The source exponent gap now bounds actual weighted lost mass, uniformly
for every positive power at most Q. -/
theorem sourceSampling_weighted_tail_small (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) (n : ℕ)
    (hn : (n : ℝ) ≤ samplingQ (sourceBlockSize s)) :
    sourceSamplingWeightedMeasure I s θ (n : ℤ) (sourceTailOrderFailure θ (s+1) n) ≤
      sourceSamplingWeightedMeasure I s θ (n : ℤ) Set.univ *
        ENNReal.ofReal (4*(sourceBlockSize s : ℝ)^(-(sourceBlockSize s : ℝ)/20)) := by
  apply (sourceSampling_weighted_tail_loss I s θ hθ n).trans
  gcongr 1
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ 4*samplingQ (sourceBlockSize s)/((sourceStageState (s+1)).K : ℝ) := by gcongr
    _ ≤ _ := sourceSampling_tail_ratio s

end
end FiniteFactor

end OAI
