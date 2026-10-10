import OAI.Probability.InvariantIsing.Spectral.SpectralPartition
import OAI.Probability.InvariantIsing.Spectral.SpectralQuantileMoments

namespace OAI

/-! The actual spectral-group quantiles sum to the total spin quantile. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma spectralCoordinate_unit {m : ℕ} {Q : ProbabilityMeasure (SpectralArray m)}
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ a, 0 ≤ (x (0,1) a : ℝ)) (a : Fin m) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray m)),
      spectralLinearArray (Pi.single a 1) x 0 1 ∈ Icc (0 : ℝ) 1 := by
  filter_upwards [hn] with x hx
  rw [spectralLinearArray_single]
  exact ⟨hx a, (x (0,1) a).property.2⟩

def spectralPartitionQuantileWeights (m : ℕ) : Fin (m + 1) → Fin (m + 1) → ℝ :=
  Fin.lastCases (spectralSpinWeight m) (fun a => Pi.single a.castSucc 1)

def spectralPartitionRelation (m : ℕ) : Fin (m + 1) → ℝ :=
  Fin.lastCases (-1) (fun _ => 1)

lemma spectralPartitionQuantileWeights_nonneg (m : ℕ) (i a : Fin (m + 1)) :
    0 ≤ spectralPartitionQuantileWeights m i a := by
  classical
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [spectralPartitionQuantileWeights, Fin.lastCases_last] using
      spectralSpinWeight_nonneg m a
  · simp only [spectralPartitionQuantileWeights, Fin.lastCases_castSucc, Pi.single_apply]
    split_ifs <;> norm_num

lemma spectralPartitionRelation_eq_zero (m : ℕ) (a : Fin (m + 1)) :
    (∑ i, spectralPartitionRelation m i * spectralPartitionQuantileWeights m i a) = 0 := by
  classical
  rw [Fin.sum_univ_castSucc]
  simp only [spectralPartitionRelation, spectralPartitionQuantileWeights,
    Fin.lastCases_castSucc, Fin.lastCases_last, one_mul, neg_mul, one_mul]
  refine Fin.lastCases ?_ (fun j => ?_) a
  · simp [spectralSpinWeight]
  · simp [Pi.single_apply, spectralSpinWeight, Fin.castSucc_inj]

theorem spectralPartitionQuantileWeights_unit {m : ℕ}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))}
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (i : Fin (m + 1)) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      spectralLinearArray (spectralPartitionQuantileWeights m i) x 0 1 ∈ Icc (0 : ℝ) 1 := by
  refine Fin.lastCases ?_ (fun a => ?_) i
  · simpa only [spectralPartitionQuantileWeights, Fin.lastCases_last,
      spectralLinearArray_spinWeight] using spectralPartition_spin_unit hP hn
  · simpa only [spectralPartitionQuantileWeights, Fin.lastCases_castSucc] using
      spectralCoordinate_unit hn a.castSucc

/-- The spectral partition and vector Ghirlanda–Guerra synchronization
yield the sum identity. -/
theorem spectralPartition_quantile_sum {m : ℕ}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x)
    (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : Equiv.Perm ℕ,
      (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q)
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ)) :
    ∀ᵐ s ∂pathMeasure,
      (∑ a : Fin m, spectralQuantilePath Q (Pi.single a.castSucc 1) (spectralCoordinate_unit hn a.castSucc) s) =
        spectralQuantilePath Q (spectralSpinWeight m)
          (by simpa only [spectralLinearArray_spinWeight] using spectralPartition_spin_unit hP hn) s := by
  have hr := spectralQuantilePath_linear_relation hgg hG q hq hd hE
    (spectralPartitionQuantileWeights m) (spectralPartitionQuantileWeights_nonneg m)
    (spectralPartitionQuantileWeights_unit hP hn) (spectralPartitionRelation m)
    (spectralPartitionRelation_eq_zero m)
  filter_upwards [hr] with s hs
  rw [Fin.sum_univ_castSucc] at hs
  simp only [spectralPartitionRelation, spectralPartitionQuantileWeights,
    Fin.lastCases_castSucc, Fin.lastCases_last, one_mul, neg_mul, one_mul] at hs
  linarith

lemma group_increment_le_total {m : ℕ} (p : OverlapPath) (pa : Fin m → OverlapPath)
    {s t : ℝ} (hst : s ≤ t) (hs : (∑ a, pa a s) = p s) (ht : (∑ a, pa a t) = p t)
    (a : Fin m) : 0 ≤ pa a t - pa a s ∧ pa a t - pa a s ≤ p t - p s := by
  have hn (b : Fin m) : 0 ≤ pa b t - pa b s := sub_nonneg.mpr ((pa b).monotone hst)
  refine ⟨hn a, ?_⟩
  rw [← ht, ← hs, ← Finset.sum_sub_distrib]
  exact Finset.single_le_sum (fun b _ => hn b) (Finset.mem_univ a)

end InvariantIsing

end

end OAI
