import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceProfileSampling
import OAI.GroupTheory.PolycyclicRecognition.Analysis.OccupationSampling

namespace OAI

/-! # Good profiles in the original Haar cells

The good sets remain subsets of the original recurrence cells, and their
probability estimate is exactly a relative Haar-volume estimate.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology ENNReal

theorem cellProbabilityMeasure_apply_toReal
    {N : Type*} [MeasurableSpace N] (μ : Measure N)
    (Q B : Set N) (hQ0 : μ Q ≠ 0) (hQfin : μ Q ≠ ∞) (hB : MeasurableSet B) :
    ((cellProbabilityMeasure μ Q hQ0 hQfin : Measure N) B).toReal =
      (μ (B ∩ Q)).toReal / (μ Q).toReal := by
  change (((μ Q)⁻¹ • μ.restrict Q) B).toReal = _
  rw [Measure.smul_apply, Measure.restrict_apply hB]
  simp only [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_inv_mul]

/-- The supported profile law gives shrinking errors on a prescribed
compact set and good subsets of the actual recurrence cells with relative
mass at least `exp(-o(scale))`. -/
theorem exists_good_cell_profiles_sequence
    {V W N : Type*} [TopologicalSpace V] [NormedAddCommGroup W] [MeasurableSpace N]
    (S : Set C(V, W)) [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (K : Set V) (hK : IsCompact K)
    (scale : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (μ : Measure N) (Q : ℕ → Set N) (hQ : ∀ n, MeasurableSet (Q n))
    (hQ0 : ∀ n, μ (Q n) ≠ 0) (hQfin : ∀ n, μ (Q n) ≠ ∞)
    (profile : ℕ → N → S) (hp : ∀ n, Measurable (profile n))
    (ν : ProbabilityMeasure S)
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (cellProbabilityMeasure μ (Q n) (hQ0 n) (hQfin n)) (profile n)) atTop (𝓝 ν))
    {f : S} (hf : f ∈ (ν : Measure S).support) :
    ∃ (A : ℕ → Set N) (ε : ℕ → ℝ),
      (∀ n, MeasurableSet (A n)) ∧ (∀ n, A n ⊆ Q n) ∧
      (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      HasSubexponentialLowerBoundSeq scale
        (fun n => (μ (A n)).toReal / (μ (Q n)).toReal) ∧
      (∀ᶠ n in atTop, 0 < (μ (A n)).toReal) ∧
      ∀ n a, a ∈ A n → ∀ z ∈ K, ‖(profile n a).val z - f.val z‖ < ε n := by
  obtain ⟨B, ε, hB, hε, hεlim, hmass, hgood⟩ := exists_good_sampled_profiles_sequence
    S K hK scale hs (fun n => cellProbabilityMeasure μ (Q n) (hQ0 n) (hQfin n))
    profile hp ν hν hf
  let A := fun n => B n ∩ Q n
  have hmass' : HasSubexponentialLowerBoundSeq scale
      (fun n => (μ (A n)).toReal / (μ (Q n)).toReal) := by
    simpa only [cellProbabilityMeasure_apply_toReal μ _ _ (hQ0 _) (hQfin _) (hB _)] using hmass
  refine ⟨A, ε, fun n => (hB n).inter (hQ n), fun _ => inter_subset_right,
    hε, hεlim, hmass', ?_, ?_⟩
  · filter_upwards [hmass'.eventually_pos] with n hn
    exact (div_pos_iff.mp hn).resolve_right (fun h => (ENNReal.toReal_nonneg).not_gt h.1)
      |>.1
  · intro n a ha
    exact hgood n a ha.1

end PolycyclicRecognition

end

end OAI
