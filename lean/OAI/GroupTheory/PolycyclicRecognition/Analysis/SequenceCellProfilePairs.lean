import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceCellProfiles
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubsequences

namespace OAI

/-! # Joint good sheets for two supported profile limits

The two profile approximations are imposed on the same Haar-cell subset.
Their joint weak limit supplies its subexponential relative mass.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- A supported pair of profile limits gives a common good set in each
original recurrence cell, with both uniform errors tending to zero. -/
theorem exists_good_cell_profile_pairs_sequence
    {V W N : Type*} [TopologicalSpace V] [NormedAddCommGroup W] [MeasurableSpace N]
    (S : Set C(V, W)) [MeasurableSpace S] [BorelSpace S]
    [BorelSpace (S × S)] [HasOuterApproxClosed (S × S)]
    (K : Set V) (hK : IsCompact K)
    (scale : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (μ : Measure N) (Q : ℕ → Set N) (hQ : ∀ n, MeasurableSet (Q n))
    (hQ0 : ∀ n, μ (Q n) ≠ 0) (hQfin : ∀ n, μ (Q n) ≠ ∞)
    (profile : ℕ → N → S × S) (hp : ∀ n, Measurable (profile n))
    (ν : ProbabilityMeasure (S × S))
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (cellProbabilityMeasure μ (Q n) (hQ0 n) (hQfin n)) (profile n)) atTop (𝓝 ν))
    {f : S × S} (hf : f ∈ (ν : Measure (S × S)).support) :
    ∃ (A : ℕ → Set N) (ε : ℕ → ℝ),
      (∀ n, MeasurableSet (A n)) ∧ (∀ n, A n ⊆ Q n) ∧
      (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      HasSubexponentialLowerBoundSeq scale
        (fun n => (μ (A n)).toReal / (μ (Q n)).toReal) ∧
      (∀ᶠ n in atTop, 0 < (μ (A n)).toReal) ∧
      ∀ n x, x ∈ A n → ∀ z ∈ K,
        ‖(profile n x).1.val z - f.1.val z‖ < ε n ∧
        ‖(profile n x).2.val z - f.2.val z‖ < ε n := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let incl : C(K, V) := ⟨Subtype.val, continuous_subtype_val⟩
  let res : C(S, C(K, W)) := ⟨fun g => g.val.comp incl,
    (ContinuousMap.continuous_precomp incl).comp continuous_subtype_val⟩
  let observe : C(S × S, C(K, W) × C(K, W)) :=
    ⟨fun g => (res g.1, res g.2), (res.continuous.comp continuous_fst).prodMk
      (res.continuous.comp continuous_snd)⟩
  obtain ⟨B, ε, hB, hε, hεlim, hmass, hgood⟩ := exists_good_sampled_observations_sequence
    scale hs (fun n => cellProbabilityMeasure μ (Q n) (hQ0 n) (hQfin n))
    profile hp ν hν hf observe
  let A := fun n => B n ∩ Q n
  have hmass' : HasSubexponentialLowerBoundSeq scale
      (fun n => (μ (A n)).toReal / (μ (Q n)).toReal) := by
    simpa only [cellProbabilityMeasure_apply_toReal μ _ _ (hQ0 _) (hQfin _) (hB _)] using hmass
  refine ⟨A, ε, fun n => (hB n).inter (hQ n), fun _ => inter_subset_right,
    hε, hεlim, hmass', ?_, ?_⟩
  · filter_upwards [hmass'.eventually_pos] with n hn
    exact (div_pos_iff.mp hn).resolve_right
      (fun h => (ENNReal.toReal_nonneg).not_gt h.1) |>.1
  intro n x hx z hz
  have hc := hgood n x hx.1
  have hfst : ‖res (profile n x).1 - res f.1‖ ≤ ‖observe (profile n x) - observe f‖ :=
    norm_fst_le (observe (profile n x) - observe f)
  have hsnd : ‖res (profile n x).2 - res f.2‖ ≤ ‖observe (profile n x) - observe f‖ :=
    norm_snd_le (observe (profile n x) - observe f)
  exact ⟨((res (profile n x).1 - res f.1).norm_coe_le_norm ⟨z, hz⟩).trans_lt
    (hfst.trans_lt hc), ((res (profile n x).2 - res f.2).norm_coe_le_norm ⟨z, hz⟩).trans_lt
    (hsnd.trans_lt hc)⟩

/-- Retain only good scales once, before applying the coupled recurrence.
Both the actual scales and their indices remain strictly increasing. -/
theorem exists_positive_good_cell_profile_pairs
    {V W N : Type*} [TopologicalSpace V] [NormedAddCommGroup W] [MeasurableSpace N]
    (S : Set C(V, W)) [MeasurableSpace S] [BorelSpace S]
    [BorelSpace (S × S)] [HasOuterApproxClosed (S × S)]
    (K : Set V) (hK : IsCompact K)
    (scale : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (μ : Measure N) (Q : ℕ → Set N) (hQ : ∀ n, MeasurableSet (Q n))
    (hQ0 : ∀ n, μ (Q n) ≠ 0) (hQfin : ∀ n, μ (Q n) ≠ ∞)
    (profile : ℕ → N → S × S) (hp : ∀ n, Measurable (profile n))
    (ν : ProbabilityMeasure (S × S))
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (cellProbabilityMeasure μ (Q n) (hQ0 n) (hQfin n)) (profile n)) atTop (𝓝 ν))
    {f : S × S} (hf : f ∈ (ν : Measure (S × S)).support) :
    ∃ (u : ℕ → ℕ) (A : ℕ → Set N) (ε : ℕ → ℝ),
      StrictMono u ∧ StrictMono (scale ∘ u) ∧
      (∀ n, MeasurableSet (A n)) ∧ (∀ n, A n ⊆ Q (u n)) ∧
      (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ n, 0 < (μ (A n)).toReal) ∧
      HasSubexponentialLowerBoundSeq (scale ∘ u)
        (fun n => (μ (A n)).toReal / (μ (Q (u n))).toReal) ∧
      ∀ n x, x ∈ A n → ∀ z ∈ K,
        ‖(profile (u n) x).1.val z - f.1.val z‖ < ε n ∧
        ‖(profile (u n) x).2.val z - f.2.val z‖ < ε n := by
  obtain ⟨A, ε, hA, hAQ, hε, hεlim, hmass, hpos, hgood⟩ :=
    exists_good_cell_profile_pairs_sequence S K hK scale hs μ Q hQ hQ0 hQfin
      profile hp ν hν hf
  obtain ⟨u, hu, hsu, hupos⟩ := exists_increasing_good_scale_subsequence hs hpos
  refine ⟨u, A ∘ u, ε ∘ u, hu, hsu, fun n => hA (u n), fun n => hAQ (u n),
    fun n => hε (u n), hεlim.comp hu.tendsto_atTop, hupos,
    hmass.comp hu.tendsto_atTop, ?_⟩
  exact fun n => hgood (u n)

/-- Replace the finitely many zero-measure good cells by their whole cells.
The scale sequence is preserved, which keeps both already chosen polynomial
limits and the chart selected by the geometric comparison unchanged. -/
theorem exists_positive_eventually_good_cell_profile_pairs
    {V W N : Type*} [TopologicalSpace V] [NormedAddCommGroup W] [MeasurableSpace N]
    (S : Set C(V, W)) [MeasurableSpace S] [BorelSpace S]
    [BorelSpace (S × S)] [HasOuterApproxClosed (S × S)]
    (K : Set V) (hK : IsCompact K)
    (scale : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (μ : Measure N) (Q : ℕ → Set N) (hQ : ∀ n, MeasurableSet (Q n))
    (hQ0 : ∀ n, μ (Q n) ≠ 0) (hQfin : ∀ n, μ (Q n) ≠ ∞)
    (profile : ℕ → N → S × S) (hp : ∀ n, Measurable (profile n))
    (ν : ProbabilityMeasure (S × S))
    (hν : Tendsto (fun n => ProbabilityMeasure.map
      (cellProbabilityMeasure μ (Q n) (hQ0 n) (hQfin n)) (profile n)) atTop (𝓝 ν))
    {f : S × S} (hf : f ∈ (ν : Measure (S × S)).support) :
    ∃ (A : ℕ → Set N) (ε : ℕ → ℝ),
      (∀ n, MeasurableSet (A n)) ∧ (∀ n, A n ⊆ Q n) ∧
      (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ n, 0 < (μ (A n)).toReal) ∧
      HasSubexponentialLowerBoundSeq scale
        (fun n => (μ (A n)).toReal / (μ (Q n)).toReal) ∧
      ∀ᶠ n in atTop, ∀ x ∈ A n, ∀ z ∈ K,
        ‖(profile n x).1.val z - f.1.val z‖ < ε n ∧
        ‖(profile n x).2.val z - f.2.val z‖ < ε n := by
  classical
  obtain ⟨A, ε, hA, hAQ, hε0, hε, hmass, hpos, hgood⟩ :=
    exists_good_cell_profile_pairs_sequence S K hK scale hs μ Q hQ hQ0 hQfin
      profile hp ν hν hf
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hpos
  let A' := fun n => if n₀ ≤ n then A n else Q n
  refine ⟨A', ε, ?_, ?_, hε0, hε, ?_, ?_, ?_⟩
  · intro n
    dsimp only [A']
    split_ifs
    · exact hA n
    · exact hQ n
  · intro n
    dsimp only [A']
    split_ifs
    · exact hAQ n
    · exact subset_rfl
  · intro n
    dsimp only [A']
    split_ifs with hn
    · exact hn₀ n hn
    · exact ENNReal.toReal_pos (hQ0 n) (hQfin n)
  · intro δ hδ
    filter_upwards [hmass δ hδ, eventually_ge_atTop n₀] with n hn hlarge
    simpa only [A', ite_eq_left hlarge] using hn
  · filter_upwards [eventually_ge_atTop n₀] with n hn
    simpa only [A', ite_eq_left hn] using hgood n

end PolycyclicRecognition

end

end OAI
