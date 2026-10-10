import OAI.Probability.SATComputability.PoissonSemigroup
import OAI.Probability.SATComputability.MarkovOccupation

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal

theorem candidateResidual_subset {n k d : ℕ} (U : Finset (DeletionCandidate n))
    (cs : Fin d → Fin k → SignedLiteral n) : candidateResidual U cs ⊆ U := by
  classical
  exact Finset.filter_subset _ _

theorem candidateResidual_mono {n k d : ℕ} {U V : Finset (DeletionCandidate n)}
    (h : U ⊆ V) (cs : Fin d → Fin k → SignedLiteral n) :
    candidateResidual U cs ⊆ candidateResidual V cs := by
  classical
  exact Finset.filter_subset_filter _ h

theorem candidateAlive_mono {n : ℕ} :
    Monotone (candidateAlive (n := n)) := by
  intro U V h
  unfold candidateAlive
  split_ifs with hU hV
  · rfl
  · exact (hV (hU.mono h)).elim
  · norm_num
  · rfl

theorem candidateBlock_expect_mono_state {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k : ℕ) {f : Finset (DeletionCandidate n) → ℝ}
    (hf : Monotone f) : Monotone (fun U => (candidateBlock r k U).expect f) := by
  intro U V hUV
  simp only [candidateBlock, poissonMixture_expect]
  apply integral_mono (poissonMixture_integrable_expect r
    (fun d => candidateFixedBlock k d U) f)
    (poissonMixture_integrable_expect r (fun d => candidateFixedBlock k d V) f)
  intro d
  simp only [candidateFixedBlock_expect, candidateStep_iterate]
  exact FiniteLaw.expect_mono _ (fun cs => hf (candidateResidual_mono hUV cs))

theorem candidateBlock_expect_le_of_subset {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k : ℕ) (U : Finset (DeletionCandidate n))
    (f g : Finset (DeletionCandidate n) → ℝ)
    (h : ∀ V ⊆ U, f V ≤ g V) :
    (candidateBlock r k U).expect f ≤ (candidateBlock r k U).expect g := by
  simp only [candidateBlock, poissonMixture_expect]
  apply integral_mono (poissonMixture_integrable_expect r _ f)
    (poissonMixture_integrable_expect r _ g)
  intro d
  simp only [candidateFixedBlock_expect, candidateStep_iterate]
  exact FiniteLaw.expect_mono _ (fun cs => h _ (candidateResidual_subset U cs))

theorem candidateBlock_expect_alive {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k : ℕ) (U : Finset (DeletionCandidate n)) :
    (candidateBlock r k U).expect candidateAlive = 1 - poissonKillProbability U k r := by
  have he : candidateAlive (n := n) = fun V => 1 - (if V = ∅ then 1 else 0) := by
    classical
    funext V
    by_cases h : V = ∅ <;> simp [candidateAlive, h, Finset.nonempty_iff_ne_empty]
  rw [he, FiniteLaw.expect_sub, FiniteLaw.expect_const, candidateBlock_kill]

theorem candidateBlock_empty {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k : ℕ) (f : Finset (DeletionCandidate n) → ℝ) :
    (candidateBlock r k ∅).expect f = f ∅ := by
  simp only [candidateBlock_expect, candidateStep_iterate, candidateResidual,
    Finset.filter_empty, FiniteLaw.expect_const, integral_const, probReal_univ, one_smul]

theorem candidateBlock_survival_le {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k : ℕ) (U : Finset (DeletionCandidate n)) :
    (candidateBlock r k U).expect candidateAlive ≤ candidateAlive U := by
  apply (candidateBlock_expect_le_of_subset r k U candidateAlive
    (fun _ => candidateAlive U) (fun _ h => candidateAlive_mono h)).trans_eq
  exact FiniteLaw.expect_const _ _

theorem candidateBlock_survival_submultiplicative {n : ℕ} [NeZero n]
    (r s : ℝ≥0) (k : ℕ) (U : Finset (DeletionCandidate n)) :
    (candidateBlock (r+s) k U).expect candidateAlive ≤
      (candidateBlock r k U).expect candidateAlive *
        (candidateBlock s k U).expect candidateAlive := by
  rw [candidateBlock_comp]
  calc
    _ ≤ (candidateBlock r k U).expect (fun V =>
        candidateAlive V * (candidateBlock s k U).expect candidateAlive) := by
      apply candidateBlock_expect_le_of_subset
      intro V hV
      by_cases h : V.Nonempty
      · simpa only [candidateAlive, ite_eq_left h, one_mul] using
          candidateBlock_expect_mono_state s k candidateAlive_mono hV
      · have he : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
        subst V
        simp [candidateBlock_empty, candidateAlive]
    _ = _ := FiniteLaw.expect_mul_right _ _ _

theorem candidateBlock_survival_geometric {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k : ℕ) (U : Finset (DeletionCandidate n))
    {δ : ℝ} (hδ : δ ≤ poissonKillProbability U k r) (m : ℕ) :
    (candidateBlock (r*m) k U).expect candidateAlive ≤ (1-δ)^m := by
  have hs := FiniteLaw.expect_nonneg (candidateBlock r k U) candidateAlive_nonneg
  have hb : (candidateBlock r k U).expect candidateAlive ≤ 1-δ := by
    rw [candidateBlock_expect_alive]
    linarith
  have hd : 0 ≤ 1-δ := hs.trans hb
  induction m with
  | zero => simp [candidateBlock_expect, integral_poissonMeasure, zero_pow_eq, ite_div, ite_mul,
      candidateAlive_le_one]
  | succ m ih =>
    have he : r * ((m+1 : ℕ) : ℝ≥0) = r*m+r := by push_cast; ring
    rw [he, pow_succ]
    exact (candidateBlock_survival_submultiplicative (r*m) r k U).trans
      (mul_le_mul ih hb hs (pow_nonneg hd m))

theorem candidateBlock_occupation {n : ℕ} [NeZero n]
    (r : ℝ≥0) (k L M : ℕ) (bin : Finset (DeletionCandidate n) → Prop)
    [DecidablePred bin] {δ : ℝ} (hδ : 0 < δ)
    (hbin : ∀ U, bin U → U.Nonempty ∧ δ ≤ poissonKillProbability U k (r*L))
    (U : Finset (DeletionCandidate n)) :
    (∑ t ∈ Finset.range M,
      (candidateBlock (r*t) k U).expect (fun V => if bin V then 1 else 0)) ≤
        (L : ℝ)/δ := by
  have hi (m : ℕ) (f : Finset (DeletionCandidate n) → ℝ) :
      (finiteKernelStep (candidateBlock r k))^[m] f U =
        (candidateBlock (r*m) k U).expect f := poissonCandidateStep_iterate r k m U f
  have h := finiteKernel_occupation (candidateBlock r k) candidateAlive
    (fun V => if bin V then 1 else 0) candidateAlive_nonneg candidateAlive_le_one hδ L
    (fun V => ?_) M U
  · simpa only [hi] using h
  · change δ * (if bin V then 1 else 0) ≤ candidateAlive V -
      (poissonCandidateStep r k)^[L] candidateAlive V
    rw [poissonCandidateStep_iterate]
    by_cases hb : bin V
    · obtain ⟨hne, hk⟩ := hbin V hb
      rw [ite_eq_left hb, mul_one, candidateAlive, ite_eq_left hne,
        candidateBlock_expect_alive]
      linarith
    · rw [ite_eq_right hb, mul_zero]
      exact sub_nonneg.mpr (candidateBlock_survival_le _ _ _)

end FixedClauseThreshold.Computability

end OAI
