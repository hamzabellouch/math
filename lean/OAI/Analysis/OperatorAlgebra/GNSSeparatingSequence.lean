import OAI.Analysis.OperatorAlgebra.GNSSequenceAmplification
import Mathlib.Analysis.SpecificLimits.Basic
import OAI.Analysis.ModularTheory.CommutantExpectation

namespace OAI

/-! A concrete square-summable separating vector for the countable diagonal
amplification. Its zeroth coordinate is the prescribed vector. -/
noncomputable section
open scoped Topology
namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def separatingSequenceWeight (d : ℕ → H) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ n / (1 + ‖d n‖)

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma separatingSequenceWeight_pos (d : ℕ → H) (n : ℕ) :
    0 < separatingSequenceWeight d n := by
  unfold separatingSequenceWeight
  positivity

def separatingSequenceTerm (d : ℕ → H) (n : ℕ) : SequenceHilbert H :=
  lp.single 2 (n + 1) ((separatingSequenceWeight d n : ℂ) • d n)

omit [CompleteSpace H] in
lemma separatingSequenceTerm_norm_le (d : ℕ → H) (n : ℕ) :
    ‖separatingSequenceTerm d n‖ ≤ (1 / 2 : ℝ) ^ n := by
  rw [separatingSequenceTerm, lp.norm_single (by norm_num), norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (separatingSequenceWeight_pos d n)]
  calc
    separatingSequenceWeight d n * ‖d n‖ ≤
        separatingSequenceWeight d n * (1 + ‖d n‖) := by
      exact mul_le_mul_of_nonneg_left (by linarith)
        (separatingSequenceWeight_pos d n).le
    _ = _ := div_mul_cancel₀ _ (by positivity)

omit [CompleteSpace H] in
lemma separatingSequenceTerm_norm_summable (d : ℕ → H) :
    Summable (fun n => ‖separatingSequenceTerm d n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (separatingSequenceTerm_norm_le d) summable_geometric_two

omit [CompleteSpace H] in
lemma sequenceEval_apply (n : ℕ) (x : SequenceHilbert H) :
    lp.evalCLM ℂ (fun _ : ℕ => H) 2 n x = x n := rfl

lemma separatingSequenceTerm_summable (d : ℕ → H) :
    Summable (separatingSequenceTerm d) :=
  Summable.of_norm_bounded summable_geometric_two (separatingSequenceTerm_norm_le d)

def separatingSequence (ξ : H) (d : ℕ → H) : SequenceHilbert H :=
  lp.single 2 0 ξ + ∑' n, separatingSequenceTerm d n

lemma separatingSequence_zero (ξ : H) (d : ℕ → H) :
    separatingSequence ξ d 0 = ξ := by
  have he := (lp.evalCLM ℂ (fun _ : ℕ => H) 2 0).map_tsum
    (separatingSequenceTerm_summable d)
  change ξ + (lp.evalCLM ℂ (fun _ : ℕ => H) 2 0) (∑' n, separatingSequenceTerm d n) = ξ
  rw [he]
  simp [separatingSequenceTerm, sequenceEval_apply, lp.single_apply]

lemma separatingSequence_succ (ξ : H) (d : ℕ → H) (n : ℕ) :
    separatingSequence ξ d (n + 1) = (separatingSequenceWeight d n : ℂ) • d n := by
  have he := (lp.evalCLM ℂ (fun _ : ℕ => H) 2 (n + 1)).map_tsum
    (separatingSequenceTerm_summable d)
  change 0 + (lp.evalCLM ℂ (fun _ : ℕ => H) 2 (n + 1))
    (∑' k, separatingSequenceTerm d k) = _
  rw [zero_add, he]
  rw [tsum_eq_single n]
  · simp [separatingSequenceTerm, sequenceEval_apply, lp.single_apply]
  · intro k hk
    simp [separatingSequenceTerm, sequenceEval_apply, lp.single_apply, Ne.symm hk]

omit [CompleteSpace H] in
lemma separatingSequence_norm_le (ξ : H) (d : ℕ → H) :
    ‖separatingSequence ξ d‖ ≤ ‖ξ‖ + 2 := by
  calc
    _ ≤ ‖lp.single 2 0 ξ‖ + ‖∑' n, separatingSequenceTerm d n‖ := norm_add_le _ _
    _ ≤ ‖ξ‖ + ∑' n, ‖separatingSequenceTerm d n‖ := by
      rw [lp.norm_single (by norm_num)]
      exact add_le_add le_rfl (norm_tsum_le_tsum_norm
        (separatingSequenceTerm_norm_summable d))
    _ ≤ ‖ξ‖ + ∑' n, (1 / 2 : ℝ) ^ n := by
      exact add_le_add le_rfl (Summable.tsum_le_tsum
        (separatingSequenceTerm_norm_le d)
        (separatingSequenceTerm_norm_summable d) summable_geometric_two)
    _ = _ := by rw [tsum_geometric_two]

lemma separatingSequence_separates (ξ : H) (d : ℕ → H) (hd : DenseRange d)
    (T : SequenceHilbert H →L[ℂ] SequenceHilbert H)
    (hT : ∀ i j, Commute (sequenceMatrixUnit (H := H) i j) T)
    (hzero : T (separatingSequence ξ d) = 0) : T = 0 := by
  have hdiag := sequence_diagonal_of_matrixUnit_commutation T hT
  have hentry : sequenceEntryZero T = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    refine hd.induction_on x (isClosed_eq (sequenceEntryZero T).continuous continuous_const) ?_
    intro n
    have hv := congrArg (fun v : SequenceHilbert H => v (n + 1)) hzero
    rw [hdiag, sequenceDiagonal_apply, separatingSequence_succ, map_smul] at hv
    have hc : (separatingSequenceWeight d n : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (separatingSequenceWeight_pos d n)
    exact (smul_eq_zero.mp hv).resolve_left hc
  rw [hdiag, hentry]
  exact map_zero (sequenceDiagonalHom (H := H))

open KirchbergRordam.GenericRW.GroupedFactors

lemma sequence_bicommutant_separating {A : Type*} [CStarAlgebra A]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (d : ℕ → H) (hd : DenseRange d)
    (T : SequenceHilbert H →L[ℂ] SequenceHilbert H)
    (hT : T ∈ bicommutant (sequenceAmplification π).range)
    (hz : T (separatingSequence ξ d) = 0) : T = 0 := by
  apply separatingSequence_separates ξ d hd T _ hz
  intro i j
  apply (commute_iff_eq _ _).mpr
  apply VonNeumannAlgebra.mem_commutant_iff.mp hT
  apply (mem_commutantOf_iff _ _).mpr
  rintro _ ⟨a, rfl⟩
  exact sequenceDiagonal_matrixUnit_commute (π a) i j

end WeakPureInfiniteness

end

end OAI
