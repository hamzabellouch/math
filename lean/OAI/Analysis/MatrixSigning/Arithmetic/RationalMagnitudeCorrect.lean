import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.BinaryRationalCanonical
import OAI.Analysis.MatrixSigning.Arithmetic.RationalMagnitudePositive

namespace OAI

section

namespace KS.W30.RationalMagnitudeMachine
open KS.W01.FixedStack KS.W29.FixedSequential KS.W19.FixedRun
open KS.W03.MachineCombinators KS.W19

lemma selector_zero (n : List Bool) (sgn coin : Bool) :
    program.toMachine.step ⟨some program.initial, state n [] sgn⟩ coin =
      KS.W29.FixedBranch.liftLeft zeroBranch positiveBranch
        ⟨some zeroBranch.initial, state n [] sgn⟩ := by
  unfold program
  erw [KS.W29.FixedBranch.step_start]
  apply config_ext
  · rfl
  · intro j
    fin_cases j <;> rfl

lemma selector_positive (n d : List Bool) (hd : d ≠ []) (sgn coin : Bool) :
    program.toMachine.step ⟨some program.initial, state n d sgn⟩ coin =
      KS.W29.FixedBranch.liftRight zeroBranch positiveBranch
        ⟨some positiveBranch.initial, state n d sgn⟩ := by
  cases d with
  | nil => exact (hd rfl).elim
  | cons b bs =>
    unfold program
    erw [KS.W29.FixedBranch.step_start]
    cases b <;> apply config_ext
    all_goals first | rfl | (intro j; fin_cases j <;> rfl)

theorem program_spec (n d : List Bool) (sgn : Bool) (L : ℕ)
    (hnc : CanonicalBits n) (hdc : CanonicalBits d)
    (hn : n.length ≤ L) (hd : d.length ≤ L) :
    let p := KS.W30.BinaryRational.normalizeMagnitude n d
    RunSpec program (state n d sgn)
      (state p.1 p.2 (if p.1 = [] then false else sgn)) (300 * (L + 1) ^ 3) := by
  dsimp only
  intro bits hlen
  cases bits with
  | nil => simp at hlen
  | cons coin tail =>
    simp only [List.length_cons] at hlen
    have hlin := Nat.le_self_pow (by decide : 3 ≠ 0) (L + 1)
    by_cases hd0 : d = []
    · subst d
      have ht : n.length + 4 ≤ tail.length := by omega
      rw [Machine.run, selector_zero]
      change (KS.W29.FixedBranch.branch zeroBranch positiveBranch 10 selector).toMachine.run
        (KS.W29.FixedBranch.liftLeft zeroBranch positiveBranch
          ⟨some zeroBranch.initial, state n [] sgn⟩) tail = _
      rw [KS.W29.FixedBranch.run_left]
      erw [(zeroBranch_spec n sgn).run_of_le tail ht]
      simp only [KS.W30.BinaryRational.normalizeMagnitude, trimBits, ↓reduceIte]
      rfl
    · have hdp := canonicalBits_value_pos d hdc hd0
      have ht : 250 * (L + 1) ^ 3 ≤ tail.length := by omega
      rw [Machine.run, selector_positive n d hd0 sgn coin]
      change (KS.W29.FixedBranch.branch zeroBranch positiveBranch 10 selector).toMachine.run
        (KS.W29.FixedBranch.liftRight zeroBranch positiveBranch
          ⟨some positiveBranch.initial, state n d sgn⟩) tail = _
      rw [KS.W29.FixedBranch.run_right]
      erw [(positiveBranch_spec n d sgn L hnc hdc hn hd hdp).run_of_le tail ht]
      rfl

theorem normalizes_ratBits (x : KS.W30.BinaryRational.RatBits) (L : ℕ)
    (hnc : CanonicalBits x.numerator) (hdc : CanonicalBits x.denominator)
    (hn : x.numerator.length ≤ L) (hd : x.denominator.length ≤ L) :
    RunSpec program (state x.numerator x.denominator x.negative)
      (state (KS.W30.BinaryRational.normalize x).numerator
        (KS.W30.BinaryRational.normalize x).denominator
        (KS.W30.BinaryRational.normalize x).negative) (300 * (L + 1) ^ 3) :=
  program_spec x.numerator x.denominator x.negative L hnc hdc hn hd

theorem normalizes_to_rational_encoding (x : KS.W30.BinaryRational.RatBits) (L : ℕ)
    (hnc : CanonicalBits x.numerator) (hdc : CanonicalBits x.denominator)
    (hn : x.numerator.length ≤ L) (hd : x.denominator.length ≤ L) :
    let q := x.value
    RunSpec program (state x.numerator x.denominator x.negative)
      (state (Computability.encodeNat q.num.natAbs) (Computability.encodeNat q.den)
        (decide (q.num < 0))) (300 * (L + 1) ^ 3) := by
  have h := normalizes_ratBits x L hnc hdc hn hd
  rw [KS.W30.BinaryRational.normalize_eq_encodeMagnitude] at h
  exact h

end KS.W30.RationalMagnitudeMachine

end

end OAI
