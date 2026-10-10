import OAI.Combinatorics.ContingencyTables.Model
import OAI.Combinatorics.MatchingCount.Model

namespace OAI

/-!
# Main algorithm statements for result 200

The samplers and counter use a finite transition table, independent fair
bits, binary inputs and explicit bit-operation runtime bounds. No counting or sampling oracle is part of the machine.
The exact sampler's expected runtime uses a summable tail series, avoiding
the default value of an undefined infinite sum.
-/

namespace ContingencyTables.Algorithms

open scoped BigOperators
open Filter

abbrev Machine := MatchingFPRAS.RandomMachine
abbrev Symbol := MatchingFPRAS.Symbol

def encodeMatrix {m n : ℕ} (X : Fin m → Fin n → ℕ) : List Symbol :=
  ((List.ofFn fun i => (List.ofFn fun j => MatchingFPRAS.encodeNat (X i j)).flatten)).flatten

def encodeMargins {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) : List Symbol :=
  MatchingFPRAS.encodeNat m ++ MatchingFPRAS.encodeNat n ++
    (List.ofFn fun i => MatchingFPRAS.encodeNat (r i)).flatten ++
    (List.ofFn fun j => MatchingFPRAS.encodeNat (c j)).flatten

def encodeSamplingInput {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (k : ℕ) : List Symbol :=
  encodeMargins r c ++ MatchingFPRAS.encodeNat k

def encodeCountingInput {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (ε δ : ℚ) : List Symbol :=
  encodeMargins r c ++ encodeMatrix b ++ MatchingFPRAS.encodeRat ε ++ MatchingFPRAS.encodeRat δ

/-- The tape alphabet has positive cardinality. -/
theorem alphabetSize_neZero : NeZero (8 : ℕ) := inferInstance

/-- A halted tape contains the row-major binary matrix encoding. -/
def OutputsTable (A : Machine) (input : List Symbol) {t m n : ℕ}
    (bits : Fin t → Bool) (X : Fin m → Fin n → ℕ) : Prop :=
  (MatchingFPRAS.run A input bits).state = none ∧
    @Turing.Tape.right₀ MatchingFPRAS.Symbol (@Fin.instInhabited 8 alphabetSize_neZero)
      (MatchingFPRAS.run A input bits).tape =
    @Turing.ListBlank.mk Symbol (@Fin.instInhabited 8 alphabetSize_neZero) (encodeMatrix X)

noncomputable def tableMass (A : Machine) (input : List Symbol) (t : ℕ)
    {m n : ℕ} (X : Fin m → Fin n → ℕ) : ℝ := by
  classical
  exact ((Finset.univ.filter fun bits : Fin t → Bool => OutputsTable A input bits X).card : ℝ) /
    (2 : ℝ) ^ t

noncomputable def haltMass (A : Machine) (input : List Symbol) (t : ℕ) : ℝ := by
  classical
  exact ((Finset.univ.filter fun bits : Fin t → Bool =>
      (MatchingFPRAS.run A input bits).state = none).card : ℝ) / (2 : ℝ) ^ t

def samplingSize (n : ℕ) {m : ℕ} (r : Fin m → ℕ) (k : ℕ) : ℕ :=
  m + n + Nat.clog 2 ((∑ i, r i) + 1) + k + 1

/-- Paper 200-01, Theorem main(i): bounded runtime on every random tape
and total variation at most `2⁻ᵏ`, with freely varying dimensions. -/
def BoundedSamplingStatement : Prop :=
  ∃ (A : Machine) (C d : ℕ), 0 < C ∧
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i, r i) = ∑ j, c j → ∀ k : ℕ, 1 ≤ k →
        let input := encodeSamplingInput r c k
        let t := C * (samplingSize n r k) ^ d
        (∀ bits : Fin t → Bool, ∃ X : Table r c, OutputsTable A input bits X.val) ∧
        (∑ X : Table r c,
          |tableMass A input t X.val - (Fintype.card (Table r c) : ℝ)⁻¹|) / 2 ≤
            ((2 : ℝ) ^ k)⁻¹

/-- Paper 200-01, Theorem main(ii): every halted output is feasible, each
table has limiting mass `1/|Ω|`, termination has probability one, and the
expected number of bit operations is bounded by a uniform polynomial. -/
def ExactSamplingStatement : Prop :=
  ∃ (A : Machine) (C d : ℕ), 0 < C ∧
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i, r i) = ∑ j, c j →
        let input := encodeMargins r c
        let tail : ℕ → ℝ := fun t => 1 - haltMass A input t
        (∀ t (bits : Fin t → Bool), (MatchingFPRAS.run A input bits).state = none →
          ∃ X : Table r c, OutputsTable A input bits X.val) ∧
        (∀ X : Table r c, Tendsto (fun t => tableMass A input t X.val) atTop
          (nhds ((Fintype.card (Table r c) : ℝ)⁻¹))) ∧
        Tendsto (haltMass A input) atTop (nhds 1) ∧
        Summable tail ∧
        tsum tail ≤ C * (samplingSize n r 0) ^ d

noncomputable def count {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) : ℕ := Fintype.card (BoundedTable r c b)

def countingTime (C d : ℕ) {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (b : Fin m → Fin n → ℕ) (ε δ : ℚ) : ℕ :=
  C * ((encodeCountingInput r c b ε δ).length + ⌈ε⁻¹⌉₊ +
    Nat.clog 2 ⌈δ⁻¹⌉₊ + 1) ^ d

noncomputable def goodCountingTapes (A : Machine) {m n : ℕ}
    (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ)
    (ε δ : ℚ) (t : ℕ) : Finset (Fin t → Bool) := by
  classical
  exact Finset.univ.filter fun bits => ∃ q : ℚ,
    MatchingFPRAS.Outputs A (encodeCountingInput r c b ε δ) bits q ∧
      (1 - ε) * count r c b ≤ q ∧ q ≤ (1 + ε) * count r c b

/-- Paper 200-02, Theorem main. The input length includes the rational
accuracy parameters, and infeasible inputs always produce exactly zero. -/
def CountingStatement : Prop :=
  ∃ (A : Machine) (C d : ℕ), 0 < C ∧
    ∀ (m n : ℕ), 0 < m → 0 < n →
    ∀ (r : Fin m → ℕ) (c : Fin n → ℕ) (b : Fin m → Fin n → ℕ),
      (∑ i, r i) = ∑ j, c j →
      ∀ ε δ : ℚ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        let input := encodeCountingInput r c b ε δ
        let t := countingTime C d r c b ε δ
        (∀ bits : Fin t → Bool, ∃ q : ℚ, 0 ≤ q ∧ MatchingFPRAS.Outputs A input bits q) ∧
        (count r c b = 0 → ∀ bits : Fin t → Bool, MatchingFPRAS.Outputs A input bits 0) ∧
        ((goodCountingTapes A r c b ε δ t).card : ℚ) / (2 : ℚ) ^ t ≥ 1 - δ

end ContingencyTables.Algorithms

end OAI
