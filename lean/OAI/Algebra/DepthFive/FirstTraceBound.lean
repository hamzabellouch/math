import OAI.Algebra.DepthFive.FirstOccupationMoment
import OAI.Algebra.DepthFive.TraceComplexification

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335.FirstMoment

abbrev CompositionIndex (V : Type*) [Fintype V] [DecidableEq V] (a : ℕ) :=
  ↥(Finset.finsuppAntidiag (Finset.univ : Finset V) a)

abbrev Source (V U : Type*) [Fintype V] [DecidableEq V]
    [Fintype U] [DecidableEq U] (a b : ℕ) :=
  CompositionIndex V a × CompositionIndex U b

variable {V U P : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype U] [DecidableEq U] [Nonempty U] [Fintype P]

/-- The squared normalized coefficient of one squarefree path. -/
def mass {a b : ℕ} (s : P → Finset V) (z : P → Finset U)
    (i : Source V U a b) (p : P) : ℝ :=
  (∏ v ∈ s p, (i.1.val v : ℝ)) * (∏ u ∈ z p, ((i.2.val u : ℝ) + 1))

omit [Nonempty V] [Nonempty U] [Fintype P] in
lemma mass_nonneg {a b : ℕ} (s : P → Finset V) (z : P → Finset U)
    (i : Source V U a b) (p : P) : 0 ≤ mass s z i p := by
  unfold mass
  positivity

lemma card_source (a b : ℕ) :
    Fintype.card (Source V U a b) =
      (a + Fintype.card V - 1).choose a * (b + Fintype.card U - 1).choose b := by
  simp [Source, CompositionIndex, occupation_composition_card]

lemma composition_card_pos (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W]
    (t : ℕ) : 0 < (Finset.finsuppAntidiag (Finset.univ : Finset W) t).card := by
  rw [occupation_composition_card]
  apply Nat.choose_pos
  have : 0 < Fintype.card W := Fintype.card_pos
  omega

omit [Nonempty V] [Nonempty U] in
lemma sum_mass {a b : ℕ} (s : P → Finset V) (z : P → Finset U) :
    (∑ i : Source V U a b, ∑ p, mass s z i p) =
      ∑ p, ∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset V) a,
        ∑ N ∈ Finset.finsuppAntidiag (Finset.univ : Finset U) b,
          (∏ v ∈ s p, (M v : ℝ)) * (∏ u ∈ z p, ((N u : ℝ) + 1)) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Source, Fintype.sum_prod_type, mass]
  change (∑ M : CompositionIndex V a, ∑ N : CompositionIndex U b,
    (∏ v ∈ s p, (M.val v : ℝ)) * (∏ u ∈ z p, ((N.val u : ℝ) + 1))) = _
  calc
    _ = ∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset V) a,
        ∑ N : CompositionIndex U b,
          (∏ v ∈ s p, (M v : ℝ)) * (∏ u ∈ z p, ((N.val u : ℝ) + 1)) := by
      exact Finset.sum_coe_sort _ (fun M : V →₀ ℕ =>
        ∑ N : CompositionIndex U b,
          (∏ v ∈ s p, (M v : ℝ)) * (∏ u ∈ z p, ((N.val u : ℝ) + 1)))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro M hM
      exact Finset.sum_coe_sort _ (fun N : U →₀ ℕ =>
        (∏ v ∈ s p, (M v : ℝ)) * (∏ u ∈ z p, ((N u : ℝ) + 1)))

/-- Exact first-moment loss, deliberately kept separate from asymptotic
parameter estimates. -/
def loss (a v b u k m : ℕ) : ℝ :=
  (k : ℝ) ^ 2 / a + (k : ℝ) ^ 2 / (2 * v) +
    (m : ℝ) ^ 2 / b + (m : ℝ) ^ 2 / (2 * u)

def mean (a v b u k m : ℕ) : ℝ :=
  ((a : ℝ) / v) ^ k * (1 + (b : ℝ) / u) ^ m

/-- Sum the concrete occupation lower bound over every path and every source
basis vector.  The number of paths is counted exactly, not estimated. -/
theorem sum_mass_lower {a b k m : ℕ} (s : P → Finset V) (z : P → Finset U)
    (hs : ∀ p, (s p).card = k) (hz : ∀ p, (z p).card = m)
    (ha : 0 < a) (hb : 0 < b) (hka : 2 * k ≤ a) (hmb : 2 * m ≤ b) :
    (Fintype.card (Source V U a b) : ℝ) * Fintype.card P *
      mean a (Fintype.card V) b (Fintype.card U) k m *
        Real.exp (-loss a (Fintype.card V) b (Fintype.card U) k m) ≤
      ∑ i : Source V U a b, ∑ p, mass s z i p := by
  have hD : 0 < ((Finset.finsuppAntidiag (Finset.univ : Finset V) a).card *
      (Finset.finsuppAntidiag (Finset.univ : Finset U) b).card : ℝ) := by
    exact_mod_cast Nat.mul_pos (composition_card_pos V a) (composition_card_pos U b)
  have hper (p : P) := occupation_first_moment_lower a b (s p) (z p) ha hb
    (by simpa [hs p] using hka) (by simpa [hz p] using hmb)
  have hbound (p : P) :
      Real.exp (-loss a (Fintype.card V) b (Fintype.card U) k m) *
        mean a (Fintype.card V) b (Fintype.card U) k m *
          ((Finset.finsuppAntidiag (Finset.univ : Finset V) a).card *
            (Finset.finsuppAntidiag (Finset.univ : Finset U) b).card : ℝ) ≤
      ∑ M ∈ Finset.finsuppAntidiag (Finset.univ : Finset V) a,
        ∑ N ∈ Finset.finsuppAntidiag (Finset.univ : Finset U) b,
          (∏ v ∈ s p, (M v : ℝ)) * (∏ u ∈ z p, ((N u : ℝ) + 1)) := by
    apply (le_div_iff₀ hD).mp
    simpa only [hs p, hz p, loss, mean, neg_add_rev, neg_div,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hper p
  have hsum := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset P)) => hbound p)
  rw [sum_mass]
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Source, Fintype.card_prod, CompositionIndex, Fintype.card_coe,
    Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hsum

/-- First Gram-trace lower bound for a real square-root occupation path matrix.
The disjointness premise permits arbitrary targets for zero-mass invalid paths. -/
theorem real_first_trace_lower {J : Type*} [Fintype J] [DecidableEq J]
    {a b k m : ℕ} (s : P → Finset V) (z : P → Finset U)
    (hs : ∀ p, (s p).card = k) (hz : ∀ p, (z p).card = m)
    (ha : 0 < a) (hb : 0 < b) (hka : 2 * k ≤ a) (hmb : 2 * m ≤ b)
    (shift : Source V U a b → P → J)
    (hdisjoint : ∀ i p q, p ≠ q → shift i p = shift i q →
      mass s z i p = 0 ∨ mass s z i q = 0) :
    let A := pathShiftMatrix shift (fun i p => Real.sqrt (mass s z i p))
    (Fintype.card (Source V U a b) : ℝ) * Fintype.card P *
      mean a (Fintype.card V) b (Fintype.card U) k m *
        Real.exp (-loss a (Fintype.card V) b (Fintype.card U) k m) ≤
      (A.transpose * A).trace := by
  dsimp only
  rw [pathShiftMatrix_first_trace_sqrt shift (mass s z) (mass_nonneg s z) hdisjoint]
  exact sum_mass_lower s z hs hz ha hb hka hmb

/-- The same first-moment estimate for the genuine complex adjoint. -/
theorem complex_first_trace_lower {J : Type*} [Fintype J] [DecidableEq J]
    {a b k m : ℕ} (s : P → Finset V) (z : P → Finset U)
    (hs : ∀ p, (s p).card = k) (hz : ∀ p, (z p).card = m)
    (ha : 0 < a) (hb : 0 < b) (hka : 2 * k ≤ a) (hmb : 2 * m ≤ b)
    (shift : Source V U a b → P → J)
    (hdisjoint : ∀ i p q, p ≠ q → shift i p = shift i q →
      mass s z i p = 0 ∨ mass s z i q = 0) :
    let A := pathShiftMatrix shift (fun i p => (Real.sqrt (mass s z i p) : ℂ))
    (Fintype.card (Source V U a b) : ℝ) * Fintype.card P *
      mean a (Fintype.card V) b (Fintype.card U) k m *
        Real.exp (-loss a (Fintype.card V) b (Fintype.card U) k m) ≤
      (A.conjTranspose * A).trace.re := by
  dsimp only
  rw [complex_path_first_trace_sqrt shift (mass s z) (mass_nonneg s z) hdisjoint]
  exact sum_mass_lower s z hs hz ha hb hka hmb

end Problem335.FirstMoment

end

end OAI
