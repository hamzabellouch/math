import OAI.Combinatorics.MatrixRemoval.Model
import OAI.Combinatorics.MatrixRemoval.SamplingAvoidance

namespace OAI

/-!
# From sampled protected cells to arbitrary-repair distance

The guard sets comprise only cells that the path proof requires to stay
unchanged. The hypotheses do not require preservation of every
variable-variable entry or of an original copy of the pattern.
-/

universe uOmega uCell

noncomputable section

namespace Problem348.Sampling

/-- A sparse family of guards with a deterministic obstruction forces a lower
bound on every repair to an `H`-free matrix.  The pattern may be arbitrary. -/
theorem hammingDistance_ge_of_guard_sampling
    {k n : ℕ} {Ω : Type uOmega} [Fintype Ω]
    (H : BinaryMatrix k) (A B : BinaryMatrix n)
    (guard : Ω → Finset (Fin n × Fin n)) (m : ℕ)
    (hΩ : 0 < Fintype.card Ω)
    (hbound : ∀ e,
      (Finset.univ.filter (fun ω => e ∈ guard ω)).card * m ^ 2 ≤ Fintype.card Ω)
    (hforce : ∀ ω,
      (∀ e ∈ guard ω, A e.1 e.2 = B e.1 e.2) → ¬ HFree H B)
    (hfree : HFree H B) : m ^ 2 ≤ hammingDistance A B := by
  classical
  by_contra h
  have hsmall :
      (Finset.univ.filter (fun e : Fin n × Fin n => A e.1 e.2 ≠ B e.1 e.2)).card
        < m ^ 2 := by
    simpa only [hammingDistance] using Nat.lt_of_not_ge h
  obtain ⟨ω, hω⟩ := exists_agreement_of_changed_card_lt
    (fun e : Fin n × Fin n => A e.1 e.2)
    (fun e : Fin n × Fin n => B e.1 e.2)
    (fun ω e => e ∈ guard ω) (fun _ => True) m hΩ
    (fun e _ => hbound e) hsmall
  exact hforce ω (fun e he => hω e True.intro he) hfree

/-- The three-seed specialization: a guard uses each cell in at most `m`
of the `m³` samples.  Therefore no `H`-free repair changes fewer than `m²`
entries. -/
theorem hammingDistance_ge_of_three_seed_guards
    {k n : ℕ} (m : ℕ) (hm : 0 < m)
    (H : BinaryMatrix k) (A B : BinaryMatrix n)
    (guard : (Fin m × Fin m × Fin m) → Finset (Fin n × Fin n))
    (hbound : ∀ e, (Finset.univ.filter (fun ω => e ∈ guard ω)).card ≤ m)
    (hforce : ∀ ω,
      (∀ e ∈ guard ω, A e.1 e.2 = B e.1 e.2) → ¬ HFree H B)
    (hfree : HFree H B) : m ^ 2 ≤ hammingDistance A B := by
  apply hammingDistance_ge_of_guard_sampling H A B guard m
  · simpa using Nat.mul_pos hm (Nat.mul_pos hm hm)
  · intro e
    calc
      (Finset.univ.filter (fun ω => e ∈ guard ω)).card * m ^ 2
          ≤ m * m ^ 2 := Nat.mul_le_mul_right _ (hbound e)
      _ = Fintype.card (Fin m × Fin m × Fin m) := by simp [pow_two]
  · exact hforce
  · exact hfree

/-- A guard-frequency estimate can be obtained from a larger set of protected
selected cells.  This is useful when the deterministic path proof uses just a
subset of all selected anchor, dummy, and root incidences. -/
theorem guard_frequency_le {Ω : Type uOmega} {Cell : Type uCell} [Fintype Ω] [DecidableEq Cell]
    (guard : Ω → Finset Cell) (selected : Ω → Cell → Prop)
    [DecidableRel selected]
    (hsub : ∀ ω e, e ∈ guard ω → selected ω e) (e : Cell) :
    (Finset.univ.filter (fun ω => e ∈ guard ω)).card ≤
      (Finset.univ.filter (fun ω => selected ω e)).card := by
  classical
  apply Finset.card_le_card
  intro ω hω
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub ω e (Finset.mem_filter.mp hω).2⟩

end Problem348.Sampling

end

end OAI
