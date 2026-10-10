import OAI.Combinatorics.LowSpaceSubsetSum.Streams.ModularFilters
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Prod

namespace OAI

/-!
# Exact counts under uniform low-residue choices

Raw occurrence identities and distinct entry keys may be different types.
Neither is deduplicated here: each supplied finite set is partitioned by its
residue labels. This is the exact uniform-residue calculation for the counts
`G`, `J`, and `U` in the resource proof.
-/

namespace LowSpaceSubsetSum

open scoped BigOperators

variable {α : Type*}

def normalizedResidue {p : ℕ} (hp : 0 < p) (x : ℤ) : Fin p :=
  ⟨(x % (p : ℤ)).toNat, by
    have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
    exact (Int.toNat_lt (Int.emod_nonneg _ hpZ.ne')).mpr
      (Int.emod_lt_of_pos _ hpZ)⟩

theorem normalizedResidue_eq_iff {p : ℕ} (hp : 0 < p) (x : ℤ) (r : Fin p) :
    normalizedResidue hp x = r ↔ x % (p : ℤ) = r := by
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
  have hnonneg := Int.emod_nonneg x hpZ.ne'
  constructor
  · intro h
    have hval := congrArg (fun r : Fin p => (r.val : ℤ)) h
    simpa only [normalizedResidue, Int.toNat_of_nonneg hnonneg] using hval
  · intro h
    apply Fin.ext
    simp only [normalizedResidue]
    rw [h]
    rfl

theorem sum_label_fibers {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (T : Finset α) (label : α → Ω) :
    ∑ r : Ω, (T.filter fun x => label x = r).card = T.card := by
  exact (Finset.card_eq_sum_card_fiberwise
    (s := T) (t := Finset.univ) (f := label) (by simp)).symm

theorem mean_label_fiber {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (T : Finset α) (label : α → Ω) :
    (∑ r : Ω, ((T.filter fun x => label x = r).card : ℝ)) / Fintype.card Ω =
      (T.card : ℝ) / Fintype.card Ω := by
  congr 1
  exact_mod_cast sum_label_fibers T label

def residueFiltered {p : ℕ} (hp : 0 < p) (T : Finset α) (w : α → ℤ)
    (r : Fin p) : Finset α := T.filter fun x => normalizedResidue hp (w x) = r

theorem mean_residueFiltered {p : ℕ} (hp : 0 < p) (T : Finset α) (w : α → ℤ) :
    (∑ r : Fin p, ((residueFiltered hp T w r).card : ℝ)) / p = (T.card : ℝ) / p := by
  simpa only [residueFiltered, Fintype.card_fin] using
    mean_label_fiber T (fun x => normalizedResidue hp (w x))

def twiceResidueFiltered {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (T : Finset α) (parent child : α → ℤ) (r : Fin p × Fin q) : Finset α :=
  T.filter fun x => normalizedResidue hp (parent x) = r.1 ∧
    normalizedResidue hq (child x) = r.2

/-- Each raw four-leaf occurrence passes one and only one parent/first-child
residue pair. The second child's required residue follows by nesting. -/
theorem mean_twiceResidueFiltered {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (T : Finset α) (parent child : α → ℤ) :
    (∑ r : Fin p × Fin q, ((twiceResidueFiltered hp hq T parent child r).card : ℝ)) /
      (p * q : ℕ) = (T.card : ℝ) / (p * q : ℕ) := by
  simpa only [twiceResidueFiltered, Prod.ext_iff, Fintype.card_prod,
    Fintype.card_fin] using mean_label_fiber T
      (fun x => (normalizedResidue hp (parent x), normalizedResidue hq (child x)))

/-- Finite Markov bound for a counted resource. No independence between
different resources is required when these marginal bounds are combined. -/
theorem finite_count_markov {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (count : Ω → ℕ) {T : ℝ} (hT : 0 < T) :
    (((Finset.univ.filter fun r => T < (count r : ℝ)).card : ℝ) / Fintype.card Ω) ≤
      ((∑ r : Ω, (count r : ℝ)) / Fintype.card Ω) / T := by
  classical
  have hcard : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hind : ∀ r : Ω, (if T < (count r : ℝ) then T else 0) ≤ count r := by
    intro r
    split_ifs with h
    · exact h.le
    · exact Nat.cast_nonneg _
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset Ω))
    (fun r _ => hind r)
  rw [← Finset.sum_filter] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  apply (le_div_iff₀ hT).mpr
  rw [div_mul_eq_mul_div]
  exact (div_le_div_iff_of_pos_right hcard).mpr hsum

theorem residueFiltered_tail {p : ℕ} (hp : 0 < p) (X : Finset α) (w : α → ℤ)
    {T : ℝ} (hT : 0 < T) :
    (((Finset.univ.filter fun r : Fin p => T < (residueFiltered hp X w r).card).card : ℝ) /
      p) ≤ ((X.card : ℝ) / p) / T := by
  let : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  have h := finite_count_markov (fun r => (residueFiltered hp X w r).card) hT
  simpa only [Fintype.card_fin, mean_residueFiltered] using h

theorem twiceResidueFiltered_tail {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (X : Finset α) (parent child : α → ℤ) {T : ℝ} (hT : 0 < T) :
    (((Finset.univ.filter fun r : Fin p × Fin q =>
      T < (twiceResidueFiltered hp hq X parent child r).card).card : ℝ) /
        (p * q : ℕ)) ≤ ((X.card : ℝ) / (p * q : ℕ)) / T := by
  let : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have h := finite_count_markov
    (fun r => (twiceResidueFiltered hp hq X parent child r).card) hT
  simpa only [Fintype.card_prod, Fintype.card_fin, ← Nat.cast_mul,
    mean_twiceResidueFiltered] using h

end LowSpaceSubsetSum

end OAI
