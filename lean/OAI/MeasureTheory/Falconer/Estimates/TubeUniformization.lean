import OAI.MeasureTheory.Falconer.Incidence.FiniteBallBounds
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.Log

namespace OAI

/-! Equalizing the sizes of tube pencils with only the dyadic logarithmic
loss used in Orponen--Shmerkin, Section 9. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem exists_dyadic_tube_bucket (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hP : P.Nonempty) {M : ℕ} (hT : ∀ x ∈ P, (T x).Nonempty)
    (hM : ∀ x ∈ P, (T x).card ≤ M) :
    ∃ k : ℕ, ∃ Q : Finset (Space 2), Q.Nonempty ∧ Q ⊆ P ∧
      (P.card : ℝ) ≤ (Nat.log 2 M+1 : ℕ)*(Q.card : ℝ) ∧
      ∀ x ∈ Q, 2^k ≤ (T x).card ∧ (T x).card < 2^(k+1) := by
  let L := Nat.log 2 M+1
  let f : Space 2 → ℕ := fun x => Nat.log 2 (T x).card
  have hL : (0 : ℝ) < L := by dsimp [L]; positivity
  have hmap : ∀ x ∈ P, f x ∈ Finset.range L := by
    intro x hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (hM x hx)))
  have hdiv : (Finset.range L).card • ((P.card : ℝ)/(L : ℝ)) ≤ (P.card : ℝ) := by
    simp only [Finset.card_range, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ (ne_of_gt hL)]
  obtain ⟨k,hk,hsize⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (M := ℝ) hmap (show (Finset.range L).Nonempty from ⟨0,Finset.mem_range.mpr (by dsimp [L]; omega)⟩) hdiv
  let Q := P.filter (fun x => f x = k)
  have hQ : Q.Nonempty := by
    apply Finset.card_pos.mp
    have hp : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
    have hq : (0 : ℝ) < Q.card := (div_pos hp hL).trans_le hsize
    exact_mod_cast hq
  refine ⟨k,Q,hQ,Finset.filter_subset _ _,?_,?_⟩
  · have h := (div_le_iff₀ hL).mp hsize
    simpa only [mul_comm] using h
  · intro x hx
    obtain ⟨hxP,hxk⟩ := Finset.mem_filter.mp hx
    have hn : (T x).card ≠ 0 := (hT x hxP).card_pos.ne'
    dsimp [f] at hxk
    constructor
    · rw [← hxk]
      exact Nat.pow_log_le_self 2 hn
    · rw [← hxk]
      exact Nat.lt_pow_succ_log_self (by norm_num) _

theorem exists_equal_size_tube_pencils (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty) {M : ℕ}
    (hT : ∀ x ∈ P, (T x).Nonempty) (hM : ∀ x ∈ P, (T x).card ≤ M) :
    ∃ k : ℕ, ∃ Q : Finset (Space 2), ∃ U : Space 2 → Finset (Space 2),
      Q.Nonempty ∧ Q ⊆ P ∧ (P.card : ℝ) ≤ (Nat.log 2 M+1 : ℕ)*(Q.card : ℝ) ∧
      ∀ x ∈ Q, U x ⊆ T x ∧ (U x).card = 2^k ∧ (T x).card ≤ 2*(U x).card := by
  obtain ⟨k,Q,hQ,hQP,hsize,hbucket⟩ := exists_dyadic_tube_bucket P T hP hT hM
  have hc (x : Space 2) (hx : x ∈ Q) : ∃ U ⊆ T x, U.card = 2^k :=
    Finset.exists_subset_card_eq (hbucket x hx).1
  let U : Space 2 → Finset (Space 2) := fun x => if hx : x ∈ Q then Classical.choose (hc x hx) else ∅
  refine ⟨k,Q,U,hQ,hQP,hsize,?_⟩
  intro x hx
  have hu := Classical.choose_spec (hc x hx)
  have he : U x = Classical.choose (hc x hx) := dite_eq_left hx
  rw [he]
  refine ⟨hu.1,hu.2,?_⟩
  rw [hu.2]
  have hb := (hbucket x hx).2
  rw [pow_succ] at hb
  omega

end Falconer

end OAI
