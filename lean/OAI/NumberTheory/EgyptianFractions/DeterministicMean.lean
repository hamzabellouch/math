import OAI.NumberTheory.EgyptianFractions.DeterministicReciprocal
import OAI.NumberTheory.EgyptianFractions.FourierSecondMoment

namespace OAI
noncomputable section
open scoped BigOperators
open Filter ComplexConjugate
namespace Problem337

/-- A version of the finite second moment normalized by an arbitrary upper
cutoff, valid also when the ambient integer interval is empty. -/
theorem finite_second_moment_cutoff {α β : Type*}
    (U : Finset α) (T : Finset β) (z : α → β → ℂ) (X E : ℝ)
    (hT : T.Nonempty) (hX : 0 ≤ X) (hE : 0 ≤ E) (hU : (U.card : ℝ) ≤ X)
    (hunit : ∀ u ∈ U, ∀ t ∈ T, ‖z u t‖ = 1)
    (hcorr : ∀ t ∈ T, ∀ s ∈ T, t ≠ s →
      ‖∑ u ∈ U, z u t * conj (z u s)‖ ≤ X * E) :
    (∑ u ∈ U, ‖(∑ t ∈ T, z u t) / (T.card : ℂ)‖ ^ 2) ≤
      X * (1 / (T.card : ℝ) + E) := by
  have ht : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hraw := finite_complex_second_moment_bound U T z (X * E) hunit hcorr
  have hweak : (∑ u ∈ U, ‖∑ t ∈ T, z u t‖ ^ 2) ≤
      X * T.card + (T.card : ℝ) ^ 2 * (X * E) := by
    apply hraw.trans
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right hU ht.le
    · apply mul_le_mul_of_nonneg_right _ (mul_nonneg hX hE)
      nlinarith
  simp only [norm_div, Complex.norm_natCast, div_pow]
  rw [← Finset.sum_div]
  apply (div_le_iff₀ (sq_pos_of_pos ht)).mpr
  have heq : X * (1 / (T.card : ℝ) + E) * (T.card : ℝ) ^ 2 =
      X * T.card + (T.card : ℝ) ^ 2 * (X * E) := by
    field_simp
  rw [heq]
  exact hweak

/-- The full deterministic high-level second moment, with its two explicit
error terms. Distinctness of the indexed natural entries is the only arithmetic
property used in the off-diagonal estimate. -/
theorem deterministic_mean_two_errors (D : ℝ) (hD : 255 ≤ D) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
      ∀ᶠ S : ℝ in atTop, ∀ (m X C ell : ℝ),
        m ≤ S → Real.exp S ≤ X → X ≤ Real.exp (D * S / 4) →
        Real.exp (D * S) ≤ C → C ≤ Real.exp (2 * D * S) →
        1 ≤ ell → ell ≤ Real.exp (m / 2500) →
        ∀ {β : Type*} (T : Finset β) (t : β → ℕ),
          Set.InjOn t (T : Set β) →
          Real.exp (Real.log 2 * m) ≤ (T.card : ℝ) →
          (∀ i ∈ T, (t i : ℝ) ≤ Real.exp (101 * S)) →
          (∑ u ∈ Finset.Icc (⌊Real.exp (-m / 10000) * X⌋₊ + 1) ⌊X⌋₊,
            ‖(∑ i ∈ T, differencingPhase (ell * C * (t i : ℝ) / (u : ℝ))) /
              (T.card : ℂ)‖ ^ 2) ≤
            X * (Real.exp (-Real.log 2 * m) + A * Real.exp (-c * S)) := by
  obtain ⟨A, c, hA, hc, hglobal⟩ := deterministic_reciprocal_sum_bound D hD
  refine ⟨A, c, hA, hc, ?_⟩
  filter_upwards [hglobal, eventually_ge_atTop (0 : ℝ)] with S hglobal hS
  intro m X C ell hm hXlo hXhi hClo hChi hell hellhi β T t ht hcard hsize
  have hX : 0 < X := (Real.exp_pos S).trans_le hXlo
  have hTpos : (0 : ℝ) < T.card := (Real.exp_pos _).trans_le hcard
  have hT : T.Nonempty := Finset.card_pos.mp (by exact_mod_cast hTpos)
  let U := Finset.Icc (⌊Real.exp (-m / 10000) * X⌋₊ + 1) ⌊X⌋₊
  let z : ℕ → β → ℂ := fun u i => differencingPhase (ell * C * (t i : ℝ) / (u : ℝ))
  have hUcard : (U.card : ℝ) ≤ X := by
    have hh : U.card ≤ ⌊X⌋₊ := by
      dsimp [U]
      rw [Nat.card_Icc]
      omega
    exact (Nat.cast_le.mpr hh).trans (Nat.floor_le hX.le)
  have hbound := finite_second_moment_cutoff U T z X (A * Real.exp (-c * S))
    hT hX.le (by positivity) hUcard (by intros; exact differencingPhase_norm _)
    (by
      intro i hi j hj hij
      have hne : t i ≠ t j := fun heq => hij (ht hi hj heq)
      obtain ⟨hZlo, hZhi⟩ := deterministic_frequency_bounds S m D C ell (t i) (t j)
        hS hm hell hellhi hClo hChi (hsize i hi) (hsize j hj) hne
      have hsum := hglobal m X (ell * C * ((t i : ℝ) - t j))
        (⌊Real.exp (-m / 10000) * X⌋₊ + 1) ⌊X⌋₊ hm hXlo hXhi
        (by
          simpa only [Nat.cast_add, Nat.cast_one] using
            (Nat.lt_floor_add_one (Real.exp (-m / 10000) * X)).le) (Nat.floor_le hX.le) hZlo hZhi
      have heq : (∑ u ∈ U, z u i * conj (z u j)) =
          ∑ u ∈ U, differencingPhase (ell * C * ((t i : ℝ) - t j) / (u : ℝ)) := by
        apply Finset.sum_congr rfl
        intro u hu
        dsimp [z]
        rw [← differencingPhase_sub]
        congr 1
        ring
      rw [heq]
      simpa only [U, mul_assoc, mul_comm, mul_left_comm] using hsum)
  have hinv : 1 / (T.card : ℝ) ≤ Real.exp (-Real.log 2 * m) := by
    calc
      1 / (T.card : ℝ) ≤ 1 / Real.exp (Real.log 2 * m) :=
        one_div_le_one_div_of_le (Real.exp_pos _) hcard
      _ = Real.exp (-Real.log 2 * m) := by rw [one_div, ← Real.exp_neg]; congr 1; ring
  apply hbound.trans
  exact mul_le_mul_of_nonneg_left (add_le_add hinv le_rfl) hX.le

end Problem337

end

end OAI
