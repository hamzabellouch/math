import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

namespace OAI

/-!
# An inverse-coefficient majorant without exponential loss

The normalized interior convolution of a positive weight sequence tends
to zero.  This makes the inverse recurrence contractive at large orders.
Finite initial orders are bounded uniformly over every sequence satisfying
the recurrence.  The final constant is independent of the sequence and
the order, so it introduces no new exponential base.
-/

open Finset Filter
open scoped BigOperators Topology

noncomputable section

namespace RegularPointCoordinates

/-- The convolution with the two endpoint terms omitted. -/
def interiorConvolution (L : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ l ∈ Finset.Icc 1 (m - 1), L l * L (m - l)

/-- Normalized interior convolution from `re:convolution-decay`. -/
def normalizedInteriorConvolution (L : ℕ → ℝ) (m : ℕ) : ℝ :=
  interiorConvolution L m / L m

/-- The positive-order recurrence after removing the exponential jet base. -/
def HasInverseMajorantRecurrence (L a : ℕ → ℝ) (A : ℝ) : Prop :=
  ∀ m, 0 < m → a m ≤ A * L m + Real.sqrt A *
    ∑ l ∈ Finset.Icc 1 (m - 1), L l * a (m - l)

theorem interiorConvolution_nonneg {L : ℕ → ℝ} (hL : ∀ m, 0 ≤ L m) (m : ℕ) :
    0 ≤ interiorConvolution L m := by
  exact Finset.sum_nonneg fun l _ => mul_nonneg (hL l) (hL (m - l))

theorem normalizedInteriorConvolution_mul {L : ℕ → ℝ}
    (hL : ∀ m, 0 < L m) (m : ℕ) :
    normalizedInteriorConvolution L m * L m = interiorConvolution L m :=
  div_mul_cancel₀ _ (ne_of_gt (hL m))

/-- A bound at smaller orders controls the convolution in the recurrence. -/
theorem inverse_recurrence_step {L a : ℕ → ℝ} {A C : ℝ}
    (hL : ∀ m, 0 < L m) (hrec : HasInverseMajorantRecurrence L a A)
    {m : ℕ} (hm : 0 < m) (hprev : ∀ j < m, a j ≤ C * L j) :
    a m ≤ (A + Real.sqrt A * C * normalizedInteriorConvolution L m) * L m := by
  have hsum : (∑ l ∈ Finset.Icc 1 (m - 1), L l * a (m - l)) ≤
      C * interiorConvolution L m := by
    calc
      _ ≤ ∑ l ∈ Finset.Icc 1 (m - 1), L l * (C * L (m - l)) := by
        apply Finset.sum_le_sum
        intro l hl
        have hlone : 1 ≤ l := (Finset.mem_Icc.mp hl).1
        exact mul_le_mul_of_nonneg_left (hprev (m - l) (by omega)) (hL l).le
      _ = _ := by
        unfold interiorConvolution
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
  calc
    a m ≤ A * L m + Real.sqrt A *
        ∑ l ∈ Finset.Icc 1 (m - 1), L l * a (m - l) := hrec m hm
    _ ≤ A * L m + Real.sqrt A * (C * interiorConvolution L m) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg A))
    _ = _ := by rw [← normalizedInteriorConvolution_mul hL m]; ring

/-- All orders below a finite cutoff have a common bound derived from
the recurrence itself, uniform over every admissible sequence. -/
theorem inverse_majorant_finite_prefix {L : ℕ → ℝ} {A initial : ℝ}
    (hL : ∀ m, 0 < L m) (hinitial : 0 ≤ initial) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℕ → ℝ,
      a 0 ≤ initial * L 0 → HasInverseMajorantRecurrence L a A →
      ∀ m < N, a m ≤ C * L m := by
  induction N with
  | zero => exact ⟨initial, hinitial, fun _ _ _ m hm => (Nat.not_lt_zero m hm).elim⟩
  | succ N ih =>
    obtain ⟨C, hC, hbound⟩ := ih
    let D := max C (max initial
      (A + Real.sqrt A * C * normalizedInteriorConvolution L N))
    refine ⟨D, hC.trans (le_max_left _ _), ?_⟩
    intro a ha0 hrec m hm
    by_cases hmN : m < N
    · exact (hbound a ha0 hrec m hmN).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (hL m).le)
    · have hmEq : m = N := by omega
      subst m
      by_cases hN : N = 0
      · subst N
        exact ha0.trans (mul_le_mul_of_nonneg_right
          ((le_max_left initial _).trans (le_max_right C _)) (hL 0).le)
      · exact (inverse_recurrence_step hL hrec (Nat.pos_of_ne_zero hN)
          (hbound a ha0 hrec)).trans (mul_le_mul_of_nonneg_right
            ((le_max_right initial _).trans (le_max_right C _)) (hL N).le)

/-- Vanishing normalized convolution implies a uniform inverse majorant.
The same constant works for every admissible sequence. -/
theorem inverse_majorant_uniform {L : ℕ → ℝ} {A initial : ℝ}
    (hL : ∀ m, 0 < L m) (hA : 0 ≤ A) (hinitial : 0 ≤ initial)
    (hdecay : Tendsto (normalizedInteriorConvolution L) atTop (𝓝 0)) :
    ∃ C : ℝ, initial ≤ C ∧ 2 * A ≤ C ∧ 0 ≤ C ∧
      ∀ a : ℕ → ℝ, a 0 ≤ initial * L 0 →
        HasInverseMajorantRecurrence L a A → ∀ m, a m ≤ C * L m := by
  have hlim : Tendsto (fun m => Real.sqrt A * normalizedInteriorConvolution L m)
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hdecay
  have hsmall : ∀ᶠ m in atTop,
      Real.sqrt A * normalizedInteriorConvolution L m ≤ 1 / 2 := by
    exact (hlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      fun _ h => h.le
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp hsmall
  let M := max M₀ 1
  obtain ⟨D, _, hprefix⟩ := inverse_majorant_finite_prefix hL hinitial M
  let C := max initial (max (2 * A) D)
  have hIC : initial ≤ C := le_max_left _ _
  have hAC : 2 * A ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hDC : D ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hC : 0 ≤ C := (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA).trans hAC
  refine ⟨C, hIC, hAC, hC, ?_⟩
  intro a ha0 hrec m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m < M
    · exact (hprefix a ha0 hrec m hm).trans
        (mul_le_mul_of_nonneg_right hDC (hL m).le)
    · have hmM : M ≤ m := Nat.le_of_not_gt hm
      have hmpos : 0 < m := lt_of_lt_of_le (by dsimp [M]; omega) hmM
      have hsmallm := hM₀ m ((le_max_left M₀ 1).trans hmM)
      have hcontract : A + Real.sqrt A * C * normalizedInteriorConvolution L m ≤ C := by
        have hmul := mul_le_mul_of_nonneg_left hsmallm hC
        nlinarith
      exact (inverse_recurrence_step hL hrec hmpos ih).trans
        (mul_le_mul_of_nonneg_right hcontract (hL m).le)

/-- Specialization to the initial inverse norm `√A` used by the manuscript. -/
theorem inverse_coefficients_uniform_bound {L : ℕ → ℝ} {A : ℝ}
    (hL : ∀ m, 0 < L m) (hLzero : L 0 = 1) (hA : 1 ≤ A)
    (hdecay : Tendsto (normalizedInteriorConvolution L) atTop (𝓝 0)) :
    ∃ C : ℝ, Real.sqrt A ≤ C ∧ 2 * A ≤ C ∧
      ∀ a : ℕ → ℝ, a 0 ≤ Real.sqrt A →
        HasInverseMajorantRecurrence L a A → ∀ m, a m ≤ C * L m := by
  obtain ⟨C, hIC, hAC, _, hbound⟩ := inverse_majorant_uniform hL
    (zero_le_one.trans hA) (Real.sqrt_nonneg A) hdecay
  refine ⟨C, hIC, hAC, ?_⟩
  intro a ha0 hrec
  exact hbound a (by simpa [hLzero] using ha0) hrec

end RegularPointCoordinates

end

end OAI
