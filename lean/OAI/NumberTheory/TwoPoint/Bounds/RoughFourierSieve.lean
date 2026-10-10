import OAI.NumberTheory.TwoPoint.Bounds.RoughSieveCounts
import OAI.NumberTheory.TwoPoint.Bounds.SieveBoundaryScale
import OAI.NumberTheory.TwoPoint.Bounds.MertensScale

namespace OAI

/-! The manuscript rough-integer Fourier estimates, deduced from the
published bounded Mertens input and the proved finite sieve. -/

namespace TwoPointCorrelations

open Finset Filter MeasureTheory
open scoped Classical

/-- Manuscript `(q:rough-fourier)`, uniformly in the interval length and in
every subset of the integers having no prime factor below the cutoff. -/
theorem PrimeReciprocalInput.rough_fourier (hM : PrimeReciprocalInput) :
    ∃ U V : ℝ, 0 < U ∧ 0 < V ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (D h : ℕ), (1 / 2 : ℝ) * Real.exp (L ^ (199 / 200 : ℝ)) ≤ D → 0 < h →
      ∀ Z : Finset ℕ,
      (∀ z ∈ Z, D ≤ z ∧ z < D + D ∧
        avoidsPrimeSet (sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ)))) z) →
      (∀ θ, ‖roughFourierPolynomial Z h θ‖ ≤ U * L ^ (-99 / 100 : ℝ)) ∧
      (∫ θ, ‖roughFourierPolynomial Z h θ‖ ^ 4 ∂AddCircle.haarAddCircle) ≤
        V / (D : ℝ) * L ^ (-99 / 25 : ℝ) := by
  obtain ⟨C, hC, hprime⟩ := hM.rough_scale
  refine ⟨Real.exp C + 2, Real.exp (4 * C + 6) + 2, by positivity, by positivity, ?_⟩
  filter_upwards [hprime, eventually_ge_atTop (Real.exp 1),
    eventually_sieve_boundary_cost 1002 1 (by norm_num) zero_le_one,
    eventually_sieve_boundary_cost 1002 3 (by norm_num) (by norm_num)] with
    L hprimeL hL hb₁ hb₃
  intro D h hD hh Z hZ
  have hL₁ : 1 ≤ L := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hL
  have hlog : 1 ≤ Real.log L := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hL
  have hDp : (0 : ℝ) < D := lt_of_lt_of_le (by positivity) hD
  have hDN : 0 < D := by exact_mod_cast hDp
  let : NeZero D := ⟨hDN.ne'⟩
  let Y := Real.exp (L ^ (99 / 100 : ℝ))
  let P := sievePrimesUpTo Y
  let r := ⌈500 * Real.log L⌉₊
  have hY : 0 ≤ Y := (Real.exp_pos _).le
  have hP (p : ℕ) (hp : p ∈ P) : Nat.Prime p := sievePrimesUpTo_prime Y p hp
  have hmax (p : ℕ) (hp : p ∈ P) : (p : ℝ) ≤ Y := sievePrimesUpTo_le Y hY p hp
  have hcard : (P.card : ℝ) ≤ Y := sievePrimesUpTo_card_le Y hY
  have hrlo : 220 * Real.log L ≤ (2 * r + 1 : ℕ) := by
    have hr : 500 * Real.log L ≤ (r : ℝ) := Nat.le_ceil _
    push_cast
    linarith
  have hrhi : (2 * r : ℕ) ≤ (1002 : ℝ) * Real.log L := by
    have hr : (r : ℝ) < 500 * Real.log L + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    push_cast
    linarith
  have he₁ := hb₁ Y P.card D (2 * r) hY (Nat.cast_nonneg _) hcard le_rfl hrhi hD
  have he₃ := hb₃ Y P.card D (2 * r) hY (Nat.cast_nonneg _) hcard le_rfl hrhi hD
  have hup : (∑ p ∈ P, 1 / (p : ℝ)) ≤ 5 * Real.log L := by
    have hp := hprimeL.2
    change (∑ p ∈ P, 1 / (p : ℝ)) ≤ (5 / 4 : ℝ) * Real.log L at hp
    linarith
  have hprob₁ := rough_interval_probability P hP D D r L C Y hL₁ hY hmax
    hprimeL.1 hup hrlo
  have hprob₃ := rough_cube_probability P hP (D, D, D) D r L C Y hL₁ hY hmax
    hprimeL.1 hprimeL.2 hrlo
  have hpower₁ : L ^ (-100 : ℝ) ≤ L ^ (-99 / 100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL₁ (by norm_num)
  have hpower₃ : L ^ (-100 : ℝ) ≤ L ^ (-99 / 25 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL₁ (by norm_num)
  apply roughFourier_bounds_of_sieve P Z D h hh L (Real.exp C + 2)
    (Real.exp (4 * C + 6) + 2) hZ
  · exact hprob₁.trans (by nlinarith only [he₁, hpower₁])
  · exact hprob₃.trans (by nlinarith only [he₃, hpower₃])

end TwoPointCorrelations

end OAI
