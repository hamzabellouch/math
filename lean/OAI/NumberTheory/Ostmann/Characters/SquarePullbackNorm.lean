import Mathlib.Analysis.Complex.Norm
import OAI.NumberTheory.Ostmann.Quadratic.KernelResidueCount

namespace OAI

/-! # The small-kernel quadratic pullback norm -/

namespace Ostmann

open scoped BigOperators

/-- Vanishing at nonunits means only unit square fibers contribute.
The general unit-root bound loses at most an absolute factor two. -/
theorem square_pullback_energy_le (q : ℕ) [NeZero q]
    (g : ZMod q → ℂ) (hg : ∀ x, ¬IsUnit x → g x = 0) (a : ZMod q) :
    (∑ x : ZMod q, ‖g (a * x ^ 2)‖ ^ 2) ≤
      (2 : ℝ) ^ (q.primeFactors.card + 1) * ∑ y : ZMod q, ‖g y‖ ^ 2 := by
  classical
  by_cases hau : IsUnit a
  · let A := hau.unit
    have hfiber (y : ZMod q) (hy : IsUnit y) :
        ((Finset.univ : Finset (ZMod q)).filter (fun x => a * x ^ 2 = y)).card ≤
          2 ^ (q.primeFactors.card + 1) := by
      let Y := hy.unit
      have hsub : ((Finset.univ : Finset (ZMod q)).filter (fun x => a * x ^ 2 = y)) ⊆
          Finset.univ.filter (fun x => IsUnit x ∧ x ^ 2 = ((A⁻¹ * Y : (ZMod q)ˣ) : ZMod q)) := by
        intro x hx
        have he := (Finset.mem_filter.mp hx).2
        have hux : IsUnit (x * x) := by
          have hh : IsUnit (a * x ^ 2) := he ▸ hy
          simpa only [pow_two] using isUnit_of_mul_isUnit_right hh
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, isUnit_of_mul_isUnit_left hux, ?_⟩
        calc
          x ^ 2 = (A⁻¹ : (ZMod q)ˣ) * (a * x ^ 2) := by
            rw [← mul_assoc]
            have hA : (A⁻¹ : (ZMod q)ˣ) * a = (1 : ZMod q) := by
              rw [← hau.unit_spec]
              exact A.inv_mul
            rw [hA, one_mul]
          _ = ((A⁻¹ * Y : (ZMod q)ˣ) : ZMod q) := by rw [he]; simp [Y]
      exact (Finset.card_le_card hsub).trans (unit_square_residue_card_le q (A⁻¹ * Y))
    have hmaps (x : ZMod q) (_ : x ∈ (Finset.univ : Finset (ZMod q))) :
        a * x ^ 2 ∈ (Finset.univ : Finset (ZMod q)) := Finset.mem_univ _
    rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y hy
    have he : (∑ x ∈ Finset.univ.filter (fun x : ZMod q => a * x ^ 2 = y),
        ‖g (a * x ^ 2)‖ ^ 2) =
        ((Finset.univ.filter (fun x : ZMod q => a * x ^ 2 = y)).card : ℝ) * ‖g y‖ ^ 2 := by
      calc
        _ = ∑ _x ∈ Finset.univ.filter (fun x : ZMod q => a * x ^ 2 = y), ‖g y‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
        _ = _ := by simp
    rw [he]
    by_cases hyu : IsUnit y
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfiber y hyu) (sq_nonneg _)
    · simp [hg y hyu]
  · have hz (x : ZMod q) : g (a * x ^ 2) = 0 := by
      apply hg
      intro hh
      exact hau (isUnit_of_mul_isUnit_left hh)
    simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]
    positivity

theorem square_pullback_norm_le (q : ℕ) [NeZero q]
    (g : ZMod q → ℂ) (hg : ∀ x, ¬IsUnit x → g x = 0)
    (henergy : (∑ y : ZMod q, ‖g y‖ ^ 2) ≤ q) (a : ZMod q) :
    (∑ x : ZMod q, ‖g (a * x ^ 2)‖) ≤
      Real.sqrt ((2 : ℝ) ^ (q.primeFactors.card + 1)) * q := by
  have hsq := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod q))
    (fun _ => (1 : ℝ)) (fun x => ‖g (a * x ^ 2)‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one] at hsq
  have hbound := (square_pullback_energy_le q g hg a).trans
    (mul_le_mul_of_nonneg_left henergy (by positivity))
  have hroot := Real.sq_sqrt (show 0 ≤ (2 : ℝ) ^ (q.primeFactors.card + 1) by positivity)
  have hsum : 0 ≤ ∑ x : ZMod q, ‖g (a * x ^ 2)‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have htotal := mul_le_mul_of_nonneg_left hbound (show (0 : ℝ) ≤ q by positivity)
  have hsquare : (∑ x : ZMod q, ‖g (a * x ^ 2)‖) ^ 2 ≤
      (Real.sqrt ((2 : ℝ) ^ (q.primeFactors.card + 1)) * q) ^ 2 := by
    rw [mul_pow, hroot]
    nlinarith
  exact (sq_le_sq₀ hsum (by positivity)).mp hsquare

end Ostmann

end OAI
