import Mathlib.Analysis.PSeries
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCoprimePoisson

namespace OAI

/-! # Quantitative lattice tails for the actual Poisson test function -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

private theorem schwartz_lattice_point_bound (ψ : 𝓢(ℝ, ℂ)) (A : ℕ)
    {Y R : ℝ} (hY : 0 < Y) (hR : 0 < R) (n : ℤ) :
    (if R ≤ |(n : ℝ)| then ‖ψ ((n : ℝ) * Y)‖ else 0) ≤
      (SchwartzMap.seminorm ℝ (A + 2) 0 ψ / (Y ^ (A + 2) * R ^ A)) *
        (1 / (n : ℝ) ^ 2) := by
  by_cases hn : R ≤ |(n : ℝ)|
  · rw [ite_eq_left hn]
    have hnabs : 0 < |(n : ℝ)| := hR.trans_le hn
    have hn0 : (n : ℝ) ≠ 0 := abs_pos.mp hnabs
    have hseminorm := SchwartzMap.norm_pow_mul_le_seminorm ℝ ψ (A + 2) ((n : ℝ) * Y)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hY, mul_pow, pow_add] at hseminorm
    have hh : ‖ψ ((n : ℝ) * Y)‖ * (Y ^ (A + 2) * R ^ A) * (n : ℝ) ^ 2 ≤
        SchwartzMap.seminorm ℝ (A + 2) 0 ψ := by
      calc
        _ ≤ ‖ψ ((n : ℝ) * Y)‖ * (Y ^ (A + 2) * |(n : ℝ)| ^ A) * (n : ℝ) ^ 2 := by
          gcongr
        _ = (|(n : ℝ)| ^ A * |(n : ℝ)| ^ 2) * Y ^ (A + 2) * ‖ψ ((n : ℝ) * Y)‖ := by
          rw [sq_abs]
          ring
        _ ≤ _ := hseminorm
    rw [← div_eq_mul_one_div, le_div_iff₀ (sq_pos_of_ne_zero hn0),
      le_div_iff₀ (mul_pos (pow_pos hY _) (pow_pos hR _))]
    convert hh using 1
    ring
  · rw [ite_eq_right hn]
    positivity

 theorem quadratic_schwartz_lattice_tail (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y R : ℝ, 0 < Y → 0 < R →
      (∑' n : ℤ, if R ≤ |(n : ℝ)| then ‖ψ ((n : ℝ) * Y)‖ else 0) ≤
        C / (Y ^ (A + 2) * R ^ A) := by
  let Z : ℝ := ∑' n : ℤ, 1 / (n : ℝ) ^ 2
  have hZ : 0 ≤ Z := tsum_nonneg (fun _ => by positivity)
  let P : ℝ := SchwartzMap.seminorm ℝ (A + 2) 0 ψ
  have hP : 0 ≤ P := by positivity
  refine ⟨P * Z, mul_nonneg hP hZ, ?_⟩
  intro Y R hY hR
  have hs : Summable (fun n : ℤ => (P / (Y ^ (A + 2) * R ^ A)) * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < 2)).mul_left _
  have hb := fun n => schwartz_lattice_point_bound ψ A hY hR n
  have hf : Summable (fun n : ℤ => if R ≤ |(n : ℝ)| then ‖ψ ((n : ℝ) * Y)‖ else 0) :=
    Summable.of_nonneg_of_le (fun _ => by split_ifs <;> positivity) hb hs
  have ht := hf.tsum_le_tsum hb hs
  rw [tsum_mul_left] at ht
  convert ht using 1
  dsimp only [Z, P]
  ring

 theorem quadratic_schwartz_nonzero_lattice (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, 0 < Y →
      (∑' n : ℤ, if n = 0 then 0 else ‖ψ ((n : ℝ) * Y)‖) ≤ C / Y ^ (A + 2) := by
  obtain ⟨C, hC, hc⟩ := quadratic_schwartz_lattice_tail ψ A
  refine ⟨C, hC, ?_⟩
  intro Y hY
  have hh := hc Y 1 hY zero_lt_one
  have he : (fun n : ℤ => if n = 0 then 0 else ‖ψ ((n : ℝ) * Y)‖) =
      (fun n : ℤ => if 1 ≤ |(n : ℝ)| then ‖ψ ((n : ℝ) * Y)‖ else 0) := by
    funext n
    by_cases hn : n = 0
    · simp [hn]
    · have ha : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
      simp [hn, ha]
  simpa only [he, one_pow, mul_one] using hh

 theorem quadratic_schwartz_frequency_tail (ψ : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℝ, 0 < Y → ∀ L : ℕ,
      (∑' n : ℤ, if L < n.natAbs then ‖ψ ((n : ℝ) * Y)‖ else 0) ≤
        C / (Y ^ (A + 2) * ((L : ℝ) + 1) ^ A) := by
  obtain ⟨C, hC, hc⟩ := quadratic_schwartz_lattice_tail ψ A
  refine ⟨C, hC, ?_⟩
  intro Y hY L
  have hh := hc Y (L + 1) hY (by positivity)
  have he : (fun n : ℤ => if L < n.natAbs then ‖ψ ((n : ℝ) * Y)‖ else 0) =
      (fun n : ℤ => if (L : ℝ) + 1 ≤ |(n : ℝ)| then ‖ψ ((n : ℝ) * Y)‖ else 0) := by
    funext n
    have hi : L < n.natAbs ↔ (L : ℝ) + 1 ≤ |(n : ℝ)| := by
      rw [show |(n : ℝ)| = (n.natAbs : ℝ) by simp]
      exact_mod_cast (Nat.lt_iff_add_one_le : L < n.natAbs ↔ L + 1 ≤ n.natAbs)
    simp only [hi]
  simpa only [he] using hh

end Ostmann

end OAI
