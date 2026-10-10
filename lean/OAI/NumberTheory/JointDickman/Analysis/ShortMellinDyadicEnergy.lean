import OAI.NumberTheory.JointDickman.Analysis.ShortMellinEnergy

namespace OAI

/-! # A finite block cover for the full dyadic short-average integral -/
namespace JointDickman
open Finset MeasureTheory PublishedInputs

/-- The spectral bound is needed only on subintervals of the coefficient
range [X,4X]. The number of blocks is fixed before the short length grows. -/
theorem shortAverage_dyadic_energy (η : ℝ) (hη : 0 < η) (hηhalf : η < 1/2)
    (m : ℕ) (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ArithmeticFunction ℂ), (∀ n, ‖f n‖ ≤ 1) →
      ∀ X H : ℝ, 0 < X → 1 ≤ H → H ≤ X → ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      (∀ T : ℝ, 1 ≤ T →
        (∫ t in -T..T, ‖mellinPolynomial (Ioc ⌊X⌋₊ ⌊4 * X⌋₊) f t‖ ^ 2) ≤ A + B * T) →
      (1 / X) * (∫ x in X..2 * X, ‖complexShortAverage f H x‖ ^ 2) ≤
        C * (A + B * X / H) +
          2 * (3 / (m : ℝ) + 11 / H + H / X + 1 / X + 16 * η) ^ 2 := by
  obtain ⟨C, hC, hblock⟩ := shortAverage_block_energy_of_support η hη hηhalf
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  refine ⟨4 * (m : ℝ) * C, by positivity, ?_⟩
  intro f hf X H hX hH hHX A B hA hB hspectral
  have hH0 : 0 < H := by linarith
  let a : ℕ → ℝ := fun j => X + (j : ℝ) * (X / m)
  let e : ℕ → ℝ := fun j => (X / m) / a j
  let E : ℝ := 3 / (m : ℝ) + 11 / H + H / X + 1 / X + 16 * η
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have ha0 : a 0 = X := by simp [a]
  have ham : a m = 2 * X := by dsimp [a]; field_simp; ring
  have ha (j : ℕ) (hj : j ≤ m) : a j ∈ Set.Icc X (2 * X) := by
    have hj' : (j : ℝ) ≤ m := by exact_mod_cast hj
    dsimp [a]
    constructor
    · exact le_add_of_nonneg_right (by positivity)
    · have hh := mul_le_mul_of_nonneg_right hj' (show 0 ≤ X / m by positivity)
      rw [mul_div_cancel₀ X hm0.ne'] at hh
      linarith
  have hap (j : ℕ) (hj : j ≤ m) : 0 < a j := hX.trans_le (ha j hj).1
  have he (j : ℕ) (hj : j ≤ m) : e j ∈ Set.Icc (0 : ℝ) (1 / (m : ℝ)) := by
    constructor
    · dsimp [e]; positivity
    · dsimp [e]
      apply (div_le_iff₀ (hap j hj)).mpr
      have hh := div_le_div_of_nonneg_right (ha j hj).1 hm0.le
      simpa only [one_div_mul_eq_div] using hh
  have hstep (j : ℕ) (hj : j ≤ m) : (1 + e j) * a j = a (j + 1) := by
    dsimp [e]
    rw [add_mul, one_mul, div_mul_cancel₀ _ (hap j hj).ne']
    simp only [a, Nat.cast_add, Nat.cast_one]
    ring
  have hcell (j : ℕ) (hj : j < m) :
      (∫ x in a j..a (j + 1), ‖complexShortAverage f H x‖ ^ 2) ≤
        2 * X * C * (A + 2 * (B * X / H)) + 2 * (X / m) * E ^ 2 := by
    have hjle := hj.le
    have hU := ha j hjle
    have hU0 := hap j hjle
    have he' := he j hjle
    have he1 : e j ≤ 1 := he'.2.trans ((one_div_le_one_div_of_le (by norm_num) hm1).trans_eq (one_div_one))
    have hHU : H ≤ a j := hHX.trans hU.1
    let Ej := 3 * e j + 11 / H + H / a j + 1 / a j + 16 * η
    have hEj0 : 0 ≤ Ej := by dsimp [Ej]; positivity
    have hEj : Ej ≤ E := by
      have h3 := mul_le_mul_of_nonneg_left he'.2 (by norm_num : (0 : ℝ) ≤ 3)
      have hratio := div_le_div_of_nonneg_left hH0.le hX hU.1
      have hinv := one_div_le_one_div_of_le hX hU.1
      dsimp [Ej, E]
      simp only [div_eq_mul_inv] at h3 hratio hinv ⊢
      linarith only [h3, hratio, hinv]
    have hupper : (1 + e j) * (a j + H) ≤ 4 * X := by
      have hh := (ha (j + 1) (by omega)).2
      have heH := mul_le_mul_of_nonneg_right he1 hH0.le
      have hstep' := hstep j hjle
      nlinarith
    have hb := hblock f hf ⌊X⌋₊ ⌊4 * X⌋₊ (a j) H (e j) hU0 hH hHU he'.1 he1
      (Nat.floor_mono hU.1) (Nat.floor_mono hupper) A B hA hB hspectral
    rw [hstep j hjle] at hb
    have hraw : (∫ x in a j..a (j + 1), ‖complexShortAverage f H x‖ ^ 2) ≤
        a j * (C * (A + B * a j / H) + 2 * e j * Ej ^ 2) := by
      have hh : (∫ x in a j..a (j + 1), ‖complexShortAverage f H x‖ ^ 2) / a j ≤
          C * (A + B * a j / H) + 2 * e j * Ej ^ 2 := by
        simpa only [one_div_mul_eq_div, Ej] using hb
      simpa only [mul_comm] using (div_le_iff₀ hU0).mp hh
    have hmain : a j * (C * (A + B * a j / H)) ≤
        2 * X * C * (A + 2 * (B * X / H)) := by
      have hr : B * a j / H ≤ 2 * (B * X / H) := by
        calc
          _ ≤ B * (2 * X) / H := by gcongr; exact hU.2
          _ = _ := by ring
      calc
        _ ≤ (2 * X) * (C * (A + 2 * (B * X / H))) := by gcongr; exact hU.2
        _ = _ := by ring
    have herr : a j * (2 * e j * Ej ^ 2) ≤ 2 * (X / m) * E ^ 2 := by
      have heq : a j * (2 * e j * Ej ^ 2) = 2 * (X / m) * Ej ^ 2 := by
        dsimp [e]
        field_simp
      rw [heq]
      gcongr
    calc
      _ ≤ a j * (C * (A + B * a j / H)) + a j * (2 * e j * Ej ^ 2) := by
        simpa only [mul_add] using hraw
      _ ≤ _ := add_le_add hmain herr
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (a := a) (n := m) (fun j _ => complexShortAverage_sq_integrable f hf hH0 (a j) (a (j + 1)))
  rw [ha0, ham] at hsplit
  have hsum := sum_le_sum (fun j hj => hcell j (mem_range.mp hj))
  rw [hsplit, sum_const, nsmul_eq_mul, card_range] at hsum
  have hscale := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 1 / X by positivity)
  have hright : (1 / X) * ((m : ℝ) *
      (2 * X * C * (A + 2 * (B * X / H)) + 2 * (X / m) * E ^ 2)) =
      2 * (m : ℝ) * C * (A + 2 * (B * X / H)) + 2 * E ^ 2 := by field_simp
  rw [hright] at hscale
  have hlast : 2 * (m : ℝ) * C * (A + 2 * (B * X / H)) ≤
      4 * (m : ℝ) * C * (A + B * X / H) := by
    nlinarith [mul_nonneg (show 0 ≤ (m : ℝ) * C by positivity) hA]
  exact hscale.trans (add_le_add hlast le_rfl)

end JointDickman

end OAI
