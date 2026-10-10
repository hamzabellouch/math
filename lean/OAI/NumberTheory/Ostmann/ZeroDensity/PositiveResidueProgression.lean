import OAI.NumberTheory.Ostmann.Quadratic.QuadraticResidueDecomposition

namespace OAI

/-! # The exact finite progression of positive integers in a residue class -/

namespace Ostmann

open scoped BigOperators

theorem exists_positive_residue_representative {q : ℕ} [NeZero q] (r : ZMod q) :
    ∃ a : ℕ, 0 < a ∧ a ≤ q ∧ (a : ZMod q) = r := by
  by_cases hr : r.val = 0
  · refine ⟨q, NeZero.pos q, le_rfl, ?_⟩
    have hz : r = 0 := by simpa only [hr, Nat.cast_zero] using r.natCast_zmod_val.symm
    simp [hz]
  · exact ⟨r.val, Nat.pos_of_ne_zero hr, r.val_lt.le, r.natCast_zmod_val⟩

theorem positive_residue_progression (q a W : ℕ) (hq : 0 < q)
    (ha : 0 < a) (haq : a ≤ q) :
    ((Finset.Ioc 0 W).filter (fun w => w ≡ a [MOD q])) =
      (Finset.range ((W + q - a) / q)).image (fun j => a + q * j) := by
  classical
  have haqW : a ≤ W + q := by omega
  have hsub : W + q - a + a = W + q := Nat.sub_add_cancel haqW
  ext w
  constructor
  · intro hw
    obtain ⟨hw, hmod⟩ := Finset.mem_filter.mp hw
    obtain ⟨hw0, hwW⟩ := Finset.mem_Ioc.mp hw
    have haw : a ≤ w := by
      rcases lt_or_eq_of_le haq with haq' | heq
      · have hm : w % q = a := (show w % q = a % q from hmod).trans (Nat.mod_eq_of_lt haq')
        rw [← hm]
        exact Nat.mod_le w q
      · have hqw : q ∣ w := by
          apply Nat.dvd_of_mod_eq_zero
          simpa only [heq, Nat.mod_self] using (show w % q = a % q from hmod)
        exact heq ▸ Nat.le_of_dvd hw0 hqw
    obtain ⟨j, hj⟩ := hmod.symm.dvd'
    have hval : a + q * j = w := by omega
    refine Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr ?_, hval⟩
    apply Nat.lt_of_succ_le
    apply (Nat.le_div_iff_mul_le hq).mpr
    nlinarith
  · intro hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    have hh := (Nat.le_div_iff_mul_le hq).mp (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨by omega, ?_⟩, ?_⟩
    · nlinarith
    · simp [Nat.ModEq]

theorem sum_positive_residue_progression (q a W : ℕ) (hq : 0 < q)
    (ha : 0 < a) (haq : a ≤ q) (f : ℕ → ℂ) :
    (∑ w ∈ (Finset.Ioc 0 W).filter (fun w => w ≡ a [MOD q]), f w) =
      ∑ j ∈ Finset.range ((W + q - a) / q), f (a + q * j) := by
  classical
  rw [positive_residue_progression q a W hq ha haq, Finset.sum_image]
  intro j _ k _ he
  exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_left_cancel he)

theorem sum_positive_zmod_progression {q : ℕ} [NeZero q] (a W : ℕ)
    (ha : 0 < a) (haq : a ≤ q) (f : ℕ → ℂ) :
    (∑ w ∈ (Finset.Ioc 0 W).filter (fun w : ℕ => (w : ZMod q) = a), f w) =
      ∑ j ∈ Finset.range ((W + q - a) / q), f (a + q * j) := by
  simp_rw [ZMod.natCast_eq_natCast_iff]
  exact sum_positive_residue_progression q a W (NeZero.pos q) ha haq f

/-- The floor cutoff loses less than two progression steps, uniformly in the
residue. This keeps the inverse estimate at the original quadratic scale. -/
theorem positive_progression_length_bounds (q a : ℕ) (B Y : ℝ)
    (hq : 0 < q) (ha : 0 < a) (haq : a ≤ q) (hB : 3 ≤ B) (hY : 1 ≤ Y) :
    let W := ⌊B * q * Y⌋₊
    let N := (W + q - a) / q
    Y ≤ (N : ℝ) ∧ (N : ℝ) ≤ (B + 1) * Y := by
  dsimp only
  let W := ⌊B * q * Y⌋₊
  let N := (W + q - a) / q
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have haqR : (a : ℝ) ≤ q := by exact_mod_cast haq
  have hfloor : (W : ℝ) ≤ B * q * Y := Nat.floor_le (by positivity)
  have hfloor' : B * q * Y < (W : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsub : W + q - a + a = W + q := Nat.sub_add_cancel (by omega)
  have hdiv : N * q ≤ W + q - a := Nat.div_mul_le_self _ _
  have hdiv' : W + q - a < (N + 1) * q := by
    exact (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self N)
  have hsubR : ((W + q - a : ℕ) : ℝ) + a = (W : ℝ) + q := by exact_mod_cast hsub
  have hdivR : (N : ℝ) * q ≤ ((W + q - a : ℕ) : ℝ) := by exact_mod_cast hdiv
  have hdivR' : ((W + q - a : ℕ) : ℝ) < ((N : ℝ) + 1) * q := by exact_mod_cast hdiv'
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  constructor
  · have hBY : 3 * Y ≤ B * Y := mul_le_mul_of_nonneg_right hB (by linarith)
    have hYq : 1 ≤ Y * q := by nlinarith
    have hBYq : 3 * Y * q ≤ B * q * Y := by nlinarith [mul_le_mul_of_nonneg_right hBY hqpos.le]
    nlinarith
  · have hYq : (q : ℝ) ≤ Y * q := le_mul_of_one_le_left hqpos.le hY
    nlinarith

end Ostmann

end OAI
