import OAI.NumberTheory.Ostmann.Tree.UniformGroupReduction

namespace OAI

/-! # The two simultaneous square congruences at a history split -/

namespace Ostmann

open scoped BigOperators Classical

theorem unitsMap_eq_iff_modEq {q Q : ℕ} [NeZero Q] (h : q ∣ Q)
    (x y : (ZMod Q)ˣ) :
    ZMod.unitsMap h x = ZMod.unitsMap h y ↔
      Nat.ModEq q (x : ZMod Q).val (y : ZMod Q).val := by
  rw [← Units.val_inj]
  change ZMod.castHom h (ZMod q) (x : ZMod Q) =
    ZMod.castHom h (ZMod q) (y : ZMod Q) ↔ _
  nth_rw 1 [← ZMod.natCast_zmod_val (x : ZMod Q), ← ZMod.natCast_zmod_val (y : ZMod Q)]
  simp only [map_natCast, ZMod.natCast_eq_natCast_iff]

theorem lcm_units_ext {a b : ℕ} [NeZero (a.lcm b)] (x y : (ZMod (a.lcm b))ˣ)
    (ha : ZMod.unitsMap (Nat.dvd_lcm_left a b) x = ZMod.unitsMap (Nat.dvd_lcm_left a b) y)
    (hb : ZMod.unitsMap (Nat.dvd_lcm_right a b) x = ZMod.unitsMap (Nat.dvd_lcm_right a b) y) :
    x = y := by
  have hma := (unitsMap_eq_iff_modEq (Nat.dvd_lcm_left a b) x y).mp ha
  have hmb := (unitsMap_eq_iff_modEq (Nat.dvd_lcm_right a b) x y).mp hb
  have hm := Nat.mod_lcm hma hmb
  apply Units.ext
  simpa only [ZMod.natCast_zmod_val] using
    (ZMod.natCast_eq_natCast_iff (x : ZMod (a.lcm b)).val
      (y : ZMod (a.lcm b)).val (a.lcm b)).mpr hm

theorem simultaneous_square_probability_le {a b : ℕ} [NeZero a] [NeZero b]
    [NeZero (a.lcm b)] (A : (ZMod a)ˣ) (B : (ZMod b)ˣ) :
    (Fintype.card (ZMod (a.lcm b))ˣ : ℝ)⁻¹ *
        (∑ x : (ZMod (a.lcm b))ˣ,
          if (ZMod.unitsMap (Nat.dvd_lcm_left a b) x) ^ 2 = A ∧
            (ZMod.unitsMap (Nat.dvd_lcm_right a b) x) ^ 2 = B then (1 : ℝ) else 0) ≤
      2 * ((a.lcm b).divisors.card : ℝ) ^ 2 / (a.lcm b) := by
  let P := fun x : (ZMod (a.lcm b))ˣ =>
    (ZMod.unitsMap (Nat.dvd_lcm_left a b) x) ^ 2 = A ∧
      (ZMod.unitsMap (Nat.dvd_lcm_right a b) x) ^ 2 = B
  by_cases hex : ∃ r, P r
  · obtain ⟨r, hr⟩ := hex
    have heq (x : (ZMod (a.lcm b))ˣ) : P x ↔ x ^ 2 = r ^ 2 := by
      constructor
      · intro hx
        apply lcm_units_ext
        · simp only [map_pow]
          exact hx.1.trans hr.1.symm
        · simp only [map_pow]
          exact hx.2.trans hr.2.symm
      · intro hx
        constructor
        · have ht := congrArg (ZMod.unitsMap (Nat.dvd_lcm_left a b)) hx
          rw [map_pow, map_pow] at ht
          exact ht.trans hr.1
        · have ht := congrArg (ZMod.unitsMap (Nat.dvd_lcm_right a b)) hx
          rw [map_pow, map_pow] at ht
          exact ht.trans hr.2
    change (Fintype.card (ZMod (a.lcm b))ˣ : ℝ)⁻¹ * (∑ x, if P x then 1 else 0) ≤ _
    simp_rw [heq]
    have hs : (∑ x : (ZMod (a.lcm b))ˣ, if x ^ 2 = r ^ 2 then (1 : ℝ) else 0) =
        (Nat.card {x : (ZMod (a.lcm b))ˣ // x ^ 2 = r ^ 2} : ℝ) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hs, mul_comm, ← div_eq_mul_inv]
    exact unit_square_probability_le (a.lcm b) (r ^ 2)
  · have hn : ∀ x, ¬P x := by simpa only [not_exists] using hex
    change (Fintype.card (ZMod (a.lcm b))ˣ : ℝ)⁻¹ * (∑ x, if P x then 1 else 0) ≤ _
    simp only [hn, ↓reduceIte, Finset.sum_const_zero, mul_zero]
    positivity

/-- The support probability under the original larger Haar modulus, before
conditioning on any history tests. -/
theorem reduced_simultaneous_square_probability_le {a b Q : ℕ}
    [NeZero a] [NeZero b] [NeZero Q]
    (ha : a ∣ Q) (hb : b ∣ Q) (A : (ZMod a)ˣ) (B : (ZMod b)ˣ) :
    (Fintype.card (ZMod Q)ˣ : ℝ)⁻¹ *
        (∑ x : (ZMod Q)ˣ,
          if (ZMod.unitsMap ha x) ^ 2 = A ∧ (ZMod.unitsMap hb x) ^ 2 = B then (1 : ℝ) else 0) ≤
      2 * ((a.lcm b).divisors.card : ℝ) ^ 2 / (a.lcm b) := by
  let _ : NeZero (a.lcm b) := ⟨Nat.lcm_ne_zero (NeZero.ne a) (NeZero.ne b)⟩
  have hL : a.lcm b ∣ Q := Nat.lcm_dvd ha hb
  have hleft (x : (ZMod Q)ˣ) : ZMod.unitsMap (Nat.dvd_lcm_left a b) (ZMod.unitsMap hL x) =
      ZMod.unitsMap ha x := DFunLike.congr_fun (ZMod.unitsMap_comp (Nat.dvd_lcm_left a b) hL) x
  have hright (x : (ZMod Q)ˣ) : ZMod.unitsMap (Nat.dvd_lcm_right a b) (ZMod.unitsMap hL x) =
      ZMod.unitsMap hb x := DFunLike.congr_fun (ZMod.unitsMap_comp (Nat.dvd_lcm_right a b) hL) x
  have heq := unit_reduction_average hL (fun x =>
    if (ZMod.unitsMap (Nat.dvd_lcm_left a b) x) ^ 2 = A ∧
      (ZMod.unitsMap (Nat.dvd_lcm_right a b) x) ^ 2 = B then (1 : ℝ) else 0)
  simp only [hleft, hright] at heq
  exact heq.trans_le (simultaneous_square_probability_le A B)

end Ostmann

end OAI
