import OAI.Geometry.HeilbronnTriangle.LatticeBox

namespace OAI


noncomputable section

namespace Problem355.LatticeBox

open Finset

theorem one_le_norm_realVector {d : ℕ} {v : Fin d → ℤ} (hv : v ≠ 0) :
    1 ≤ ‖realVector v‖ := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv
    ext i
    simpa using not_exists.mp h i
  have ha : (1 : ℤ) ≤ |v i| := Int.one_le_abs hi
  have har : (1 : ℝ) ≤ |(v i : ℝ)| := by exact_mod_cast ha
  exact har.trans (abs_coord_le_norm v i)

theorem reciprocal_cube_shell_le {R : ℝ} (hR : 1 ≤ R)
    (S : Finset (Fin 3 → ℤ))
    (hS : ∀ v ∈ S, R ≤ ‖realVector v‖ ∧ ‖realVector v‖ ≤ 2 * R) :
    ∑ v ∈ S, 1 / ‖realVector v‖ ^ 3 ≤ 125 := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hcount := card_le_of_norm_bound_twice hR S (fun v hv => (hS v hv).2)
  calc
    ∑ v ∈ S, 1 / ‖realVector v‖ ^ 3 ≤ ∑ _v ∈ S, 1 / R ^ 3 := by
      apply Finset.sum_le_sum
      intro v hv
      apply one_div_le_one_div_of_le (pow_pos hRpos 3)
      exact pow_le_pow_left₀ hRpos.le (hS v hv).1 3
    _ = (S.card : ℝ) / R ^ 3 := by simp [div_eq_mul_inv]
    _ ≤ 125 := (div_le_iff₀ (pow_pos hRpos 3)).mpr hcount

theorem reciprocal_cube_sum_lt_pow_le (m : ℕ) (S : Finset (Fin 3 → ℤ))
    (hS : ∀ v ∈ S, 1 ≤ ‖realVector v‖ ∧ ‖realVector v‖ < (2 : ℝ) ^ m) :
    ∑ v ∈ S, 1 / ‖realVector v‖ ^ 3 ≤ 125 * (m : ℝ) := by
  induction m generalizing S with
  | zero =>
      have hempty : S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        have h := hS v hv
        simpa using not_lt_of_ge h.1 h.2
      simp [hempty]
  | succ m ih =>
      let A := S.filter (fun v => ‖realVector v‖ < (2 : ℝ) ^ m)
      let B := S.filter (fun v => ¬ ‖realVector v‖ < (2 : ℝ) ^ m)
      have hA : ∑ v ∈ A, 1 / ‖realVector v‖ ^ 3 ≤ 125 * (m : ℝ) := by
        apply ih
        intro v hv
        exact ⟨(hS v (Finset.mem_filter.mp hv).1).1, (Finset.mem_filter.mp hv).2⟩
      have hB : ∑ v ∈ B, 1 / ‖realVector v‖ ^ 3 ≤ 125 := by
        apply reciprocal_cube_shell_le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
        intro v hv
        rcases Finset.mem_filter.mp hv with ⟨hvS, hvB⟩
        refine ⟨le_of_not_gt hvB, ?_⟩
        have hh := (hS v hvS).2.le
        simpa [pow_succ, mul_comm] using hh
      have hsplit : (∑ v ∈ A, 1 / ‖realVector v‖ ^ 3) +
          (∑ v ∈ B, 1 / ‖realVector v‖ ^ 3) =
          ∑ v ∈ S, 1 / ‖realVector v‖ ^ 3 := by
        exact Finset.sum_filter_add_sum_filter_not S _ _
      rw [← hsplit]
      push_cast
      linarith

theorem reciprocal_cube_sum_le_logb {R : ℝ} (hR : 1 ≤ R)
    (S : Finset (Fin 3 → ℤ))
    (hS : ∀ v ∈ S, v ≠ 0 ∧ ‖realVector v‖ ≤ R) :
    ∑ v ∈ S, 1 / ‖realVector v‖ ^ 3 ≤
      125 * (Real.logb 2 R + 1) := by
  let m := ⌊Real.logb 2 R⌋₊ + 1
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hlog : 0 ≤ Real.logb 2 R := Real.logb_nonneg (by norm_num) hR
  have hpow : R < (2 : ℝ) ^ m := by
    rw [← Real.rpow_natCast]
    apply (Real.logb_lt_iff_lt_rpow (by norm_num) hRpos).mp
    simpa [m] using Nat.lt_floor_add_one (Real.logb 2 R)
  calc
    ∑ v ∈ S, 1 / ‖realVector v‖ ^ 3 ≤ 125 * (m : ℝ) := by
      apply reciprocal_cube_sum_lt_pow_le
      intro v hv
      exact ⟨one_le_norm_realVector (hS v hv).1, (hS v hv).2.trans_lt hpow⟩
    _ ≤ 125 * (Real.logb 2 R + 1) := by
      have hfloor := Nat.floor_le hlog
      dsimp [m]
      push_cast
      nlinarith

theorem reciprocal_cube_sum_le_log {R : ℝ} (hR : 1 ≤ R)
    (S : Finset (Fin 3 → ℤ))
    (hS : ∀ v ∈ S, v ≠ 0 ∧ ‖realVector v‖ ≤ R) :
    ∑ v ∈ S, 1 / ‖realVector v‖ ^ 3 ≤
      (125 / Real.log 2) * Real.log (2 * R) := by
  calc
    ∑ v ∈ S, 1 / ‖realVector v‖ ^ 3 ≤ 125 * (Real.logb 2 R + 1) :=
      reciprocal_cube_sum_le_logb hR S hS
    _ = (125 / Real.log 2) * Real.log (2 * R) := by
      rw [Real.log_mul (by norm_num) (by linarith : R ≠ 0), Real.logb]
      field_simp
      ring

end Problem355.LatticeBox

end

end OAI
