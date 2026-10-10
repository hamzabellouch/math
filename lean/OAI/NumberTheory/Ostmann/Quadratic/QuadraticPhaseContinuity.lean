import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveQuadraticUniformBound

namespace OAI

/-! # Quantitative continuity of the original quadratic phase parameter -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem realAdditivePhase_sub_norm_le (x y : ℝ) :
    ‖realAdditivePhase x - realAdditivePhase y‖ ≤ 2 * Real.pi * |x - y| := by
  have heq : (realAdditivePhase (x - y) - 1) * realAdditivePhase y =
      realAdditivePhase x - realAdditivePhase y := by
    rw [sub_mul, one_mul, ← realAdditivePhase_add, sub_add_cancel]
  have hh := Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * (x - y))
  rw [mul_comm Complex.I] at hh
  calc
    _ = ‖(realAdditivePhase (x - y) - 1) * realAdditivePhase y‖ := by rw [heq]
    _ = ‖realAdditivePhase (x - y) - 1‖ := by rw [norm_mul, norm_realAdditivePhase, mul_one]
    _ ≤ |2 * Real.pi * (x - y)| := hh
    _ = _ := by rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]

theorem quadraticDensityTerm_phase_sub_bound {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (B : ℝ) (hg : ∀ x, ‖g x‖ ≤ B)
    (a : ZMod q) (θ θ' : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (s w : ℕ)
    (hR : 0 < R) (hv : 0 < v) (hH : 0 ≤ H)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ‖quadraticDensityTerm g a θ Φ R v s w - quadraticDensityTerm g a θ' Φ R v s w‖ ≤
      B * SchwartzMap.seminorm ℝ 0 0 Φ * (2 * Real.pi * H * R * |θ - θ'|) := by
  have hB : 0 ≤ B := (norm_nonneg (g 0)).trans (hg 0)
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  let z : ℝ := (s : ℝ) * v * (w : ℝ) ^ 2 / (R * q)
  by_cases hz : H < z
  · have hzero : Φ ((s : ℝ) * v * (w : ℝ) ^ 2 / (R * q)) = 0 := hΦ z hz
    simp only [quadraticDensityTerm, hzero, mul_zero, sub_self, norm_zero]
    positivity
  have hzH : z ≤ H := le_of_not_gt hz
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have heq (t : ℝ) : realAdditivePhase (t * v * (w : ℝ) ^ 2 / q) ^ s =
      realAdditivePhase (t * (R * z)) := by
    rw [← realAdditivePhase_nat_mul]
    congr 1
    dsimp [z]
    field_simp
  have hphase : ‖realAdditivePhase (θ * (R * z)) - realAdditivePhase (θ' * (R * z))‖ ≤
      2 * Real.pi * H * R * |θ - θ'| := by
    apply (realAdditivePhase_sub_norm_le _ _).trans
    have hdiff : θ * (R * z) - θ' * (R * z) = (θ - θ') * (R * z) := by ring
    rw [hdiff, abs_mul, abs_of_nonneg (mul_nonneg hR.le hz0)]
    have hh := mul_le_mul_of_nonneg_left hzH
      (show 0 ≤ 2 * Real.pi * R * |θ - θ'| by positivity)
    convert hh using 1 <;> ring
  have hdiff : quadraticDensityTerm g a θ Φ R v s w - quadraticDensityTerm g a θ' Φ R v s w =
      g (a * (w : ZMod q) ^ 2 * (s : ZMod q)) *
        (realAdditivePhase (θ * (R * z)) - realAdditivePhase (θ' * (R * z))) * Φ z := by
    simp only [quadraticDensityTerm, heq]
    ring
  rw [hdiff, norm_mul, norm_mul]
  have hh := mul_le_mul (mul_le_mul (hg (a * (w : ZMod q) ^ 2 * (s : ZMod q))) hphase (norm_nonneg _) hB)
    (Φ.norm_le_seminorm ℝ z) (norm_nonneg _) (by positivity)
  exact hh.trans_eq (by ring)

theorem positiveQuadraticSum_phase_sub_bound {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (B : ℝ) (hg : ∀ x, ‖g x‖ ≤ B)
    (a : ZMod q) (θ θ' : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (s : ℕ)
    (hR : 0 < R) (hv : 0 < v) (hH : 0 ≤ H) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ‖positiveQuadraticSum g a θ Φ R v s - positiveQuadraticSum g a θ' Φ R v s‖ ≤
      B * SchwartzMap.seminorm ℝ 0 0 Φ * (2 * Real.pi * H * R * |θ - θ'|) * Real.sqrt H := by
  let Q := Real.sqrt (R * q / ((s : ℝ) * v))
  let W := ⌊Real.sqrt (H * R * q / ((s : ℝ) * v))⌋₊
  let C := B * SchwartzMap.seminorm ℝ 0 0 Φ * (2 * Real.pi * H * R * |θ - θ'|)
  have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hQ : 0 < Q := Real.sqrt_pos.mpr (by positivity)
  have hB : 0 ≤ B := (norm_nonneg (g 0)).trans (hg 0)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hW : (W : ℝ) ≤ Real.sqrt H * Q := by
    apply (Nat.floor_le (Real.sqrt_nonneg _)).trans_eq
    have he : H * R * q / ((s : ℝ) * v) = H * (R * q / ((s : ℝ) * v)) := by ring
    rw [he, Real.sqrt_mul hH]
  rw [positiveQuadraticSum_eq_cutoff g a θ Φ R v H s s hR hv hs le_rfl hΦ,
    positiveQuadraticSum_eq_cutoff g a θ' Φ R v H s s hR hv hs le_rfl hΦ]
  change ‖(Q : ℂ)⁻¹ * (∑ w ∈ Finset.Ioc 0 W, quadraticDensityTerm g a θ Φ R v s w) -
    (Q : ℂ)⁻¹ * (∑ w ∈ Finset.Ioc 0 W, quadraticDensityTerm g a θ' Φ R v s w)‖ ≤ _
  rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hQ]
  have hsum : ‖∑ w ∈ Finset.Ioc 0 W,
      (quadraticDensityTerm g a θ Φ R v s w - quadraticDensityTerm g a θ' Φ R v s w)‖ ≤
      (W : ℝ) * C := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _w ∈ Finset.Ioc 0 W, C := Finset.sum_le_sum (fun w _ =>
        quadraticDensityTerm_phase_sub_bound g B hg a θ θ' Φ R v H s w hR hv hH hΦ)
      _ = _ := by simp
  calc
    _ ≤ Q⁻¹ * ((W : ℝ) * C) := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hQ.le)
    _ ≤ Q⁻¹ * ((Real.sqrt H * Q) * C) := by gcongr
    _ = _ := by dsimp [C]; field_simp

end Ostmann

end OAI
