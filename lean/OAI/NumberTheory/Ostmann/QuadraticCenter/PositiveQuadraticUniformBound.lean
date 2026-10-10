import OAI.NumberTheory.Ostmann.QuadraticCenter.SmallPositiveQuadratic

namespace OAI

/-! # A uniform bound for the positive quadratic series at every kernel -/

namespace Ostmann

open scoped BigOperators SchwartzMap

theorem positiveQuadraticSum_uniform_bound {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (B : ℝ) (hg : ∀ x, ‖g x‖ ≤ B)
    (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (s : ℕ)
    (hR : 0 < R) (hv : 0 < v) (hH : 0 ≤ H) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ‖positiveQuadraticSum g a θ Φ R v s‖ ≤
      B * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H := by
  let Q := Real.sqrt (R * q / ((s : ℝ) * v))
  let W := ⌊Real.sqrt (H * R * q / ((s : ℝ) * v))⌋₊
  have hqR : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hQ : 0 < Q := Real.sqrt_pos.mpr (by positivity)
  have hB : 0 ≤ B := (norm_nonneg (g 0)).trans (hg 0)
  have hΦ0 : 0 ≤ SchwartzMap.seminorm ℝ 0 0 Φ := by positivity
  have hW : (W : ℝ) ≤ Real.sqrt H * Q := by
    apply (Nat.floor_le (Real.sqrt_nonneg _)).trans_eq
    have he : H * R * q / ((s : ℝ) * v) = H * (R * q / ((s : ℝ) * v)) := by ring
    rw [he, Real.sqrt_mul hH]
  rw [positiveQuadraticSum_eq_cutoff g a θ Φ R v H s s hR hv hs le_rfl hΦ]
  change ‖(Q : ℂ)⁻¹ * ∑ w ∈ Finset.Ioc 0 W, quadraticDensityTerm g a θ Φ R v s w‖ ≤ _
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ]
  have hsum : ‖∑ w ∈ Finset.Ioc 0 W, quadraticDensityTerm g a θ Φ R v s w‖ ≤
      (W : ℝ) * (B * SchwartzMap.seminorm ℝ 0 0 Φ) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _w ∈ Finset.Ioc 0 W, B * SchwartzMap.seminorm ℝ 0 0 Φ := by
        apply Finset.sum_le_sum
        intro w _
        simp only [quadraticDensityTerm, norm_mul, norm_pow, norm_realAdditivePhase,
          one_pow, mul_one]
        exact mul_le_mul (hg _) (Φ.norm_le_seminorm ℝ _) (norm_nonneg _) hB
      _ = _ := by simp
  calc
    _ ≤ Q⁻¹ * ((W : ℝ) * (B * SchwartzMap.seminorm ℝ 0 0 Φ)) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hQ.le)
    _ ≤ Q⁻¹ * ((Real.sqrt H * Q) * (B * SchwartzMap.seminorm ℝ 0 0 Φ)) := by gcongr
    _ = _ := by field_simp

theorem positiveQuadraticSum_energy_uniform_bound {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (hg : (∑ x : ZMod q, ‖g x‖ ^ 2) ≤ q)
    (a : ZMod q) (θ : ℝ) (Φ : 𝓢(ℝ, ℂ)) (R v H : ℝ) (s : ℕ)
    (hR : 0 < R) (hv : 0 < v) (hH : 0 ≤ H) (hs : 0 < s)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ‖positiveQuadraticSum g a θ Φ R v s‖ ≤
      Real.sqrt q * SchwartzMap.seminorm ℝ 0 0 Φ * Real.sqrt H := by
  apply positiveQuadraticSum_uniform_bound g (Real.sqrt q) _ a θ Φ R v H s hR hv hH hs hΦ
  intro x
  apply Real.le_sqrt_of_sq_le
  exact (Finset.single_le_sum (fun y _ => sq_nonneg ‖g y‖) (Finset.mem_univ x)).trans hg

end Ostmann

end OAI
