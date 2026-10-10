import OAI.MeasureTheory.Falconer.Shells.HighShellCoefficientBounds

namespace OAI

namespace PlanarFalconer

theorem high_shell_radial_power_bound {v r : ℝ} (hr : (2:ℝ)^(v-1) ≤ r) (j : ℕ) :
    0 ≤ ((r/(2:ℝ)^v)⁻¹)^j ∧ ((r/(2:ℝ)^v)⁻¹)^j ≤ (2:ℝ)^j := by
  have hrpos : 0 < r := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hr
  have hd : (1/2:ℝ) ≤ r/(2:ℝ)^v := by
    apply (le_div_iff₀ (by positivity)).mpr
    have he : (1/2:ℝ)*(2:ℝ)^v = (2:ℝ)^(v-1) := by
      rw [Real.rpow_sub (by norm_num : (0:ℝ) < 2),Real.rpow_one]
      ring
    rw [he]
    exact hr
  have hi : (r/(2:ℝ)^v)⁻¹ ≤ 2 := by
    simpa only [one_div, inv_inv] using inv_anti₀ (by norm_num : (0:ℝ) < 1/2) hd
  exact ⟨pow_nonneg (by positivity) _,pow_le_pow_left₀ (by positivity) hi j⟩

theorem uniform_minimal_inverseLeibniz_subpower {eps : ℝ} (heps : 0 < eps) (j : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : ℕ → ℝ) (q a t : ℕ), 0 < q →
    ((inverseLeibnizTerms j (pairMaskIndices (policyDescriptorList A N q a t))).map
      (fun b => ‖b.1‖)).sum * (2:ℝ)^j ≤ ((2:ℝ)^N)^eps := by
  let C := (inverseStationaryExpr j).cost * (2:ℝ)^(2*j) * (2:ℝ)^j
  obtain ⟨N₁,h₁⟩ := fixed_constant_absorbed (half_pos heps) C
  obtain ⟨N₂,h₂⟩ := fixed_polynomial_subpower (6*j) (half_pos heps)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN A q a t hq
  have hpoly : (((N:ℝ)+1)^3)^(2*j) = ((N:ℝ)+1)^(6*j) := by
    rw [← pow_mul]
    congr 1
    omega
  have hbound := mul_le_mul_of_nonneg_right (minimal_inverseLeibniz_cost A (N := N) (a := a) (t := t) hq j)
    (by positivity : 0 ≤ (2:ℝ)^j)
  apply hbound.trans
  calc
    _ = C*((N:ℝ)+1)^(6*j) := by rw [mul_pow,hpoly]; dsimp [C]; ring
    _ ≤ C*(4*(N:ℝ)+1)^(6*j) := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by have := Nat.cast_nonneg (α := ℝ) N; linarith) _)
      (by dsimp [C]; exact mul_nonneg (mul_nonneg (inverseStationaryExpr j).cost_nonneg (by positivity)) (by positivity))
    _ ≤ ((2:ℝ)^N)^(eps/2)*((2:ℝ)^N)^(eps/2) :=
      mul_le_mul (h₁ N ((le_max_left _ _).trans hN)) (h₂ N ((le_max_right _ _).trans hN))
        (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end PlanarFalconer

end OAI
