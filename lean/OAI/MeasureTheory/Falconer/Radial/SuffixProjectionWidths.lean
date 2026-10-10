import OAI.MeasureTheory.Falconer.Angular.AngularWidths

namespace OAI

namespace PlanarFalconer

theorem sourceAngularWidth_lower (N : ℕ) (sig : ℝ) {J i : ℕ}
    (hJ : 0 < J) (hi : i ≤ J) (u : ℕ) :
    ((2:ℝ)^N)^(1000*sig)/(2:ℝ)^u ≤ sourceAngularWidth N sig J i u := by
  have hj : 0 < (J:ℝ) := by exact_mod_cast hJ
  have hir : (i:ℝ) ≤ (J:ℝ) := by exact_mod_cast hi
  have hcoeff : 1 ≤ 2-(i:ℝ)/(J:ℝ) := by
    have := (div_le_one hj).mpr hir
    linarith
  unfold sourceAngularWidth
  calc
    _ = (1/(2:ℝ)^u)*((2:ℝ)^N)^(1000*sig) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hcoeff (by positivity)) (by positivity)

theorem uniform_suffix_projection_gap {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) (C K : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ p u : ℕ, p ≤ u → ∀ i ≤ J,
      K/(2:ℝ)^u+4/(2:ℝ)^u+(2/(2:ℝ)^p)*(C/(2:ℝ)^(u-p)) ≤
        sourceAngularWidth N sig J i u := by
  obtain ⟨N₀,hN₀⟩ := fixed_constant_absorbed (by positivity : 0 < 1000*sig) (K+4+2*C)
  refine ⟨N₀,?_⟩
  intro N hN p u hpu i hi
  have hp : (2:ℝ)^p*(2:ℝ)^(u-p) = (2:ℝ)^u := by
    rw [← pow_add,Nat.add_sub_of_le hpu]
  calc
    _ = (K+4+2*C)/(2:ℝ)^u := by
      rw [div_mul_div_comm, hp]
      ring
    _ ≤ ((2:ℝ)^N)^(1000*sig)/(2:ℝ)^u :=
      div_le_div_of_nonneg_right (hN₀ N hN) (by positivity)
    _ ≤ _ := sourceAngularWidth_lower N sig hJ hi u

end PlanarFalconer

end OAI
