import OAI.MeasureTheory.Falconer.Recursion.RelativeScaleBudget
import OAI.MeasureTheory.Falconer.Radial.RadialCollisionWidths

namespace OAI

/-! # Fixed normalization and collision widths for the three-interval argument -/

namespace Falconer

noncomputable def cellContraction (d : ℕ) : ℝ := 1/(4*(Real.sqrt d+1))

theorem cellContraction_pos (d : ℕ) : 0 < cellContraction d := by
  unfold cellContraction
  positivity

theorem cellContraction_le_one (d : ℕ) : cellContraction d ≤ 1 := by
  unfold cellContraction
  apply (div_le_one (by positivity)).mpr
  nlinarith [Real.sqrt_nonneg (d:ℝ)]

theorem cellContraction_sqrt (d : ℕ) : cellContraction d*Real.sqrt d ≤ 1/4 := by
  unfold cellContraction
  rw [one_div,mul_comm,← div_eq_mul_inv]
  apply (div_le_iff₀ (by positivity : 0 < 4*(Real.sqrt (d:ℝ)+1))).mpr
  ring_nf
  linarith

theorem dyadic_collision_width (d : ℕ) {s C : ℝ} (hs : 0 < s)
    (hC : 4*Real.sqrt d/s+2 ≤ C) {v N : ℕ} (hvN : v ≤ N) :
    2*(Real.sqrt d*(1/(2:ℝ)^v))/(s/2)+2*(1/(2:ℝ)^N) ≤ C/(2:ℝ)^v := by
  have hδ : 1/(2:ℝ)^N ≤ 1/(2:ℝ)^v :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hvN)
  have he : 2*(Real.sqrt d*(1/(2:ℝ)^v))/(s/2) =
      (4*Real.sqrt d/s)*(1/(2:ℝ)^v) := by
    field_simp
    ring
  rw [he]
  calc
    _ ≤ (4*Real.sqrt d/s)*(1/(2:ℝ)^v)+2*(1/(2:ℝ)^v) := by linarith
    _ = (4*Real.sqrt d/s+2)/(2:ℝ)^v := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hC (by positivity)

theorem eventually_cell_diameter_small (d : ℕ) {γ s : ℝ}
    (hγ : 0 < γ) (hs : 0 < s) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n : ℕ, γ*(N:ℝ) ≤ n →
      Real.sqrt d/(2:ℝ)^n ≤ s/2 := by
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hγ (2*Real.sqrt d/s)
  refine ⟨N₀,fun N hN n hn => ?_⟩
  have hh : 2*Real.sqrt d/s ≤ (2:ℝ)^n := by
    apply (hN₀ N hN).trans
    have hb : (N:ℝ)*γ ≤ (n:ℝ)*1 := by nlinarith
    simpa only [Real.rpow_one] using dyadic_relative_scale_bound N n hb
  have hh' := (div_le_iff₀ hs).mp hh
  apply (div_le_iff₀ (by positivity : 0 < (2:ℝ)^n)).mpr
  nlinarith

end Falconer

end OAI
