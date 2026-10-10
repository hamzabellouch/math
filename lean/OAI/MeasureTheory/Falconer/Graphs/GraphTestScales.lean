import OAI.MeasureTheory.Falconer.Graphs.DescriptorGraph

namespace OAI

/-! # The graph widths fit inside the actual parallel tests -/

namespace Falconer

theorem uniform_graph_parallel_width (d : ℕ) {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a g p i : ℕ, a ≤ g → i ≤ J →
      ∀ δ : ℝ, 0 ≤ δ →
      δ ≤ ((2:ℝ)^a/(2:ℝ)^p)*((2:ℝ)^N)^(10*σ) →
      2*((1/(2:ℝ)^p)*((2:ℝ)^N)^(30*σ)) +
        2*δ*(Real.sqrt d*(1/(2:ℝ)^g)) ≤ angularTestWidth N σ J i p := by
  obtain ⟨N₀,h₀⟩ := Regularization.fixed_constant_absorbed
    (by positivity : 0 < 470*σ) (2+2*Real.sqrt d)
  refine ⟨N₀,?_⟩
  intro N hN a g p i hag hi δ _hδ hδbound
  let R := (2:ℝ)^N
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hscale : δ*(1/(2:ℝ)^g) ≤ (1/(2:ℝ)^p)*R^(10*σ) := by
    calc
      _ ≤ (((2:ℝ)^a/(2:ℝ)^p)*R^(10*σ))*(1/(2:ℝ)^g) :=
        mul_le_mul_of_nonneg_right hδbound (by positivity)
      _ ≤ (((2:ℝ)^a/(2:ℝ)^p)*R^(10*σ))*(1/(2:ℝ)^a) :=
        mul_le_mul_of_nonneg_left (dyadic_side_mono hag) (by positivity)
      _ = _ := by field_simp
  have hpowers : R^(10*σ) ≤ R^(30*σ) :=
    Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have hcoefficient : (2+2*Real.sqrt d)*R^(30*σ) ≤ R^(500*σ) := by
    calc
      _ ≤ R^(470*σ)*R^(30*σ) :=
        mul_le_mul_of_nonneg_right (h₀ N hN) (by positivity)
      _ = _ := by rw [← Real.rpow_add hRpos]; congr 1; ring
  calc
    _ = 2*((1/(2:ℝ)^p)*R^(30*σ)) +
        (2*Real.sqrt d)*(δ*(1/(2:ℝ)^g)) := by ring
    _ ≤ 2*((1/(2:ℝ)^p)*R^(30*σ)) +
        (2*Real.sqrt d)*((1/(2:ℝ)^p)*R^(10*σ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hscale
        (by positivity : 0 ≤ 2*Real.sqrt d))
    _ ≤ 2*((1/(2:ℝ)^p)*R^(30*σ)) +
        (2*Real.sqrt d)*((1/(2:ℝ)^p)*R^(30*σ)) := by gcongr
    _ = ((2+2*Real.sqrt d)*R^(30*σ))/(2:ℝ)^p := by ring
    _ ≤ R^(500*σ)/(2:ℝ)^p :=
      div_le_div_of_nonneg_right hcoefficient (by positivity)
    _ ≤ _ := angularTestWidth_lower N σ hJ hi p

end Falconer

end OAI
