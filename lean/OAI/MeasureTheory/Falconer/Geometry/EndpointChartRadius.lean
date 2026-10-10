import OAI.MeasureTheory.Falconer.Slicing.SmallGaussianChart

namespace OAI

/-! # A fixed small cap for the three-dimensional endpoint slice -/

namespace Falconer

theorem exists_endpoint_chart_radius (h : ℕ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1/8 ∧ (h:ℝ)*((h+3:ℝ)*(2*ρ)) ≤ 1/2 := by
  obtain ⟨r,hr,_,hst,_⟩ := exists_small_gaussian_chart_radius (h+1)
  have hcast : ((h+1:ℕ):ℝ)+2 = (h+3:ℝ) := by push_cast; ring
  rw [hcast] at hst
  refine ⟨min r (1/8),lt_min hr (by norm_num),min_le_right _ _,?_⟩
  have hh : (h:ℝ)*((h+3:ℝ)*(2*r)) ≤ ((h+1:ℕ):ℝ)*((h+3:ℝ)*(2*r)) :=
    mul_le_mul_of_nonneg_right (by push_cast; linarith) (by positivity)
  apply le_trans _ (hh.trans hst)
  gcongr
  exact min_le_left _ _

end Falconer

end OAI
