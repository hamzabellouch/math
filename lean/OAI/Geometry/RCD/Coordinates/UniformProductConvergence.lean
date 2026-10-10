import OAI.Geometry.RCD.Coordinates.NormalizedUniformMean

namespace OAI

/-! # Products preserve uniform almost-everywhere convergence with bounded limits -/

open Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem ae_uniform_product_convergence (μ : ℕ → Measure X)
    (u w f g : ℕ → X → ℝ) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hf : ∀ k, ∀ᵐ x ∂μ k, |f k x|≤A) (hg : ∀ k, ∀ᵐ x ∂μ k, |g k x|≤B)
    (hu : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ᵐ x ∂μ k, |u k x-f k x|≤η)
    (hw : ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ᵐ x ∂μ k, |w k x-g k x|≤η) :
    ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ᵐ x ∂μ k, |u k x*w k x-f k x*g k x|≤η := by
  intro η hη
  let δ := min 1 (η/(A+B+1))
  have hC : 0<A+B+1 := by linarith
  have hδ : 0<δ := lt_min zero_lt_one (div_pos hη hC)
  have hδ1 : δ≤1 := min_le_left _ _
  have hδC : δ*(A+B+1)≤η := (le_div_iff₀ hC).mp (min_le_right _ _)
  filter_upwards [hu δ hδ,hw δ hδ] with k huk hwk
  filter_upwards [huk,hwk,hf k,hg k] with x hux hwx hfx hgx
  have hwb : |w k x|≤B+1 := by
    have ht := abs_add_le (w k x-g k x) (g k x)
    simp only [sub_add_cancel] at ht
    linarith
  have he : u k x*w k x-f k x*g k x=
      (u k x-f k x)*w k x+f k x*(w k x-g k x) := by ring
  rw [he]
  calc
    _ ≤ |(u k x-f k x)*w k x|+|f k x*(w k x-g k x)| := abs_add_le _ _
    _ = |u k x-f k x| * |w k x|+|f k x| * |w k x-g k x| := by rw [abs_mul,abs_mul]
    _ ≤ δ*(B+1)+A*δ := by
      gcongr
    _ = δ*(A+B+1) := by ring
    _ ≤ η := hδC

end RegularPointCoordinates

end

end OAI
