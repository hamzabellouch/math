import OAI.Geometry.RCD.Harmonic.HomogeneousAffineImprovement

namespace OAI

/-! # Adding the actual Sobolev value limits on a common sequence -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

theorem sobolev_sum_value_convergence {n : ℕ} (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (Ω : ℕ → Set X) (V : ℕ → X → Euclidean n)
    (f g : ℕ → SobolevSpace μ hQ) (F G : Euclidean n → ℝ)
    (hf : ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k),
      |SobolevSpace.toLp μ hQ (f k) x-F (V k x)| ≤ δ)
    (hg : ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k),
      |SobolevSpace.toLp μ hQ (g k) x-G (V k x)| ≤ δ) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k),
      |SobolevSpace.toLp μ hQ (f k+g k) x-(F (V k x)+G (V k x))| ≤ δ := by
  intro δ hδ
  filter_upwards [hf (δ/2) (half_pos hδ),hg (δ/2) (half_pos hδ)] with k hfk hgk
  have hadd : SobolevSpace.toLp μ hQ (f k+g k) =ᵐ[μ]
      fun x => SobolevSpace.toLp μ hQ (f k) x+SobolevSpace.toLp μ hQ (g k) x := by
    rw [map_add]
    exact Lp.coeFn_add _ _
  filter_upwards [hfk,hgk,ae_restrict_of_ae hadd] with x hfx hgx hx
  rw [hx]
  have he : SobolevSpace.toLp μ hQ (f k) x+SobolevSpace.toLp μ hQ (g k) x-
      (F (V k x)+G (V k x)) =
      (SobolevSpace.toLp μ hQ (f k) x-F (V k x))+
        (SobolevSpace.toLp μ hQ (g k) x-G (V k x)) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

end RegularPointCoordinates

end

end OAI
