import OAI.Geometry.RCD.Coordinates.VanishingDiagonalCost
import Mathlib.MeasureTheory.Integral.Average

namespace OAI

/-! # Simultaneous diagonal and sample choice for vanishing mean costs -/

open Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem diagonal_mean_selection {A : Type*} [MeasurableSpace A]
    (μ : ℕ → ℕ → Measure A) [∀ m k, IsProbabilityMeasure (μ m k)]
    (f : ℕ → ℕ → A → ℝ) (P : ℕ → ℕ → A → Prop)
    (hf : ∀ m k, Integrable (f m k) (μ m k))
    (hpos : ∀ m k a, 0 ≤ f m k a)
    (hP : ∀ m k, ∀ᵐ a ∂μ m k, P m k a)
    (hlim : ∀ m, Tendsto (fun k => ∫ a, f m k a ∂μ m k) atTop (𝓝 0)) :
    ∃ (d : ℕ → ℕ) (a : ℕ → A), Tendsto d atTop atTop ∧
      (∀ k, P (d k) k (a k)) ∧
      Tendsto (fun k => f (d k) k (a k)) atTop (𝓝 0) := by
  obtain ⟨d,hd,hcost⟩ := exists_vanishing_diagonal_cost
    (fun m k => ∫ a, f m k a ∂μ m k)
    (fun m k => integral_nonneg (hpos m k)) hlim
  have hex (k : ℕ) : ∃ a, P (d k) k a ∧ f (d k) k a ≤ ∫ z, f (d k) k z ∂μ (d k) k := by
    obtain ⟨a,ha,hb⟩ := exists_notMem_null_le_integral (hf (d k) k) (ae_iff.mp (hP (d k) k))
    exact ⟨a,of_not_not ha,hb⟩
  choose a hPa ha using hex
  exact ⟨d,a,hd,hPa,squeeze_zero (fun k => hpos (d k) k (a k)) ha hcost⟩

end RegularPointCoordinates

end

end OAI
