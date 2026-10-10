import OAI.Geometry.RCD.Transport.GlobalRenyiMidpoint

namespace OAI

/-! # Maximal Rényi midpoints on a finite dyadic tree

These predicates record the actual variational choices of the construction.
The reference is always the original measure, independent of support balls.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
attribute [local instance] pathBorel pathBorelSpace

def RenyiMidpointMaximal (μ : Measure X) (q : ℝ) (ν₀ νm ν₁ : Measure X) : Prop :=
  ∀ κ : Measure C(Time,X), IsProbabilityMeasure κ →
    (∀ᵐ γ ∂κ, IsGeodesic γ) → IsOptimalCoupling ν₀ ν₁ (κ.map (fun γ => (γ 0,γ 1))) →
    (∫ x, ((κ.map (fun γ => γ midpointTime)).rnDeriv μ x).toReal^q ∂μ) ≤
      ∫ x, (νm.rnDeriv μ x).toReal^q ∂μ

def RenyiDyadicMaximal (μ : Measure X) (q : ℝ) (ν : Time → Measure X) : ℕ → Prop
  | 0 => True
  | m+1 => RenyiMidpointMaximal μ q (ν 0) (ν midpointTime) (ν 1) ∧
      RenyiDyadicMaximal μ q (fun t => ν (lowerTime t)) m ∧
      RenyiDyadicMaximal μ q (fun t => ν (upperTime t)) m

theorem RenyiDyadicMaximal.congr {μ : Measure X} {q : ℝ} {ν η : Time → Measure X}
    {m : ℕ} (h : RenyiDyadicMaximal μ q ν m) (he : ∀ t, ν t=η t) :
    RenyiDyadicMaximal μ q η m := by
  have hf := funext he
  rwa [←hf]

end RegularPointCoordinates

end

end OAI
