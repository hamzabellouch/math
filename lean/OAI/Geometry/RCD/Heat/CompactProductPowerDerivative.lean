import OAI.Geometry.RCD.Sobolev.CompactIntegralDerivative
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace OAI

/-! # Compact power integration for two scalar differentiable families -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

theorem compact_product_power_hasDerivAt {a b t : ℝ} (ht : t ∈ Ioo a b)
    {Ω : Set X} (hΩ : IsCompact Ω) (F G dF dG : ℝ → X → ℝ)
    (hF : ContinuousOn (Function.uncurry F) (Icc a b ×ˢ Ω))
    (hG : ContinuousOn (Function.uncurry G) (Icc a b ×ˢ Ω))
    (hdF : ContinuousOn (Function.uncurry dF) (Icc a b ×ˢ Ω))
    (hdG : ContinuousOn (Function.uncurry dG) (Icc a b ×ˢ Ω))
    (hderF : ∀ s ∈ Ioo a b, ∀ x ∈ Ω, HasDerivAt (fun r => F r x) (dF s x) s)
    (hderG : ∀ s ∈ Ioo a b, ∀ x ∈ Ω, HasDerivAt (fun r => G r x) (dG s x) s)
    (q : ℕ) :
    HasDerivAt (fun s => ∫ x in Ω, (F s x*G s x)^q ∂μ)
      ((q:ℝ)*(∫ x in Ω, (F t x*G t x)^(q-1)*(dF t x*G t x+F t x*dG t x) ∂μ)) t := by
  have hc : ContinuousOn (Function.uncurry (fun s x => (F s x*G s x)^q))
      (Icc a b ×ˢ Ω) := (hF.mul hG).pow q
  have hdc : ContinuousOn (Function.uncurry (fun s x =>
      (q:ℝ)*(F s x*G s x)^(q-1)*(dF s x*G s x+F s x*dG s x)))
      (Icc a b ×ˢ Ω) :=
    (continuousOn_const.mul ((hF.mul hG).pow (q-1))).mul ((hdF.mul hG).add (hF.mul hdG))
  have hd := compact_integral_hasDerivAt (μ := μ) ht hΩ _ _ hc hdc (by
    intro s hs x hx
    exact ((hderF s hs x hx).mul (hderG s hs x hx)).pow q)
  simpa only [mul_assoc,integral_const_mul] using hd

end RegularPointCoordinates

end

end OAI
