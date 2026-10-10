import OAI.Geometry.RCD.Heat.LipschitzTimePairing

namespace OAI

/-! # The time derivative in the compact Hamilton--Jacobi pairing

The original pairing need only be Lipschitz on the open interval. A
Lipschitz extension defines its endpoint values; the zero boundary time
test removes those values from integration by parts.
-/

open Set Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem compact_time_pairing_derivative_identity
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) {Ω : Set X} (hΩ : IsCompact Ω) (H : ℝ → X → ℝ)
    {a b : ℝ} (hab : a ≤ b) {L : ℝ≥0}
    (hH : LipschitzOnWith L (Function.uncurry H) (Ioo a b ×ˢ Ω))
    (φ : X → ℝ) (hφ : IntegrableOn φ Ω μ)
    (θ θ' : ℝ → ℝ) {A : ℝ≥0} (hθ : LipschitzOnWith A θ (Icc a b))
    (hder : ∀ t ∈ Ioo a b, HasDerivAt θ (θ' t) t)
    (hθa : θ a = 0) (hθb : θ b = 0) :
    -(∫ t in Ioo a b, θ' t*(∫ x in Ω, φ x*H t x ∂μ)) =
      ∫ t in Ioo a b, θ t*deriv (fun s => ∫ x in Ω, φ x*H s x ∂μ) t := by
  let P := fun t => ∫ x in Ω, φ x*H t x ∂μ
  obtain ⟨V,hV,he⟩ := (compact_set_pairing_lipschitz μ hΩ H hH φ hφ).extend_real
  have hv : LipschitzOnWith
      ⟨(L:ℝ)*(∫ x in Ω, |φ x| ∂μ),mul_nonneg L.coe_nonneg
        (integral_nonneg fun x => abs_nonneg (φ x))⟩ V (Icc a b) := hV.lipschitzOnWith
  have hd (t : ℝ) (ht : t ∈ Ioo a b) : deriv V t = deriv P t := by
    have heq : V =ᶠ[𝓝 t] P := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact (he hs).symm
    exact heq.deriv_eq
  have hb := lipschitz_time_pairing_integration_by_parts V θ θ' hab hv hθ hder hθa hθb
  have heP : (∫ t in Ioo a b, θ' t*V t) = ∫ t in Ioo a b, θ' t*P t := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    change θ' t*V t = θ' t*P t
    rw [← he ht]
  have heD : (∫ t in Ioo a b, θ t*deriv V t) = ∫ t in Ioo a b, θ t*deriv P t := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    change θ t*deriv V t = θ t*deriv P t
    rw [hd t ht]
  simpa only [heP,heD] using hb

end RegularPointCoordinates

end

end OAI
