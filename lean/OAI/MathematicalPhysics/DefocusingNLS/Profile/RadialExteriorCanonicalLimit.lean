import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorCanonical
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorOutgoingContinuation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialParameterSubsequence

namespace OAI

/-! Actual H convergence for the uniquely selected outgoing exterior solution. -/

open Set Filter
namespace DefocusingNLS

theorem radialExteriorCanonical_H_limit (ν m : ℕ → ℂ) (q m₀ : ℂ)
    (hq : -1 < q.re) (hν : Tendsto ν atTop (nhds (-2*q)))
    (hm : Tendsto m atTop (nhds m₀)) (δ ρ l : ℝ)
    (hδ : 0 < δ) (hδm : δ < ‖m₀‖) (hsmall : ‖m₀‖+2*δ < 1) (hρ : ρ < 1)
    (hupper : ∀ t, l ≤ t → ‖(radialFreeSlowJet q m₀ t).1‖+2*δ ≤ ρ)
    (hlower : ∀ t, l ≤ t → δ < ‖(radialFreeSlowJet q m₀ t).1‖) :
    (∀ᶠ n in atTop, HasRadialExterior (ν n) n (m n) l) ∧
      TendstoUniformlyOn (fun n => radialExteriorCanonical (ν n) n (m n) l)
        (radialFreeSlowJet q m₀) atTop (Ici l) := by
  obtain ⟨Z,hconv,hc,he,hd⟩ := exists_radialExterior_outgoing_extended ν m q m₀
    hq hν hm δ ρ l hδ hδm hsmall hρ hupper hlower
  have hcanon : ∀ᶠ n in atTop, ∀ t, l ≤ t →
      radialExteriorCanonical (ν n) n (m n) l t=Z n t := by
    filter_upwards [he,hd] with n hen hdn t ht
    exact radialExteriorCanonical_eq (Z n) (hc n) hen hdn t ht
  refine ⟨?_,?_⟩
  · filter_upwards [he,hd] with n hen hdn
    exact ⟨Z n,hc n,hen,hdn⟩
  · rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
    intro ε hε
    filter_upwards [hconv ε hε,hcanon] with n hn hcn t ht
    rw [hcn t ht]
    exact hn t ht

theorem radialExteriorCanonical_H_limit_subsequence
    (s : ℕ → ℕ) (hs : StrictMono s) (ν m : ℕ → ℂ) (q m₀ : ℂ)
    (hq : -1 < q.re) (hν : Tendsto ν atTop (nhds (-2*q)))
    (hm : Tendsto m atTop (nhds m₀)) (δ ρ l : ℝ)
    (hδ : 0 < δ) (hδm : δ < ‖m₀‖) (hsmall : ‖m₀‖+2*δ < 1) (hρ : ρ < 1)
    (hupper : ∀ t, l ≤ t → ‖(radialFreeSlowJet q m₀ t).1‖+2*δ ≤ ρ)
    (hlower : ∀ t, l ≤ t → δ < ‖(radialFreeSlowJet q m₀ t).1‖) :
    (∀ᶠ i in atTop, HasRadialExterior (ν i) (s i) (m i) l) ∧
      TendstoUniformlyOn (fun i => radialExteriorCanonical (ν i) (s i) (m i) l)
        (radialFreeSlowJet q m₀) atTop (Ici l) := by
  obtain ⟨he,hconv⟩ := radialExteriorCanonical_H_limit
    (radialParameterExtension s ν (-2*q)) (radialParameterExtension s m m₀) q m₀ hq
    (radialParameterExtension_tendsto s hs ν (-2*q) hν)
    (radialParameterExtension_tendsto s hs m m₀ hm) δ ρ l hδ hδm hsmall hρ hupper hlower
  refine ⟨?_,?_⟩
  · simpa only [radialParameterExtension_apply s hs] using hs.tendsto_atTop.eventually he
  · rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
    intro ε hε
    simpa only [radialParameterExtension_apply s hs] using
      hs.tendsto_atTop.eventually (hconv ε hε)

end DefocusingNLS

end OAI
