import OAI.Probability.ContinuumTransition.LowerKac

namespace OAI

section
open scoped Topology BigOperators
open Filter Set
namespace ContinuumTemperature

theorem physical_kac_tendsto {C : NNReal} (hC : LipschitzWith C kernel)
    {t β a : ℝ} (ht : 1 < t) (hβ : 0 < β) (ha : 0 ≤ a)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(a+∑' n, σ n) ≤ (t^2/8)/8)
    (hgap : t*a/2 < (t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/64)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (hbound : ∀ n, σ n ≠ 0 → R n ≤ R₀)
    (h : ℝ) :
    Tendsto (fun q : ℕ =>
      physicalPressure (physicalProfile t (prepend a σ) (prepend (((q : ℝ)/4)^2) R)) t (β,h))
      atTop (𝓝 (quadraticPressure (physicalProfile t σ R) β (t*h) (β*(t*a)/2)/t)) := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro c hc
    have hc' : t*c < quadraticPressure (physicalProfile t σ R) β (t*h) (β*(t*a)/2) := by
      simpa only [mul_comm] using (lt_div_iff₀ ht0).1 hc
    obtain ⟨v, ⟨d, hd, rfl⟩, hv⟩ :=
      exists_lt_of_lt_csSup (show
        ((fun d : ℝ => t*h*d+(β*(t*a)/2)*d^2-canonicalDensity (physicalProfile t σ R) β d) '' Ici 0).Nonempty
        from Set.Nonempty.image _ (nonempty_Ici : (Ici (0 : ℝ)).Nonempty)) hc'
    apply physical_kac_lower_density_eventually hC ht hβ ha hσ hR hs hsmall h hd
    apply (lt_div_iff₀ ht0).2
    nlinarith only [hv]
  · intro c hc
    have he : 0 < (c-quadraticPressure (physicalProfile t σ R) β (t*h) (β*(t*a)/2)/t)/2 := by linarith
    filter_upwards [physical_kac_upper_eventually hC ht hβ ha hσ hR hs hsmall hgap hR₀ hbound h he] with q hq
    linarith

end ContinuumTemperature
end

end OAI
