import OAI.NumberTheory.EgyptianFractions.MinorArcLogWindow
import OAI.NumberTheory.EgyptianFractions.VaughanEstimate

namespace OAI
noncomputable section
open Filter
open scoped ArithmeticFunction

namespace Problem337.MinorArc

/-- Actual von Mangoldt cancellation outside the logarithmic major arcs.
Both the rational approximation and the Vaughan estimate are discharged. -/
theorem eventually_vonMangoldt_minor_arc_bound (D : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
      θ ∉ ThreePrimeAnalysis.majorArcUnion
        ⌊Real.log N ^ (2 * (4 + D + 2))⌋₊
        (2 * Real.log N ^ (2 * (4 + D + 2)) / N) →
      ‖Vaughan.weightedSum (Finset.Ioc 0 N)
        (fun k => VaughanBilinear.phase (θ * k)) Λ‖ ≤
        (N : ℝ) / Real.log N ^ D := by
  have hgeom := (tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually
    (eventually_minor_fraction_with_vaughan_budget 4 D 16200 (by norm_num))
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hgeom, hlog, Vaughan.eventually_vonMangoldt_sum_log_bound]
    with N hgeom hlog hvaughan
  intro θ hθ hminor
  obtain ⟨a, q, hlow, hupp, hq, hcop, happ, hbudget⟩ := hgeom θ hθ hminor
  have hqNr : (q : ℝ) ≤ N := hupp.trans
    (div_le_self (Nat.cast_nonneg N) (one_le_pow₀ hlog))
  have hqN : q ≤ N := by exact_mod_cast hqNr
  calc
    _ ≤ 16200 * Real.log N ^ 4 * Vaughan.approximationEnvelope N q :=
      hvaughan θ a q hq hcop happ hqN
    _ = 16200 * ((N : ℝ) / Real.sqrt q + (N : ℝ) ^ (4 / 5 : ℝ) +
        Real.sqrt ((N : ℝ) * q)) * Real.log N ^ 4 := by
      rw [Vaughan.approximationEnvelope]
      ring
    _ ≤ _ := hbudget

end Problem337.MinorArc

end

end OAI
