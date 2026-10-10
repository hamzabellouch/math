import OAI.NumberTheory.Ostmann.Characters.FactorialContradictionHilbert

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace Ostmann.Characters

theorem factorial_remainder_eventually_le_mass (n : ℕ) {z : ℝ} (hz : 0 < z)
    (R : ℝ → ℝ)
    (hR : Tendsto (fun L => R L / (factorialBulk z L : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ L : ℝ in atTop, R L ≤ factorialMass n (factorialBulk z L) := by
  have hsmall := (tendsto_order.1 hR).2 1 (by norm_num)
  have hpos := (factorialBulk_tendsto hz).eventually (eventually_gt_atTop (0 : ℝ))
  filter_upwards [hsmall, hpos] with L hL hm
  have hR' : R L < (factorialBulk z L : ℝ) := by
    simpa using (div_lt_iff₀ hm).mp hL
  have hr : (1 : ℝ) ≤ 2^(n+1) := one_le_pow₀ (by norm_num)
  exact hR'.le.trans (by
    simpa only [factorialMass, one_mul] using
      mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg (factorialBulk z L)))

theorem exists_depth_factorial_comparison_with_remainders (B BD C ε : ℝ)
    (hε : 60*ε < Real.log 2) (n₀ : ℕ) :
    ∃ n : ℕ, n₀ ≤ n ∧ ∀ (z c α K : ℝ), 0 < z → 0 < c → 0 < α → 0 ≤ K →
      ∀ R S : ℝ → ℝ,
        Tendsto (fun L => R L / (factorialBulk z L : ℝ)) atTop (𝓝 0) →
        Tendsto (fun L => S L / (factorialBulk z L : ℝ)) atTop (𝓝 0) →
        ∀ᶠ L : ℝ in atTop,
          2 * Real.exp ((BD+60*ε*(n+1)) * factorialMass n (factorialBulk z L) + R L) *
            (Real.exp (C * factorialMass n (factorialBulk z L) + S L) /
              (factorialCount n (factorialBulk z L) : ℝ) +
              K * Real.exp (-c*Real.exp (α*L))) <
            Real.exp (-2*B * factorialMass n (factorialBulk z L)) := by
  obtain ⟨n, hn, h⟩ := exists_depth_factorial_comparison B (BD+1) (C+1) ε hε n₀
  refine ⟨n, hn, ?_⟩
  intro z c α K hz hc hα hK R S hR hS
  filter_upwards [h z c α K hz hc hα,
    factorial_remainder_eventually_le_mass n hz R hR,
    factorial_remainder_eventually_le_mass n hz S hS] with L hL hRL hSL
  apply lt_of_le_of_lt _ hL
  have hv : Real.exp ((BD+60*ε*(n+1)) * factorialMass n (factorialBulk z L) + R L) ≤
      Real.exp ((BD+1+60*ε*(n+1)) * factorialMass n (factorialBulk z L)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hd : Real.exp (C * factorialMass n (factorialBulk z L) + S L) ≤
      Real.exp ((C+1) * factorialMass n (factorialBulk z L)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  gcongr

end Ostmann.Characters

end

end OAI
