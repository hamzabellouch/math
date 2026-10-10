import OAI.NumberTheory.Ostmann.Characters.FactorialContradictionDecay

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace Ostmann.Characters

theorem factorial_diagonal_bound (n m : ℕ) {B v C : ℝ}
    (hdepth : v + C + 2*B + 2 ≤ (n : ℝ)*Real.log 2 - 1) :
    Real.exp (v * factorialMass n m) *
        (Real.exp (C * factorialMass n m) / (factorialCount n m : ℝ)) ≤
      Real.exp (-(2*B+2) * factorialMass n m) := by
  let M := factorialMass n m
  let q := (n : ℝ)*Real.log 2 - 1
  have hM : 0 ≤ M := factorialMass_nonneg n m
  calc
    _ ≤ Real.exp (v*M) * (Real.exp (C*M) / Real.exp (M*q)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      exact div_le_div_of_nonneg_left (Real.exp_nonneg _) (Real.exp_pos _)
        (exp_le_factorialCount n m)
    _ = Real.exp ((v+C-q)*M) := by
      rw [← Real.exp_sub, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right hdepth hM
      dsimp [q] at *
      nlinarith

theorem factorial_comparison_eventually_lt (n : ℕ) (B v C K : ℝ)
    {z c α : ℝ} (hz : 0 < z) (hc : 0 < c) (hα : 0 < α)
    (hdepth : v + C + 2*B + 2 ≤ (n : ℝ)*Real.log 2 - 1) :
    ∀ᶠ L : ℝ in atTop,
      2 * Real.exp (v * factorialMass n (factorialBulk z L)) *
        (Real.exp (C * factorialMass n (factorialBulk z L)) /
          (factorialCount n (factorialBulk z L) : ℝ) +
          K * Real.exp (-c * Real.exp (α * L))) <
      Real.exp (-2*B * factorialMass n (factorialBulk z L)) := by
  have hd : Tendsto (fun L : ℝ => Real.exp (-2 * factorialMass n (factorialBulk z L)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        ((factorialMass_tendsto n hz).const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have he := factorial_error_tendsto_zero n (v+2*B) hz hc hα
  have hlim := (hd.const_mul 2).add (he.const_mul (2*K))
  simp only [mul_zero, add_zero] at hlim
  have hsmall := (tendsto_order.1 hlim).2 1 (by norm_num)
  filter_upwards [hsmall] with L hL
  let m := factorialBulk z L
  let M := factorialMass n m
  have hdiag := factorial_diagonal_bound n m hdepth
  have heq₁ : Real.exp (-(2*B+2)*M) =
      Real.exp (-2*B*M) * Real.exp (-2*M) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have heq₂ : Real.exp (v*M) * Real.exp (-c * Real.exp (α*L)) =
      Real.exp (-2*B*M) * Real.exp ((v+2*B)*M-c*Real.exp (α*L)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = 2 * (Real.exp (v*M) * (Real.exp (C*M) / (factorialCount n m : ℝ))) +
        2*K*(Real.exp (v*M) * Real.exp (-c*Real.exp (α*L))) := by ring
    _ ≤ 2 * Real.exp (-(2*B+2)*M) +
        2*K*(Real.exp (v*M) * Real.exp (-c*Real.exp (α*L))) := by
      gcongr
    _ = Real.exp (-2*B*M) *
        (2*Real.exp (-2*M) + 2*K*Real.exp ((v+2*B)*M-c*Real.exp (α*L))) := by
      rw [heq₁, heq₂]
      ring
    _ < _ := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left hL (Real.exp_pos (-2*B*M))

theorem exists_depth_factorial_comparison (B BD C ε : ℝ)
    (hε : 60*ε < Real.log 2) (n₀ : ℕ) :
    ∃ n : ℕ, n₀ ≤ n ∧ ∀ (z c α K : ℝ), 0 < z → 0 < c → 0 < α →
      ∀ᶠ L : ℝ in atTop,
        2 * Real.exp ((BD+60*ε*(n+1)) * factorialMass n (factorialBulk z L)) *
          (Real.exp (C * factorialMass n (factorialBulk z L)) /
            (factorialCount n (factorialBulk z L) : ℝ) +
            K * Real.exp (-c*Real.exp (α*L))) <
          Real.exp (-2*B * factorialMass n (factorialBulk z L)) := by
  obtain ⟨n, hn, hdepth⟩ := exists_factorial_depth B BD C ε hε n₀
  refine ⟨n, hn, ?_⟩
  intro z c α K hz hc hα
  exact factorial_comparison_eventually_lt n B (BD+60*ε*(n+1)) C K hz hc hα hdepth

end Ostmann.Characters

end

end OAI
