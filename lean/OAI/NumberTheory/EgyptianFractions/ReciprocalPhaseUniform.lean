import OAI.NumberTheory.EgyptianFractions.ReciprocalPhaseCancellation
import OAI.NumberTheory.EgyptianFractions.FinitePowerSaving

namespace OAI
noncomputable section
open scoped BigOperators Topology
open Filter
namespace Problem337

/-- The terminal estimate needed at one fixed differencing order. -/
def ReciprocalTerminalPowerBound (k : ℕ) (C U : ℝ) : Prop :=
  ∀ Z : ℝ,
    U ^ (-(3 : ℝ) / 2) ≤ |Z| * U ^ (-((k : ℝ) + 1)) →
    |Z| * U ^ (-((k : ℝ) + 1)) ≤ U ^ (-(1 : ℝ) / 2) →
    ∀ L R : ℤ, U ≤ (L : ℝ) → (R : ℝ) ≤ 2 * U →
    ∀ hs : List ℤ, hs.length = k - 2 →
      (∀ h ∈ hs, 0 < h ∧ h < (Nat.floor (U ^ (1 / (10 * (k : ℝ)))) : ℤ)) →
      ‖∑ n ∈ Finset.Icc L (R - hs.sum),
        differencingPhase (forwardDifference (hs.map (fun h : ℤ => (h : ℝ)))
          (fun x => Z / x) n)‖ ≤ C * U ^ ((4 : ℝ) / 5)

/-- For a bounded range of reciprocal-phase numerators, fixed-order terminal
estimates give one positive power saving uniformly in the numerator and interval.
All analytic hypotheses are confined to the explicit terminal estimate. -/
theorem reciprocal_phase_uniform_of_terminal
    (hterminal : ∀ k : ℕ, 4 ≤ k → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ U : ℝ in atTop, ReciprocalTerminalPowerBound k C U)
    (B : ℝ) (hB : 4 ≤ B) :
    ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧
      ∀ᶠ U : ℝ in atTop, ∀ (Z : ℝ) (L R : ℤ),
        U ^ (4 : ℕ) ≤ |Z| → |Z| ≤ U ^ B →
        U ≤ (L : ℝ) → (R : ℝ) ≤ 2 * U →
        ‖∑ n ∈ Finset.Icc L R, differencingPhase (Z / (n : ℝ))‖ ≤
          A * U ^ (1 - δ) := by
  let F : ℕ → ℝ → (ℝ × ℤ × ℤ) → ℝ := fun _ _ z =>
    ‖∑ n ∈ Finset.Icc z.2.1 z.2.2, differencingPhase (z.1 / (n : ℝ))‖
  let P : ℕ → ℝ → (ℝ × ℤ × ℤ) → Prop := fun k U z =>
    U ^ (-(3 : ℝ) / 2) ≤ |z.1| * U ^ (-((k : ℝ) + 1)) ∧
    |z.1| * U ^ (-((k : ℝ) + 1)) ≤ U ^ (-(1 : ℝ) / 2) ∧
    U ≤ (z.2.1 : ℝ) ∧ (z.2.2 : ℝ) ≤ 2 * U
  have horders : ∀ k : ℕ, 4 ≤ k → k ≤ Nat.ceil B + 1 →
      ∃ A δ : ℝ, 0 < A ∧ 0 < δ ∧ ∃ T : ℝ,
        ∀ U : ℝ, T ≤ U → ∀ z : ℝ × ℤ × ℤ,
          P k U z → F k U z ≤ A * U ^ (1 - δ) := by
    intro k hk _
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hkfour : (4 : ℝ) ≤ k := by exact_mod_cast hk
    let α : ℝ := 1 / (10 * (k : ℝ))
    have hα : 0 < α := by dsimp [α]; positivity
    have hαsmall : α < (1 : ℝ) / 5 := by
      dsimp [α]
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 10 * k)).2
      nlinarith
    obtain ⟨C, hC, hterm⟩ := hterminal k hk
    have hb := reciprocal_interval_budget_eventually (k - 2) α C hα hαsmall hC
    obtain ⟨T, hT⟩ := eventually_atTop.mp (hterm.and hb)
    refine ⟨36, α / (2 : ℝ) ^ (k - 2), by norm_num, by positivity, T, ?_⟩
    intro U hU z hz
    obtain ⟨ht, hb⟩ := hT U hU
    exact hb z.2.1 z.2.2 hz.2.2.1 hz.2.2.2 (fun x => z.1 / x)
      (ht z.1 hz.1 hz.2.1 z.2.1 z.2.2 hz.2.2.1 hz.2.2.2)
  obtain ⟨A, δ, hA, hδ, T, _, hbound⟩ :=
    finite_derivative_order_power_saving (Nat.ceil B + 1) F P horders
  refine ⟨A, δ, hA, hδ, ?_⟩
  filter_upwards [eventually_ge_atTop T, eventually_gt_atTop (1 : ℝ)] with U hU hUone
  intro Z L R hlo hhi hL hR
  obtain ⟨k, hk, hkB, hklo, hkhi⟩ := reciprocal_phase_order hUone hB hlo hhi
  exact hbound k hk hkB U hU (Z, L, R) ⟨hklo, hkhi, hL, hR⟩

end Problem337

end

end OAI
