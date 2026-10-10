import OAI.NumberTheory.JointDickman.Analysis.LogPhaseDifferencingBudget
import OAI.NumberTheory.JointDickman.Amplification.CorrelationPhase

namespace OAI
noncomputable section
open scoped BigOperators Topology
open Filter
namespace JointDickman
open Problem337

/-- Ambient normalization converts a terminal forward-difference estimate
on every shortened subinterval into cancellation on the original interval. -/
theorem logarithmic_interval_budget_eventually (r : ℕ) (α C : ℝ)
    (hα : 0 < α) (hαsmall : α < (1 : ℝ) / 5) (hC : 0 ≤ C) :
    ∀ᶠ (U : ℝ) in atTop, ∀ (L R : ℤ), U ≤ (L : ℝ) → (R : ℝ) ≤ 2 * U →
      ∀ f : ℝ → ℝ,
      (∀ hs : List ℤ, hs.length = r →
        (∀ h ∈ hs, 0 < h ∧ h < (Nat.floor (U ^ α) : ℤ)) →
        ‖∑ n ∈ Finset.Icc L (R - hs.sum),
          differencingPhase (forwardDifference (hs.map (fun h : ℤ => (h : ℝ))) f n)‖ ≤
          C * U ^ ((4 : ℝ) / 5)) →
      ‖∑ n ∈ Finset.Icc L R, differencingPhase (f n)‖ ≤
        36 * U ^ (1 - α / (2 : ℝ) ^ r) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    logarithmic_differencing_budget_eventually r α C hα hαsmall hC] with U hU hbudget
  intro L R hUL hRU f hterminal
  let N : ℕ := Nat.ceil (2 * U)
  have hUN : U ≤ (N : ℝ) := by
    have hceil : 2 * U ≤ (N : ℝ) := Nat.le_ceil _
    linarith
  have hNU : (N : ℝ) ≤ 3 * U := by
    have hceil : (N : ℝ) < 2 * U + 1 := Nat.ceil_lt_add_one (by linarith)
    linarith
  have hL : (1 : ℤ) ≤ L := by exact_mod_cast hU.trans hUL
  have hR : R ≤ (N : ℤ) := by
    have hceil : 2 * U ≤ (N : ℝ) := Nat.le_ceil _
    exact_mod_cast hRU.trans hceil
  have hsupp : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → intervalPhase f L R n = 0 := by
    intro n hn
    have hout : ¬ (L ≤ n ∧ n ≤ R) := by
      simp only [Finset.mem_Icc] at hn
      omega
    simp [intervalPhase, hout]
  have hnrm : ∀ n : ℤ, ‖intervalPhase f L R n‖ ≤ 1 := by
    intro n
    unfold intervalPhase
    split_ifs <;> simp
  have hb := hbudget N hUN hNU (intervalPhase f L R) hsupp hnrm (by
    intro hs hlen hsteps
    have hnonneg : ∀ h ∈ hs, 0 ≤ h := fun h hh => (hsteps h hh).1.le
    rw [iteratedCorrelation_intervalPhase hs f L R hnonneg]
    have hsum : 0 ≤ hs.sum := List.sum_nonneg hnonneg
    rw [intervalPhase_sum _ L (R - hs.sum) 1 N hL (by omega)]
    exact hterminal hs hlen hsteps)
  rwa [intervalPhase_sum f L R 1 N hL hR] at hb

end JointDickman

end

end OAI
