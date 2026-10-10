import OAI.Probability.InvariantIsing.Core.PositiveRationalApproximation
import OAI.Probability.InvariantIsing.Core.FiniteFieldLabels

namespace OAI

/-! Positive rational approximations to arbitrary finite field populations. -/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace InvariantIsing

def fieldApproxDenominator {A : Type*} [Fintype A] (γ : A → ℝ) (k : ℕ) : ℕ :=
  ∑ a, positiveApproxCount (γ a) k

def fieldApproxWeights {A : Type*} [Fintype A] (γ : A → ℝ) (k : ℕ) (a : A) : ℝ :=
  (positiveApproxCount (γ a) k : ℝ)/fieldApproxDenominator γ k

lemma fieldApproxDenominator_pos {A : Type*} [Fintype A] (a0 : A) (γ : A → ℝ) (k : ℕ) :
    0 < fieldApproxDenominator γ k :=
  (positiveApproxCount_pos (γ a0) k).trans_le
    (Finset.single_le_sum (f := fun a => positiveApproxCount (γ a) k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a0))

lemma fieldApproxWeights_pos {A : Type*} [Fintype A] (a0 : A) (γ : A → ℝ) (k : ℕ) (a : A) :
    0 < fieldApproxWeights γ k a :=
  div_pos (Nat.cast_pos.mpr (positiveApproxCount_pos _ _))
    (Nat.cast_pos.mpr (fieldApproxDenominator_pos a0 γ k))

lemma fieldApproxWeights_sum {A : Type*} [Fintype A] (a0 : A) (γ : A → ℝ) (k : ℕ) :
    ∑ a, fieldApproxWeights γ k a=1 := by
  simp only [fieldApproxWeights,← Finset.sum_div,← Nat.cast_sum]
  exact div_self (Nat.cast_ne_zero.mpr (fieldApproxDenominator_pos a0 γ k).ne')

lemma fieldApproxWeights_tendsto {A : Type*} [Fintype A] (γ : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hsum : ∑ a, γ a=1) :
    Tendsto (fieldApproxWeights γ) atTop (𝓝 γ) := by
  have hden : Tendsto (fun k => (fieldApproxDenominator γ k : ℝ)/(k+1)) atTop (𝓝 (1:ℝ)) := by
    have hh := tendsto_finsetSum Finset.univ (fun a _ => positiveApproxCount_ratio (γ a) (hγ a))
    simpa only [fieldApproxDenominator,Nat.cast_sum,Finset.sum_div,hsum] using hh
  apply tendsto_pi_nhds.mpr
  intro a
  have hh := (positiveApproxCount_ratio (γ a) (hγ a)).div hden one_ne_zero
  simp only [div_one] at hh
  apply hh.congr
  intro k
  exact div_div_div_cancel_right₀ (by positivity : (k+1 : ℝ)≠0) _ _

end InvariantIsing

end

end OAI
