import OAI.NumberTheory.Ostmann.QuadraticCenter.HighWeightExponential
import OAI.NumberTheory.Ostmann.QuadraticCenter.HighWeightScaleExponent

namespace OAI

open Erdos970

namespace Ostmann.QuadraticCenter
open scoped BigOperators Topology
open Filter

theorem high_weight_mass_eventually :
    ∀ᶠ T : ℝ in atTop, ∀ (S : Finset ℕ) (X L a : ℕ) (u K : ℝ),
      0 < L → 2 * L ^ 2 ≤ X → (X : ℝ) ≤ Real.exp (T ^ 2) →
      1 < u → u ≤ T ^ ((1 : ℝ) / 100000) → T ^ ((3 : ℝ) / 4) ≤ K →
      (∀ n ∈ S, Squarefree n) → (∀ n ∈ S, n.Coprime L) →
      (∀ n ∈ S, Nat.ModEq L n a) → (∀ n ∈ S, n ≤ 2 * X) →
      (∀ n ∈ S, Real.exp (K / 200) < u ^ n.primeFactors.card) →
      (∑ n ∈ S, u ^ n.primeFactors.card) ≤
        ((X : ℝ) / (L : ℝ)) * Real.exp (-10 * K) := by
  obtain ⟨C, hC, hmass⟩ := high_weight_mass_le_exponential
  filter_upwards [high_weight_error_budget_eventually C] with T hTbudget
  intro S X L a u K hL hX hXupper hu huupper hK hS hcop hres hupper hweight
  have hT := hTbudget.1
  have hT0 : 0 ≤ T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hK0 : 0 ≤ K := (Real.rpow_nonneg hT0 _).trans hK
  have hX1 : 1 ≤ X := by nlinarith
  have hv : 1 ≤ T ^ ((1 : ℝ) / 4) := Real.one_le_rpow hT1 (by norm_num)
  apply (hmass S X L a hL hX hS hcop hres hupper u (T ^ ((1 : ℝ) / 4))
    (K / 200) hu hv (by positivity) hweight).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  exact high_weight_scale_exponent_le hT hC hu huupper hK hX1 hXupper hTbudget.2

noncomputable def highWeightResidueSet (X L a : ℕ) (u K : ℝ) : Finset ℕ := by
  classical
  exact (Finset.Ico X (2 * X)).filter (fun n =>
    Squarefree n ∧ n.Coprime L ∧ Nat.ModEq L n a ∧
      Real.exp (K / 200) < u ^ n.primeFactors.card)

@[simp] theorem mem_highWeightResidueSet {X L a n : ℕ} {u K : ℝ} :
    n ∈ highWeightResidueSet X L a u K ↔
      X ≤ n ∧ n < 2 * X ∧ Squarefree n ∧ n.Coprime L ∧ Nat.ModEq L n a ∧
        Real.exp (K / 200) < u ^ n.primeFactors.card := by
  classical
  simp only [highWeightResidueSet, Finset.mem_filter, Finset.mem_Ico, and_assoc]

theorem high_weight_residue_mass_eventually :
    ∀ᶠ T : ℝ in atTop, ∀ (X L a : ℕ) (u K : ℝ),
      0 < L → 2 * L ^ 2 ≤ X → (X : ℝ) ≤ Real.exp (T ^ 2) →
      1 < u → u ≤ T ^ ((1 : ℝ) / 100000) → T ^ ((3 : ℝ) / 4) ≤ K →
      (∑ n ∈ highWeightResidueSet X L a u K, u ^ n.primeFactors.card) ≤
        ((X : ℝ) / (L : ℝ)) * Real.exp (-10 * K) := by
  filter_upwards [high_weight_mass_eventually] with T hT
  intro X L a u K hL hX hXupper hu huupper hK
  apply hT (highWeightResidueSet X L a u K) X L a u K hL hX hXupper hu huupper hK
  all_goals
    intro n hn
    obtain ⟨hnX, hn2, hns, hnc, hnr, hnw⟩ := mem_highWeightResidueSet.mp hn
    first | assumption | exact hn2.le

end Ostmann.QuadraticCenter

end OAI
