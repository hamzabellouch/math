import OAI.NumberTheory.CubicMoment.Decomposition.StoppedBinMoment
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSmoothDiscard

namespace OAI

/-! The discarded short bins of the literal stopped coefficient have
arbitrary logarithmic saving, by their proved smooth support. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedBeta_short_bin_log_saving (hpnt : PrimaryPrimePNT)
    {ξ κ D : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ) :
    ∀ᶠ X : ℝ in atTop, ∀ (B ρ a b u : ℝ),
      1 < ρ → ρ ≤ 2 → 1 ≤ a → b ≤ B → X^κ ≤ b → b ≤ X →
      ∀ (S : ι → Finset Eisenstein) (W : ι → Eisenstein → ℂ)
        (R D₀ : Finset Eisenstein),
      (∀ l, ∀ p ∈ S l, primaryPrime p) → (∀ l, ∀ p ∈ S l, ‖W l p‖ ≤ 1) →
      (∀ r ∈ R, primary r) → (∀ d ∈ D₀, primary d) →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool) (v e : Eisenstein),
      ‖∑ n ∈ primaryPairSupport R D₀,
        stoppedBeta R D₀ (distinguishedTupleCoefficient S W primeDetectorCutoff
          (X^ξ) (X^(2/5:ℝ))) primeDetectorCutoff (X^ξ)
          (stoppedShortBinTest B ρ (Real.exp (Real.sqrt (Real.log X))) j₀ k h Z Q early) n*
        (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
          then normTwist u n*cubicSymbol n v else 0)‖ ≤ b/(Real.log X)^D := by
  filter_upwards [stoppedBeta_smooth_discard (ι := ι) (A := D) hpnt hξ hξz
      (C := 1) (by norm_num) hκ
      (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩)
      (fun _ _ hx => primeDetectorCutoff_one hx) (fun _ hx => primeDetectorCutoff_zero hx),
    eventually_gt_atTop (1:ℝ)] with X hdiscard hX
  intro B ρ a b u hρ hρ₂ ha hbB hbX hb S W R D₀ hS hW hR hD₀ j₀ k h Z Q early v e
  let y := Real.exp (Real.sqrt (Real.log X))
  let small := fun n : Eisenstein =>
    geometricBinLower ρ B (geometricPrimeBin ρ B (largestPrimeChoice n)) < y/2
  let U := (primaryPairSupport R D₀).filter (fun n =>
    (Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b) ∧ small n)
  let f := distinguishedTupleCoefficient S W primeDetectorCutoff (X^ξ) (X^(2/5:ℝ))
  let selected := stoppedShortBinTest B ρ y j₀ k h Z Q early
  let beta := stoppedBeta R D₀ f primeDetectorCutoff (X^ξ) selected
  have hprimary {n : Eisenstein} (hn : n ∈ primaryPairSupport R D₀) : primary n :=
    primaryPairSupport_primary R D₀ hR hD₀ hn
  have hzero (n : Eisenstein) (hn : ¬small n) : beta n = 0 := by
    change stoppedBeta R D₀ f primeDetectorCutoff (X^ξ)
      (fun r d => stoppedSideTest (geometricPrimeBin ρ B) (geometricBinLower ρ B)
        j₀ k h Z Q early r d ∧ small (r*d)) n = 0
    rw [stoppedBeta_product_predicate,ite_eq_right hn]
  have heq : (∑ n ∈ primaryPairSupport R D₀, beta n*
      (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
        then normTwist u n*cubicSymbol n v else 0)) =
      ∑ n ∈ U, beta n*(normTwist u n*cubicSymbol n v) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hc : Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
    · by_cases hs : small n
      · simp only [hc,hs,and_self,ite_true]
      · simp only [hc,hs,hzero n hs,and_false,ite_false,zero_mul]
    · simp only [hc,false_and,ite_false,mul_zero]
  have hU (n : Eisenstein) (hn : n ∈ U) : primary n ∧ Squarefree n := by
    obtain ⟨hn,hc,_⟩ := Finset.mem_filter.mp hn
    exact ⟨hprimary hn,hc.1⟩
  have hmass : (∑ n ∈ U, ‖beta n‖) ≤ b*(Real.log X)^(-D) := by
    apply hdiscard b S W R D₀ U selected hbX (by simpa only [one_mul] using hb)
      hS hW hR hU
    · intro n hn
      exact (Finset.mem_filter.mp hn).2.1.2.2.2
    · intro n hn
      obtain ⟨hn,hc,hs⟩ := Finset.mem_filter.mp hn
      exact stopped_short_bin_smooth hρ hρ₂ (hprimary hn) hc.1
        (ha.trans_lt hc.2.2.1) (hc.2.2.2.trans hbB) hs
  change ‖∑ n ∈ primaryPairSupport R D₀, beta n*_‖ ≤ _
  rw [heq]
  calc
    _ ≤ ∑ n ∈ U, ‖beta n‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul,norm_mul,norm_normTwist,one_mul]
      exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hU n hn).1 v)
    _ ≤ b*(Real.log X)^(-D) := hmass
    _ = _ := by rw [Real.rpow_neg (Real.log_pos hX).le,div_eq_mul_inv]

end CubicFirstMoment

end

end OAI
