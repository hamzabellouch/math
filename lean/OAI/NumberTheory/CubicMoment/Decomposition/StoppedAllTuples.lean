import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDistinguishedLogSaving
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedEmptyTuple

namespace OAI

/-! The distinguished-role estimate for every finite tuple, including
zero distinguished primes. The empty case is an exact vanishing identity. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedBeta_distinguished_log_saving_all (m : ℕ)
    (hSW : KummerPrimeSiegelWalfisz) {A D H E F C ξ : ℝ}
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hF : 0 ≤ F)
    (hξ : 0 < ξ) (hgap : C < ξ*m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (B ρ a b z u V : ℝ) (j : ℕ),
      1 < ρ → ρ ≤ 2 → j < geometricBinCount ρ B →
      Real.exp (Real.sqrt (Real.log X))/2 ≤ geometricBinLower ρ B j →
      0 ≤ b → b ≤ X^C → X^ξ ≤ z → 0 ≤ V →
      |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ (W : ι → ℝ → ℂ) (D₀ : Finset Eisenstein),
      (∀ l x, ‖W l x‖ ≤ 1) → (∀ l, ContDiff ℝ ∞ (W l)) →
      (∀ l x, 0 < x → ‖deriv (W l) x‖*x ≤ V) →
      (∀ d ∈ D₀, primary d) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
      norm v ≤ (Real.log X)^A → e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖∑ n ∈ primaryPairSupport (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D₀,
        stoppedBeta (orderedConvolutionSupport (fun _ : ι => primeCutoff B)) D₀
          (distinguishedTupleCoefficient (fun _ : ι => primeCutoff B)
            (fun l p => W l (norm p)) primeDetectorCutoff (X^ξ) z) primeDetectorCutoff (X^ξ)
          (stoppedDistinguishedTest B ρ j j₀ k h Z Q early) n *
        (if Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
          then normTwist u n*cubicSymbol n v else 0)‖ ≤ K*b/(Real.log X)^D := by
  rcases isEmpty_or_nonempty ι with he | hn
  · have := he
    refine ⟨1,zero_lt_one,?_⟩
    filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
    intro B ρ a b z u V j _hρ _hρ₂ hj _hPlong hb _hbX _hwz _hV _hu _hVF
      W D₀ _hW _hWi _hWd hD₀ v e _hv _hnc _hNv _he _heX j₀ k h Z Q early
    rw [stopped_distinguished_empty B ρ a b (X^ξ) z u hj j₀ k h Z Q early W D₀ hD₀ v e,
      norm_zero,one_mul]
    exact div_nonneg hb (Real.rpow_nonneg (Real.log_nonneg hX.le) _)
  · have := hn
    exact stoppedBeta_distinguished_log_saving m hSW hA hD hH hF hξ hgap

end CubicFirstMoment

end

end OAI
