import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedSequenceSW
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCharacterRows

namespace OAI

/-! Exact conversion of the stopped largest-prime decomposition to the
squarefree coefficient row used in angular dispersion. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma angular_stoppedCharacterSum_eq_rows (ℓ : ℤ) (X w z a b u : ℝ)
    (W : ι → ℝ → ℂ) (selected : Eisenstein → Eisenstein → Prop) (v e : Eisenstein) :
    angular_stoppedCharacterSum ℓ X w z a b u W selected v e =
      angularStoppedCharacterSum ℓ X w z a b u W selected v e := by
  unfold angular_stoppedCharacterSum angularStoppedCharacterSum stoppedIntervalSupport
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases h : Squarefree n ∧ IsCoprime n e ∧ a < norm n ∧ norm n ≤ b
  · simp only [h,and_self,ite_true,angularStoppedRowCoefficient,stoppedRowCoefficient,
      angularCubicSymbol,angularKummerCharacter]
    ring
  · simp only [h,ite_false,mul_zero]

theorem angular_stopped_row_kummer_sw (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {ξ κ A D H E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ a b u V : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      1 ≤ a → X^κ ≤ b → b ≤ X → 0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ l x, ‖W l x‖ ≤ 1) → (∀ l, ContDiff ℝ ∞ (W l)) →
      (∀ l x, 0 < x → ‖deriv (W l) x‖*x ≤ V) →
      ∀ v e : Eisenstein, v ≠ 0 → (¬∃ n : Eisenstein, n^3 = v) →
      norm v ≤ (Real.log X)^A → e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖angularStoppedCharacterSum ℓ X (X^ξ) (X^(2/5:ℝ)) a b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k h Z Q early) v e‖ ≤ K*b/(Real.log X)^D := by
  simpa only [angular_stoppedCharacterSum_eq_rows] using
    (angular_stopped_sequence_kummer_sw (ι := ι) hpnt hEF ℓ hℓ
      (E := E) hξ hξz hκ hA hD hH hF hJ)

end CubicFirstMoment

end

end OAI
