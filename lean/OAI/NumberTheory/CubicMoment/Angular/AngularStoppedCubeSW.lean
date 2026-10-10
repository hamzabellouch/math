import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedSequenceRows
import OAI.NumberTheory.CubicMoment.Estimates.StructuredResidualFrequencies

namespace OAI

/-! Cube frequencies are genuine coprimality exclusions in the angular
stopped row. The angular factor occurs only once in the coefficient. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_sequence_cube_sw (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {ξ κ A D H E F J d : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hA : 0 < A) (hD : 0 < D) (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ a b u V : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      1 ≤ a → X^κ ≤ b → b ≤ X → 0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ l x, ‖W l x‖ ≤ 1) → (∀ l, ContDiff ℝ ∞ (W l)) →
      (∀ l x, 0 < x → ‖deriv (W l) x‖*x ≤ V) →
      ∀ v j e : Eisenstein, v ≠ 0 → j ≠ 0 → (¬∃ n : Eisenstein, n^3 = v*j^3) →
      norm v ≤ (Real.log X)^A → norm j ≤ X^d → e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k h : ℕ) (Z Q : ℝ) (early : Bool),
      ‖angularStoppedCharacterSum ℓ X (X^ξ) (X^(2/5:ℝ)) a b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k h Z Q early) (v*j^3) e‖ ≤ K*b/(Real.log X)^D := by
  obtain ⟨K,hK,hbound⟩ := angular_stopped_row_kummer_sw (ι := ι)
    (E := E+d) hpnt hEF ℓ hℓ hξ hξz hκ hA hD hH hF hJ
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (1:ℝ)] with X hbound hX
  intro δ a b u V hδ hδone hwidth ha hb hbX hV hu hVF W hW hWi hWd
    v j e hv hj hnc hNv hNj he hNe j₀ k h Z Q early
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hncv : ¬∃ n : Eisenstein, n^3 = v := by
    rintro ⟨n,hn⟩
    exact hnc ⟨n*j,by rw [mul_pow,hn]⟩
  have hNej : norm (e*j) ≤ X^(E+d) := by
    rw [norm_mul_eq,Real.rpow_add hXpos]
    exact mul_le_mul hNe hNj (norm_nonneg _) (Real.rpow_nonneg hXpos.le _)
  rw [angularStoppedCharacterSum_cube ℓ]
  exact hbound δ a b u V hδ hδone hwidth ha hb hbX hV hu hVF W hW hWi hWd
    v (e*j) hv hncv hNv (mul_ne_zero he hj) hNej j₀ k h Z Q early


end CubicFirstMoment

end

end OAI
