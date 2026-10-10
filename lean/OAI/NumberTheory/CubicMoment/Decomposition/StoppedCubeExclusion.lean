import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSequenceSW
import OAI.NumberTheory.CubicMoment.Estimates.StructuredResidualFrequencies

namespace OAI

/-! Cube factors in the frequency are exact exclusions for the literal
stopped coefficient. Its established Kummer sequence bound therefore
applies to a small noncube core times an arbitrary bounded cube. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedCharacterSum_cube (B w z a b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (v j e : Eisenstein) :
    stoppedCharacterSum B w z a b u W selected (v*j^3) e =
      stoppedCharacterSum B w z a b u W selected v (e*j) := by
  unfold stoppedCharacterSum
  apply Finset.sum_congr rfl
  intro n hn
  have hnp : primary n := primaryPairSupport_primary _ _
    (fun r hr => orderedPrimarySupport_primary _
      (fun _ _ hp => (mem_primeCutoff.mp hp).1.1) hr)
    (fun d hd => (mem_primaryElementBall.mp hd).1) hn
  have hcop : IsCoprime n (e*j) ↔ IsCoprime n e ∧ IsCoprime n j :=
    ⟨fun h => ⟨h.of_mul_right_left,h.of_mul_right_right⟩,fun h => h.1.mul_right h.2⟩
  rw [cubicSymbol_mul_upper hnp,cubicSymbol_cube_indicator hnp j]
  by_cases he : IsCoprime n e <;> by_cases hj : IsCoprime n j <;>
    simp [hcop,he,hj]

theorem stopped_sequence_cube_sw (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
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
      ‖stoppedCharacterSum X (X^ξ) (X^(2/5:ℝ)) a b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k h Z Q early) (v*j^3) e‖ ≤ K*b/(Real.log X)^D := by
  obtain ⟨K,hK,hbound⟩ := stopped_sequence_kummer_sw (ι := ι)
    (E := E+d) hpnt hSW hξ hξz hκ hA hD hH hF hJ
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
  rw [stoppedCharacterSum_cube]
  exact hbound δ a b u V hδ hδone hwidth ha hb hbX hV hu hVF W hW hWi hWd
    v (e*j) hv hncv hNv (mul_ne_zero he hj) hNej j₀ k h Z Q early

end CubicFirstMoment

end

end OAI
