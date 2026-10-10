import OAI.Combinatorics.Progressions.Sampling.BudgetedGridProjection

namespace OAI

section

namespace Erdos3.IntegerFourierBudget

open scoped BigOperators Classical

theorem controls_coefficientCap_nonneg {X J : Type*} [Fintype X] [Fintype J]
    (B : IntegerFourierBudget) (p : FiniteProbabilityWeights X)
    (Y : (J → ℤ) → X → J → ℤ) (K M : ℕ) [NeZero M] (hmodel : B.Controls p Y K M) :
    0 ≤ B.coefficientCap := by
  obtain ⟨_, _, hcap, _⟩ := hmodel 1 (by norm_num) le_rfl
  exact (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans (hcap (fun _ => 0))

theorem projected_approximation_at_error {X J H G : Type*}
    [Fintype X] [Fintype J] [AddCommGroup H] [Fintype H] [Fintype G]
    (B : IntegerFourierBudget) (p : FiniteProbabilityWeights X)
    (Y : (J → ℤ) → X → J → ℤ) (K M : ℕ) [NeZero M] (hKM : K ≤ M)
    (hmodel : B.Controls p Y K M) (q : FiniteProbabilityWeights G)
    (ι : H →+ (J → ZMod M)) (w : G → ℂ) (path : G → J → ℤ)
    {W δ : ℝ} (hδ : 0 < δ) (hw : q.mean (fun x => ‖w x‖) ≤ W)
    (hdiscard : ∀ k, B.RationalMode K M (projectionApproxTolerance W δ) k →
      (rectangularResidueMode M k).compAddMonoidHom ι ≠ 1 →
      ‖q.complexMean (fun x => w x * star (rectangularGridCharacter M k (path x)))‖ ≤
        projectionModeTolerance B.coefficientCap δ) :
    ∃ S : Finset (J → Fin M),
      (S.card : ℝ) ≤ B.countConstant / (projectionApproxTolerance W δ) ^ B.countExponent ∧
      (∀ center, (∑ k, ‖integerGridCoefficient p (Y center) M k‖) ≤ B.coefficientCap) ∧
      (∀ k ∈ S, B.RationalMode K M (projectionApproxTolerance W δ) k) ∧
      ∀ center, (∀ x, q.weight x ≠ 0 → centeredFundamentalBox B.radius K center (path x)) →
        ‖q.complexMean (fun x => w x *
          (((K : ℝ) ^ Fintype.card J * finiteImageMass p (Y center) (path x) : ℝ) : ℂ)) -
          q.complexMean (fun x => w x * finiteCosetAverage ι (residueGridApproximation p (Y center) K M S)
            (integerGridResidue M (path x)))‖ ≤ δ := by
  have hW : 0 ≤ W := (q.mean_nonneg (fun x => norm_nonneg (w x))).trans hw
  have hs := projectionErrorBudget_spec hW (B.controls_coefficientCap_nonneg p Y K M hmodel) hδ
  obtain ⟨S, hcount, hcap, hchar, herr⟩ := B.projected_approximation p Y K M hKM hmodel q ι w path
    hs.1 hs.2.1 hs.2.2.1.le hw hdiscard
  exact ⟨S, hcount, hcap, hchar, fun center hpath => (herr center hpath).trans hs.2.2.2⟩

end Erdos3.IntegerFourierBudget

end

end OAI
