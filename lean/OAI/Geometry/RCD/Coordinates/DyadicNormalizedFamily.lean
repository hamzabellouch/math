import OAI.Geometry.RCD.Coordinates.BoundedRegularNormalization

namespace OAI

/-! # Extracting one fixed-root dyadic normalization family -/

open Set Metric MeasureTheory

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The all-small-scales transformation theorem supplies a single chosen
family with exact means at the radii of the actual heat construction. -/
theorem exists_dyadic_normalized_family (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {n : ℕ} (u : Fin n → SobolevSpace μ hQ) (p : X) {R T β : ℝ}
    (hR : 0 < R) (hRT : 4 * R ≤ T)
    (hfamily : ∀ r : ℝ, 0 < r → 64 * r ≤ T →
      ∃ A : Euclidean n ≃L[ℝ] Euclidean n,
        IsExactMeanNormalization μ hQ (sobolevColumnMap μ hQ u)
          (ball p (16 * r)) measurableSet_ball A ∧
        ∃ w : X → Euclidean n,
          FirstOrderSplittingOn μ hQ p (16 * r) β (transformedColumn μ hQ u A) w) :
    ∃ S : ℕ → Euclidean n ≃L[ℝ] Euclidean n,
      (∀ i, IsExactMeanNormalization μ hQ (sobolevColumnMap μ hQ u)
        (ball p (R / 2 ^ i)) measurableSet_ball (S i)) ∧
      ∀ i, ∃ w : X → Euclidean n,
        FirstOrderSplittingOn μ hQ p (R / 2 ^ i) β (transformedColumn μ hQ u (S i)) w := by
  have hchoose (i : ℕ) : ∃ A : Euclidean n ≃L[ℝ] Euclidean n,
      IsExactMeanNormalization μ hQ (sobolevColumnMap μ hQ u)
        (ball p (R / 2 ^ i)) measurableSet_ball A ∧
      ∃ w : X → Euclidean n,
        FirstOrderSplittingOn μ hQ p (R / 2 ^ i) β (transformedColumn μ hQ u A) w := by
    have hs : 0 < R / (2 : ℝ) ^ i := div_pos hR (by positivity)
    have hsR : R / (2 : ℝ) ^ i ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
    have hsmall : 64 * ((R / 2 ^ i) / 16) ≤ T := by linarith
    have h := hfamily ((R / 2 ^ i) / 16) (by positivity) hsmall
    simpa only [show 16 * ((R / (2 : ℝ) ^ i) / 16) = R / 2 ^ i by ring] using h
  choose S hS using hchoose
  exact ⟨S, fun i => (hS i).1, fun i => (hS i).2⟩

end RegularPointCoordinates

end

end OAI
