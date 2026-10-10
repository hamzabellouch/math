import OAI.Geometry.RCD.Sobolev.BochnerCutoffIdentity
import OAI.Geometry.RCD.Sobolev.BochnerMassEstimate

namespace OAI

/-! # Small Bochner mass from the harmonic Gram error

The local harmonic Bochner equation and cutoff Laplacian bound the full measure.
-/

open Set Metric MeasureTheory
open scoped NNReal InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)

/-- The canonical local Bochner family satisfies the small-mass estimate
with exactly the dimension loss in the coordinatewise Gram error. -/
theorem harmonic_bochner_mass_le {n : ℕ} (u : Fin n → SobolevSpace μ hQ)
    (M : PositiveBilinearMeasure X (Euclidean n)) {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0}
    (G : ∀ v, LocalHarmonicEnergy μ hQ (sobolevColumnMap μ hQ u) M κ p r L v)
    (χ : X →ᵇ ℝ) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχs : HasCompactSupport (χ : X → ℝ))
    (hχΩ : tsupport (χ : X → ℝ) ⊆ ball p (2 * r))
    {R : ℝ} (hR : 0 < R) (hRr : R < 2 * r)
    (hχR : ∀ x, R < dist p x → χ x = 0)
    (c : SobolevSpace μ hQ) (hc : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    (q : Lp ℝ 2 μ) (hq : IsWeakLaplacian μ hQ c q)
    (hqR : ∀ᵐ x ∂μ, R < dist p x → q x = 0)
    (s : Set X) (hs : MeasurableSet s) (hχone : ∀ x ∈ s, χ x = 1)
    {D ε : ℝ} (hD : 0 ≤ D) (hε : 0 ≤ ε) (hκ : 0 ≤ κ)
    (hqb : ∀ᵐ x ∂μ, |q x| ≤ D)
    (herror : ∀ i j : Fin n, ∫ x in closedBall p R,
      |localGamma μ hQ (u i) (u j) x - (if i = j then 1 else 0)| ∂μ ≤ ε)
    (v : Euclidean n) :
    ⟪v, M.massOperator s v⟫_ℝ ≤
      (D * ((n : ℝ) ^ 2 * ε) / 2 +
        κ * ((n : ℝ) ^ 2 * ε + μ.real (closedBall p R))) * ‖v‖ ^ 2 := by
  apply bochner_mass_le_of_coordinate_errors μ hQ u M χ hχ p hR hχR c hc q hq
    hqR s hs hχone hD hε hκ hqb herror
  intro w
  have hqs : ∀ᵐ x ∂μ, x ∉ ball p (2 * r) → q x = 0 := by
    filter_upwards [hqR] with x hx hnot
    apply hx
    have hdist : 2 * r ≤ dist p x := by
      simpa only [mem_ball, dist_comm, not_lt] using hnot
    exact hRr.trans_le hdist
  have hi := (G w).test_cutoff μ hQ χ hχs hχΩ c hc q hq hqs
  have hΓq : (∫ x in closedBall p R,
      localGamma μ hQ (sobolevColumnMap μ hQ u w) (sobolevColumnMap μ hQ u w) x * q x ∂μ) =
      ∫ x, localGamma μ hQ (sobolevColumnMap μ hQ u w) (sobolevColumnMap μ hQ u w) x * q x ∂μ := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hqR] with x hx hnot
    rw [hx (by simpa only [mem_closedBall, dist_comm, not_le] using hnot), mul_zero]
  have hχΓ : (∫ x in closedBall p R,
      χ x * localGamma μ hQ (sobolevColumnMap μ hQ u w) (sobolevColumnMap μ hQ u w) x ∂μ) =
      ∫ x, χ x * localGamma μ hQ (sobolevColumnMap μ hQ u w) (sobolevColumnMap μ hQ u w) x ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [hχR x (by simpa only [mem_closedBall, dist_comm, not_le] using hx), zero_mul]
  rw [hΓq, hχΓ]
  exact hi

end RegularPointCoordinates

end

end OAI
