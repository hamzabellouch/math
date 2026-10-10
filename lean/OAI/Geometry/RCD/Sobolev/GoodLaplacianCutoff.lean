import OAI.Geometry.RCD.Sobolev.HarmonicBochnerConstruction

namespace OAI

/-!
# Quantitative cutoff input and its canonical Bochner application

The existence input is the fixed radius-ratio specialization of Mondino--
Naber (2019), Lemma 3.1 (arXiv:1405.2222v3, pp.13--14), also stated in
Connell et al. (2021), Lemma 2.6. Scaling to unit radius and lowering the
curvature bound to -1 makes its constant dimensional. Support of the
Laplacian off the transition region is the locality of the weak Laplacian.
-/

open Set Metric MeasureTheory
open scoped NNReal InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- An actual Sobolev cutoff with bounded weak Laplacian. -/
structure GoodLaplacianCutoff (p : X) (r C : ℝ) where
  weight : X →ᵇ ℝ
  sobolev : SobolevSpace μ hQ
  laplacian : Lp ℝ 2 μ
  bounds : ∀ x, 0 ≤ weight x ∧ weight x ≤ 1
  one : ∀ x ∈ ball p r, weight x = 1
  zero : ∀ x, 2 * r < dist p x → weight x = 0
  lipschitz : LipschitzWith (C / r).toNNReal weight
  representative : SobolevSpace.toLp μ hQ sobolev =ᵐ[μ] weight
  weak_laplacian : IsWeakLaplacian μ hQ sobolev laplacian
  laplacian_bound : ∀ᵐ x ∂μ, |laplacian x| ≤ C / r ^ 2
  laplacian_locality : ∀ᵐ x ∂μ,
    (dist p x < r ∨ 2 * r < dist p x) → laplacian x = 0

/-- Exact existence consequence at bounded rescaled curvature. -/
def LocalGoodCutoffInput {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) : Prop :=
  2 ≤ n → ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : X) (r : ℝ), 0 < r →
    -1 ≤ K * r ^ 2 → Nonempty (GoodLaplacianCutoff (hausdorff n X) hX.quadratic p r C)

namespace GoodLaplacianCutoff

omit [ProperSpace X] [BorelSpace X] in
/-- The topological support remains inside the closed outer ball. -/
theorem tsupport_subset {p : X} {r C : ℝ} (χ : GoodLaplacianCutoff μ hQ p r C) :
    tsupport (χ.weight : X → ℝ) ⊆ closedBall p (2 * r) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hn
  exact hx (χ.zero x (by simpa only [mem_closedBall, dist_comm, not_le] using hn))

omit [BorelSpace X] in
theorem hasCompactSupport {p : X} {r C : ℝ} (χ : GoodLaplacianCutoff μ hQ p r C) :
    HasCompactSupport (χ.weight : X → ℝ) :=
  (isCompact_closedBall p (2 * r)).of_isClosed_subset (isClosed_tsupport _) (χ.tsupport_subset μ hQ)

/-- The good cutoff and local harmonic Bochner equation imply small mass
on the inner ball, without a separate raw-source assumption. -/
theorem harmonic_mass_le [IsFiniteMeasureOnCompacts μ]
    {n : ℕ} {p : X} {ρ C r κ : ℝ} {L : ℝ≥0}
    (χ : GoodLaplacianCutoff μ hQ p ρ C) (hρ : 0 < ρ) (hρr : ρ < r)
    (hC : 0 ≤ C) (hκ : 0 ≤ κ) (u : Fin n → SobolevSpace μ hQ)
    (M : PositiveBilinearMeasure X (Euclidean n))
    (G : ∀ v, LocalHarmonicEnergy μ hQ (sobolevColumnMap μ hQ u) M κ p r L v)
    {ε : ℝ} (hε : 0 ≤ ε)
    (herror : ∀ i j : Fin n, ∫ x in closedBall p (2 * ρ),
      |localGamma μ hQ (u i) (u j) x - (if i = j then 1 else 0)| ∂μ ≤ ε)
    (v : Euclidean n) :
    ⟪v, M.massOperator (ball p ρ) v⟫_ℝ ≤
      ((C / ρ ^ 2) * ((n : ℝ) ^ 2 * ε) / 2 +
        κ * ((n : ℝ) ^ 2 * ε + μ.real (closedBall p (2 * ρ)))) * ‖v‖ ^ 2 := by
  apply harmonic_bochner_mass_le μ hQ u M G χ.weight χ.bounds
    (χ.hasCompactSupport μ hQ) _ (mul_pos (by norm_num) hρ) (by linarith)
    χ.zero χ.sobolev χ.representative χ.laplacian χ.weak_laplacian _
    (ball p ρ) measurableSet_ball χ.one (div_nonneg hC (sq_nonneg ρ)) hε hκ
    χ.laplacian_bound herror v
  · intro x hx
    have hd : dist x p ≤ 2 * ρ := χ.tsupport_subset μ hQ hx
    exact lt_of_le_of_lt hd (by linarith)
  · filter_upwards [χ.laplacian_locality] with x hx hdist
    exact hx (Or.inr hdist)

end GoodLaplacianCutoff
end RegularPointCoordinates

end

end OAI
