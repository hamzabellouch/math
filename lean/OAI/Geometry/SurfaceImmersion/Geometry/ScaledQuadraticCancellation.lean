import OAI.Geometry.SurfaceImmersion.Correction.PolynomialQuadraticCancellation
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialSolveFactors

namespace OAI

/-! Keep the delta-squared size and high residual power explicit in the
actual finite cancellation of all doubled and mixed quadratic phases. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates

theorem scaled_polynomial_quadratic_cancellation {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (P : Fin 3 → Fin n → Expression) (ε δ : ℝ)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (φ : ι → Base → ℝ)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (K : ι → Compacts Base)
    (H : ∀ i, SupportedField (F := Fin 4 → ℂ) (K i)) {τ : ℝ} {s : ℝ≥0}
    (c : ∀ l, PolynomialSolveData P ε G hG (quadraticFamilyPhase φ l) (quadraticCompacts K l) τ s)
    (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hε : 0 ≤ ε) (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1) (q : ℕ)
    (A : QuadraticLabel ι → ℕ → ℝ) :
    let f := fun l => combinedQuadraticTarget (c l).openU (c l).openO P (c l).smoothP hG φ hφ H
      (c l).mapsG l (c l).supportU ε τ 0
    (∀ l m, (c l).norm (f l) m ≤ δ ^ 2 * A l m) →
    ∃ V : RField 4, ContDiff ℝ ∞ V ∧ tsupport V ⊆ ⋃ i, (modeSupport (K i) : Set SmallModes.Base) ∧
      (∀ m, WeightedBound Set.univ τ m
        (δ ^ 2 * ∑ l, (c l).sizeFactor q m * A l (PolynomialSolveData.inputOrder (P := P) q m)) V) ∧
      (∀ m, WeightedBound Set.univ τ m
        (δ ^ 2 * (τ / s + ε / τ ^ tensorLoss P) ^ (q + 1) *
          ∑ l, (c l).residualFactor q m * A l (PolynomialSolveData.inputOrder (P := P) q m))
        (coordinateFullLinearized P ε G V + combinedNonzeroQuadratic P ε G φ (fun i => H i) τ)) := by
  dsimp only
  intro hA
  obtain ⟨V,hV,hsp,hsize,hres⟩ := polynomial_quadratic_cancellation P ε hG φ hφ K H c
    hτ hs hτs hs1 hε hsmall q
  refine ⟨V,hV,hsp,?_,?_⟩
  · intro m
    apply (hsize m).mono_const
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    exact (c l).size_le_scaled (sq_nonneg δ) _ q m (hA l _)
  · intro m
    apply (hres m).mono_const
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    have hh := (c l).residual_le_scaled
      (add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))) _ q m (hA l _)
    convert hh using 1

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
