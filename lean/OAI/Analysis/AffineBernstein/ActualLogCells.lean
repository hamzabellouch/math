import Mathlib
import OAI.Analysis.AffineBernstein.ActualLogGrowth
import OAI.Analysis.AffineBernstein.LogCellBound

namespace OAI

noncomputable section

namespace AffineBernstein

section ActualGrowthDependencies
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter Metric
open scoped Topology

section ActualLogCells
open Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

/- The exact analytic log-growth contradiction, reduced to a uniform bound on
each fixed unit cell of the genuine sigma measure. This is an intermediate
criterion: the model geometry must still produce its two mass hypotheses. -/
theorem affineMaximal_no_eventual_bounded_log_cells {n k l₀ : ℕ}
    (hn : 3 ≤ n) (hn9 : n ≤ 9) (hk : 2 ≤ k) (hkn : k ≤ n)
    {μ : Measure (Space k)} [μ.IsAddHaarMeasure]
    (Ω : ℕ → Set (Space n)) (u : ℕ → Space n → ℝ)
    (a : ℕ → Space n × ℝ) (L : ℕ → (Space k × E) ≃L[ℝ] (Space n × ℝ))
    (D : ℕ → Set (Space k)) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (hΩ : ∀ j, IsOpen (Ω j)) (hcv : ∀ j, Convex ℝ (Ω j))
    (hu : ∀ j, ContDiffOn ℝ ∞ (u j) (Ω j))
    (hp : ∀ j x, x ∈ Ω j → (hessian (u j) x).PosDef)
    (hm : ∀ j, AffineMaximalOn (Ω j) (u j))
    (hD : ∀ j, IsOpen (D j)) (hDpos : ∀ j, D j ⊆ positiveOrthant k)
    (hK : ∀ j s, s ∈ D j → IsCompact {y | (s,y) ∈ affineEpigraphPullback (Ω j) (u j) (a j) (L j)})
    (hzero : ∀ j s, s ∈ D j →
      (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback (Ω j) (u j) (a j) (L j)})
    (havail : ∀ R : ℕ, l₀ ≤ R → ∀ᶠ j in atTop, logarithmicBox k R ⊆ logSpace '' (D j))
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hpos : ∀ᶠ j in atTop, c ≤
      (affineEpigraphLogMeasure μ (D j) (Ω j) (u j) (a j) (L j) bE).real (logarithmicBox k l₀))
    (hcell : ∀ z : Fin k → ℤ, ∀ᶠ j in atTop,
      affineEpigraphLogMeasure μ (D j) (Ω j) (u j) (a j) (L j) bE
        (logarithmicUnitCell k z) ≤ ENNReal.ofReal C) : False := by
  apply affineMaximal_no_polynomial_logMeasure hn hn9 hk hkn Ω u a L D bE
    hΩ hcv hu hp hm hD hDpos hK hzero havail hc hpos
  intro R _
  exact eventual_logarithmicBox_bound_of_unitCells
    (fun j => affineEpigraphLogMeasure μ (D j) (Ω j) (u j) (a j) (L j) bE) hC hcell R
end ActualLogCells

-- END

end ActualGrowthDependencies

end AffineBernstein

end

end OAI
