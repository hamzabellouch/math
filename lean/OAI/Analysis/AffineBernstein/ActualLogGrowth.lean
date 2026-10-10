import Mathlib
import OAI.Analysis.AffineBernstein.ActualLogMeasure
import OAI.Analysis.AffineBernstein.ActualLogMeasureFurther

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter Metric
open scoped Topology

open Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {κ : Type*} [Fintype κ] [DecidableEq κ]

lemma tsupport_logarithmicCutoff_subset (k : ℕ) (L : ℝ) :
    tsupport (logarithmicCutoff k L) ⊆ logarithmicBox k (L+1) := by
  apply closure_minimal _ (logarithmicBox_isClosed k (L+1))
  intro x hx i
  by_contra hi
  exact hx (logarithmicCutoff_zero ⟨i,(not_le.mp hi).le⟩)

/- Finiteness on each available logarithmic box follows from the literal
support-function density, without any a priori integral bound. -/
lemma affineEpigraphLogMeasure_box_finite {n k : ℕ}
    {μ : Measure (Space k)} [μ.IsAddHaarMeasure]
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (Space k × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set (Space k)} (hD : IsOpen D) (hDpos : D ⊆ positiveOrthant k)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) {R : ℝ}
    (hR : logarithmicBox k R ⊆ logSpace '' D) :
    affineEpigraphLogMeasure μ D Ω u a L bE (logarithmicBox k R) ≠ ⊤ := by
  obtain ⟨hM,hT,-⟩ := affineEpigraph_logWeight_regular hΩ hcv hu hp a L hD hDpos hK hzero bE
  exact (logTubeMeasure_compact_lt_top hDpos (hM.mul hT)
    (logarithmicBox_isCompact k R) hR).ne

/- The growth contradiction is now specialized to genuine affine-maximal
approximate graphs. Only the two remaining quantitative model bounds are inputs:
positive mass on one fixed box and a uniform polynomial upper bound. Every
Poincare estimate and local finiteness assertion is derived here. -/
theorem affineMaximal_no_polynomial_logMeasure {n k l₀ : ℕ}
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
    {c C : ℝ} (hc : 0 < c)
    (hpos : ∀ᶠ j in atTop, c ≤
      (affineEpigraphLogMeasure μ (D j) (Ω j) (u j) (a j) (L j) bE).real (logarithmicBox k l₀))
    (hupper : ∀ R : ℕ, l₀ ≤ R → ∀ᶠ j in atTop,
      (affineEpigraphLogMeasure μ (D j) (Ω j) (u j) (a j) (L j) bE).real (logarithmicBox k R) ≤
        C*(R+1:ℝ)^k) : False := by
  apply no_polynomial_logarithmic_poincare
    (fun j => affineEpigraphLogMeasure μ (D j) (Ω j) (u j) (a j) (L j) bE)
    hc (A := 4194304+(n : ℝ)*1358954512)
    (by positivity) hpos ?_ hupper ?_
  · intro R hR
    filter_upwards [havail R hR] with j hj
    exact affineEpigraphLogMeasure_box_finite (hΩ j) (hcv j) (hu j) (hp j) (a j) (L j)
      (hD j) (hDpos j) (hK j) (hzero j) bE hj
  · intro R hR
    filter_upwards [havail (R+1) (by omega)] with j hj
    apply affineMaximal_logMeasure_poincare hn hn9 hk hkn (hΩ j) (hcv j) (hu j) (hp j)
      (hm j) (a j) (L j) (hD j) (hDpos j) (hK j) (hzero j) bE
      (logarithmicCutoff_smooth k R) (logarithmicCutoff_hasCompactSupport k R)
    apply (tsupport_logarithmicCutoff_subset k R).trans
    simpa only [Nat.cast_add,Nat.cast_one] using hj

end AffineBernstein

end

end OAI
