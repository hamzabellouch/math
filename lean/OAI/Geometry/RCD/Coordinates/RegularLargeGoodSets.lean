import OAI.Geometry.RCD.Coordinates.RegularGoodSplittingSets

namespace OAI

/-! # Arbitrarily large good sets at all sufficiently small regular scales -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.regular_large_good_sets {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {p : X} (hp : IsRegular n p) {t ζ : ℝ} (ht : 0 < t) (hζ : 0 < ζ) :
    ∃ s : ℝ, 0 < s ∧ ∀ R : ℝ, 0 < R → R < s →
      ∃ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
        (v : X → Euclidean n) (U : Set X),
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (2*R) t u v ∧
        IsCompact U ∧ U ⊆ closedBall p R ∧
        (hausdorff n X).real (ball p R \ U) ≤ ζ*(hausdorff n X).real (ball p R) ∧
        ∀ x ∈ U, ∀ r : ℝ, 0 < r → r < R →
          FirstOrderSplittingOn (hausdorff n X) hX.quadratic x r t u v := by
  let D := fiveBallConstant n
  have hD : 0 < D := by dsimp only [D,fiveBallConstant]; positivity
  let e := min t (ζ*t/(D^2*((n:ℝ)^2+1)))
  have he : 0 < e := lt_min ht (by positivity)
  have het : e ≤ t := min_le_left _ _
  have heζ : e*(D^2*((n:ℝ)^2+1)) ≤ ζ*t :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hcoef : (D/t)*((n:ℝ)^2*e)*D ≤ ζ := by
    calc
      _ = (D^2*(n:ℝ)^2*e)/t := by ring
      _ ≤ ζ := (div_le_iff₀ ht).mpr (by nlinarith [mul_nonneg (sq_nonneg D) he.le])
  obtain ⟨s,hs,hsets⟩ := hX.regular_good_splitting_sets hn hp he ht het
  refine ⟨s,hs,?_⟩
  intro R hR hRs
  obtain ⟨u,v,U,hcurv,hsplit,hU,hUsub,hbad,hgood⟩ := hsets R hR hRs
  have hvol : (hausdorff n X).real (ball p (2*R)) ≤ D*(hausdorff n X).real (ball p R) := by
    apply le_trans (measureReal_mono (ball_subset_ball (by linarith : 2*R ≤ 5*R))
      (hX.finiteOnBounded _ isBounded_ball).ne)
    exact hX.five_ball_doubling hn hR hcurv p R hR le_rfl
  refine ⟨u,v,U,hsplit.mono_error _ _ he.le het,hU,hUsub,hbad.trans ?_,hgood⟩
  calc
    _ ≤ (D/t)*((n:ℝ)^2*e*(D*(hausdorff n X).real (ball p R))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hvol (by positivity)) (by positivity)
    _ = ((D/t)*((n:ℝ)^2*e)*D)*(hausdorff n X).real (ball p R) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef measureReal_nonneg

end RegularPointCoordinates

end

end OAI
