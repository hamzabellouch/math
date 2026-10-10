import OAI.Geometry.RCD.Coordinates.CenteredFirstOrderFrame

namespace OAI

/-! # The exact inner Gram error of centered first-order coordinates -/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
theorem centered_frame_gram_bound {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
    {p : X} {r ε D : ℝ} (hr : 0 < r) (hε : 0 ≤ ε)
    (u w : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (v : X → Euclidean n)
    (hsplit : FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (80*r) ε u v)
    (hvol : (hausdorff n X).real (ball p (80*r)) ≤ D*(hausdorff n X).real (ball p (5*r)))
    (he : ∀ i j, (fun x => r^2*localGamma (hausdorff n X) hX.quadratic (w i) (w j) x) =ᵐ[
      (hausdorff n X).restrict (ball p (5*r))]
      localGamma (hausdorff n X) hX.quadratic (u i) (u j)) (i j : Fin n) :
    ((hausdorff n X).real (ball p (5*r)))⁻¹*
      ∫ x in ball p (4*r), |r^2*localGamma (hausdorff n X) hX.quadratic (w i) (w j) x-
        (if i=j then 1 else 0)| ∂hausdorff n X ≤ D*ε := by
  let μ := hausdorff n X
  let f := fun x => |localGamma μ hX.quadratic (u i) (u j) x-(if i=j then 1 else 0)|
  have hf : IntegrableOn f (ball p (80*r)) μ :=
    ((localGamma_memL1 μ hX.quadratic (u i) (u j)).integrableOn.sub
      (integrableOn_const (hX.finiteOnBounded _ isBounded_ball).ne)).abs
  have hs : ball p (5*r) ⊆ ball p (80*r) := ball_subset_ball (by linarith)
  have ht : ball p (4*r) ⊆ ball p (5*r) := ball_subset_ball (by linarith)
  have hpos (a : ℝ) (ha : 0 < a) : 0 < μ.real (ball p (a*r)) :=
    ENNReal.toReal_pos (ne_of_gt (hX.fullSupport p (a*r) (mul_pos ha hr)))
      (hX.finiteOnBounded _ isBounded_ball).ne
  have hb := average_nonneg_le_of_subset μ hs (hpos 5 (by norm_num))
    (hpos 80 (by norm_num)) hf (fun x => abs_nonneg _) hε hvol (hsplit.gram i j)
  rw [integral_congr_ae (show (fun x => |r^2*localGamma μ hX.quadratic (w i) (w j) x-
      (if i=j then 1 else 0)|) =ᵐ[μ.restrict (ball p (4*r))] f from by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset ht (he i j)] with x hx
    dsimp only [f]
    rw [hx])]
  exact (mul_le_mul_of_nonneg_left
    (setIntegral_mono_set (hf.mono_set hs) (Filter.Eventually.of_forall (fun x => abs_nonneg _))
      (Filter.Eventually.of_forall ht)) (inv_nonneg.mpr measureReal_nonneg)).trans hb

end RegularPointCoordinates

end

end OAI
