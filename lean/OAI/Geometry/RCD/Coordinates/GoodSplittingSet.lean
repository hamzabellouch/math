import OAI.Geometry.RCD.Harmonic.GramDefect
import OAI.Geometry.RCD.Sobolev.WeakMaximal
import OAI.Geometry.RCD.Harmonic.FirstOrderLocalization

namespace OAI

/-! # One compact good set for every smaller splitting scale

The original harmonic functions and their representatives are retained.
Only their finite Gram defect enters the maximal estimate.
-/

open Set Metric MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.good_splitting_set {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (p : X) {R ε t : ℝ} (hR : 0 < R) (hcurv : -1 ≤ K*(5*R)^2)
    (hε : 0 ≤ ε) (ht : 0 < t) (hεt : ε ≤ t)
    {u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic} {v : X → Euclidean n}
    (hsplit : FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (2*R) ε u v) :
    ∃ U : Set X, IsCompact U ∧ U ⊆ closedBall p R ∧
      (hausdorff n X).real (ball p R \ U) ≤
        (fiveBallConstant n/t)*((n:ℝ)^2*ε*(hausdorff n X).real (ball p (2*R))) ∧
      ∀ x ∈ U, ∀ r : ℝ, 0 < r → r < R →
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic x r t u v := by
  let μ := hausdorff n X
  have hfin : μ (ball p (2*R)) ≠ ⊤ := (hX.finiteOnBounded _ isBounded_ball).ne
  have hvol : 0 < μ.real (ball p (2*R)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (by positivity)).ne' hfin
  have hfi := gramDefect_integrableOn μ hX.quadratic u hfin
  have hbound := gramDefect_integral_bound μ hX.quadratic hvol hfin hsplit
  obtain ⟨U,hU,hUsub,hbad,hgood⟩ := hX.local_maximal_good_set hn p hR hcurv ht hfi
    (Filter.Eventually.of_forall (gramDefect_nonneg μ hX.quadratic u))
  refine ⟨U,hU,hUsub,hbad.trans ?_,?_⟩
  · exact mul_le_mul_of_nonneg_left hbound (by unfold fiveBallConstant; positivity)
  · intro x hx r hr hrR
    have hsub : ball x r ⊆ ball p (2*R) := by
      intro y hy
      have hh := dist_triangle y x p
      have hyx : dist y x < r := hy
      have hxp : dist x p ≤ R := hUsub hx
      change dist y p < 2*R
      linarith
    refine ⟨fun i => ae_restrict_of_ae_restrict_of_subset hsub (hsplit.representative i),
      hsplit.continuous.mono hsub,fun i => (hsplit.harmonic i).mono μ hX.quadratic hsub,?_,?_⟩
    · intro i
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (hsplit.gradient i)] with y hy
      exact hy.trans (by nlinarith : (1+ε)^2 ≤ (1+t)^2)
    · intro i j
      have hsmallfin : μ (ball x r) ≠ ⊤ := (hX.finiteOnBounded _ isBounded_ball).ne
      have hsmallvol : 0 < μ.real (ball x r) :=
        ENNReal.toReal_pos (hX.fullSupport x r hr).ne' hsmallfin
      rw [← div_eq_inv_mul,div_le_iff₀ hsmallvol]
      apply le_trans _ (hgood x hx r hr hrR)
      apply integral_mono
        (((localGamma_memL1 μ hX.quadratic (u i) (u j)).integrableOn.sub
          (integrableOn_const hsmallfin)).abs) (hfi.mono_set hsub)
      exact gramDefect_entry_le μ hX.quadratic u i j

end RegularPointCoordinates

end

end OAI
