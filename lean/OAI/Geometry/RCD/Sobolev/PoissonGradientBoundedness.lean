import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Sobolev.PoissonInteriorSmallRadii

namespace OAI

/-! # Local boundedness of the gradient on arbitrary interior balls -/

open Set Filter Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- A uniformly small auxiliary radius gives qualitative boundedness on
every interior ball. The later Bochner iteration removes its radius loss. -/
theorem NoncollapsedRCD.poisson_gradient_locally_bounded {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff n X) ker)
    (p : X) (R : ℝ) (hR : 0 < R)
    (f : SobolevSpace (hausdorff n X) hX.quadratic) (c : ℝ) (A : ℝ≥0)
    (hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (8*R)) f c)
    (hA : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*R)), |SobolevSpace.toLp _ _ f x| ≤ A) :
    ∃ L : ℝ≥0, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (4*R)),
      localGamma (hausdorff n X) hX.quadratic f f x ≤ (L:ℝ)^2 := by
  obtain ⟨M,hM,hlocal⟩ := hX.small_scale_poisson_gradient hn hk hg
  let : TopologicalSpace.SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨g,hg,hgA,hfg⟩ := hf.bounded_extension μ hX.quadratic measurableSet_ball A hA
  have hpair := localGamma_pair_congr_ae μ hX.quadratic hfg hfg
  let ρ := min (R/16) (1/(16*(|K|+1)))
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρR : 16*ρ ≤ R := by have hh := min_le_left (R/16) (1/(16*(|K|+1))); dsimp only [ρ]; linarith
  have hsmall : ρ*(16*(|K|+1)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (min_le_right (R/16) (1/(16*(|K|+1))))
  have hρ1 : ρ ≤ 1 := by
    have hh : 0 ≤ |K| *ρ := mul_nonneg (abs_nonneg K) hρ.le
    nlinarith
  have hcurv : -1 ≤ K*(4*ρ)^2 := by
    have h0 : 0 ≤ |K| *ρ := mul_nonneg (abs_nonneg K) hρ.le
    have h1 : |K| *(4*ρ) ≤ 1 := by nlinarith only [hsmall,hρ.le]
    have h2 : 4*ρ ≤ 1 := by nlinarith only [hsmall,h0]
    have hh := mul_le_mul h1 h2 (by positivity : 0 ≤ 4*ρ) (by norm_num : (0:ℝ) ≤ 1)
    have hK := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg (4*ρ))
    nlinarith only [hh,hK]
  let L : ℝ≥0 := ⟨M*((A:ℝ)/ρ+|c| *ρ),by positivity⟩
  refine ⟨L,?_⟩
  have hestimate (q : ball p (4*R)) :
      ∀ᵐ x ∂μ.restrict (ball q.val (ρ/16)), localGamma μ hX.quadratic f f x ≤ (L:ℝ)^2 := by
    have hq : dist q.val p < 4*R := q.property
    have hsub : ball q.val (16*ρ) ⊆ ball p (8*R) := ball_subset_ball' (by linarith)
    have hh := hlocal q.val ρ hρ hρ1 hcurv g c A
      (hg.mono μ hX.quadratic measurableSet_ball hsub) hgA
    have hsub' : ball q.val (ρ/16) ⊆ ball p (8*R) := ball_subset_ball' (by linarith)
    filter_upwards [hh,ae_restrict_of_ae_restrict_of_subset hsub' hpair] with x hx he
    rw [he]
    exact hx
  let U : ball p (4*R) → Set X := fun q => ball q.val (ρ/16)
  obtain ⟨s,hs,hcover⟩ := (HereditarilyLindelofSpace.isLindelof (ball p (4*R))).elim_countable_subcover
    U (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (by positivity)⟩)
  exact ae_restrict_of_ae_restrict_of_subset hcover
    ((ae_restrict_biUnion_iff U hs _).mpr (fun q _ => hestimate q))

end RegularPointCoordinates

end

end OAI
