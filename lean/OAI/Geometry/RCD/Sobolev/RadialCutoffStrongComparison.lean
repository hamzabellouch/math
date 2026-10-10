import OAI.Geometry.RCD.Sobolev.RadialCutoffEnergyIdentity
import OAI.Geometry.RCD.Sobolev.ScaledRadialCutoffSobolev
import OAI.Geometry.RCD.Sobolev.ContainingMassPoissonComparison

namespace OAI

/-! # Local strong comparison with the original outer-ball normalization

The cutoff is constructed on the physical space. Its comparison with the
Euclidean radial weight transfers both the sharp recovery energy and the
lower bound, while the exact Poisson identity retains the source errors.
-/

open Set Metric Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.radial_cutoff_strong_comparison {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {S a b R A M Q E : ℝ}
    (hS : 0<S) (hab : a<b) (hbR : b<R) (hRS : R<S)
    (hA : 0≤A) (hM : 0≤M)
    (p : ℕ → X) (r ε α : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    (w q : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hα : ∀ᶠ k in atTop, |α k|≤A)
    (hw : ∀ k, IsConstantLaplacianOn (hausdorff n X) hX.quadratic
      (ball (p k) (R*r k)) (w k) (α k/r k^2))
    (hwg : ∀ᶠ k in atTop, ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (R*r k)),
      r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x≤M^2)
    (hqg : ∀ᶠ k in atTop, ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (R*r k)),
      r k^2*localGamma (hausdorff n X) hX.quadratic (q k) (q k) x≤Q^2)
    (hvalue : Tendsto (fun k => ((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (R*r k),
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k-q k) x)^2 ∂hausdorff n X)
      atTop (𝓝 0))
    (hq : Tendsto (fun k => r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (S*r k), (euclideanNestedCutoff n hab (V k x))^2*
        localGamma (hausdorff n X) hX.quadratic (q k) (q k) x ∂hausdorff n X)
      atTop (𝓝 E))
    (hlower : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      E-δ≤r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
        ∫ x in ball (p k) (S*r k), (euclideanNestedCutoff n hab (V k x))^2*
          localGamma (hausdorff n X) hX.quadratic (w k) (w k) x ∂hausdorff n X) :
    Tendsto (fun k => r k^2*((hausdorff n X).real (ball (p k) (S*r k)))⁻¹*
      ∫ x in ball (p k) (R*r k), (nestedBallCutoff (p k) (a*r k) (b*r k) x)^2*
        localGamma (hausdorff n X) hX.quadratic (w k-q k) (w k-q k) x ∂hausdorff n X)
      atTop (𝓝 0) := by
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let Ω := fun k => ball (p k) (R*r k)
  let m := fun k => μ.real (ball (p k) (S*r k))
  let χ := fun k => nestedBallCutoff (p k) (a*r k) (b*r k)
  let : ∀ k, IsFiniteMeasure (μ.restrict (Ω k)) := fun k => ⟨by
    simpa only [Measure.restrict_apply_univ] using hX.finiteOnBounded (Ω k) isBounded_ball⟩
  have hm (k : ℕ) : 0 < m k := ENNReal.toReal_pos
    (hX.fullSupport _ _ (mul_pos hS (hr k))).ne' (hX.finiteOnBounded _ isBounded_ball).ne
  have hmass (k : ℕ) : μ.real (Ω k) ≤ m k :=
    ENNReal.toReal_mono (hX.finiteOnBounded _ isBounded_ball).ne
      (measure_mono (ball_subset_ball (mul_le_mul_of_nonneg_right hRS.le (hr k).le)))
  choose η hη hηg hηscaled using fun k => scaled_radial_cutoff_sobolev μ hX.quadratic
    (p k) hab (hr k)
  let P : ℕ → ℝ≥0 := fun k => ⟨(b*r k-a*r k)⁻¹,
    inv_nonneg.mpr (sub_pos.mpr (mul_lt_mul_of_pos_right hab (hr k))).le⟩
  have heq (f : ℕ → SobolevSpace μ hX.quadratic) (k : ℕ) :=
    hX.radial_cutoff_energy_identity (p k) hab hbR hRS (hr k) (hV k) (f k)
  have hqerr := hX.radial_cutoff_energy_error_tendsto hS hab hbR p r ε V hr hεlim hV q hqg
  have hwerr := hX.radial_cutoff_energy_error_tendsto hS hab hbR p r ε V hr hεlim hV w hwg
  have hqlim : Tendsto (fun k => r k^2*(m k)⁻¹*
      ∫ x in Ω k, (χ k x)^2*localGamma μ hX.quadratic (q k) (q k) x ∂μ) atTop (𝓝 E) := by
    convert hq.add hqerr using 1
    · funext k
      rw [heq q k]
      ring
    · simp
  have hwl : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      E-δ≤r k^2*(m k)⁻¹*∫ x in Ω k, (χ k x)^2*
        localGamma μ hX.quadratic (w k) (w k) x ∂μ := by
    intro δ hδ
    filter_upwards [hlower (δ/2) (half_pos hδ),
      hwerr.eventually (Ioi_mem_nhds (neg_lt_zero.mpr (half_pos hδ)))] with k hk he
    rw [heq w k,mul_add]
    linarith
  exact poisson_strong_cutoff_comparison_containing_mass μ hX.quadratic Ω m hm hmass r hr
    w q η χ P P (fun k => nestedBallCutoff_lipschitz (p k) (mul_lt_mul_of_pos_right hab (hr k)))
    (fun k => nestedBallCutoff_hasCompactSupport (p k) (mul_lt_mul_of_pos_right hab (hr k)))
    (fun k x => by rw [abs_of_nonneg (nestedBallCutoff_bounds _ _ _ _).1]; exact (nestedBallCutoff_bounds _ _ _ _).2)
    (fun k x => (nestedBallCutoff_bounds _ _ _ _).1) hη hηg
    (fun k => (nestedBallCutoff_tsupport (p k) (mul_lt_mul_of_pos_right hab (hr k))).trans
      (closedBall_subset_ball (mul_lt_mul_of_pos_right hbR (hr k)))) α hw
    hA hM (inv_nonneg.mpr (sub_pos.mpr hab).le) hα hwg
    (Eventually.of_forall fun k => ae_restrict_of_ae (hηscaled k)) hvalue hqlim hwl

end RegularPointCoordinates

end

end OAI
