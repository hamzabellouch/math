import OAI.Geometry.RCD.Harmonic.HarmonicMeanConstruction

namespace OAI

/-! # Harmonic mean bounds on every strict interior fraction

The fixed half-ball estimate and nearby-ball volume comparison suffice.
The constants depend only on the curvature bound and interior fraction.
-/

open Set Metric Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
theorem harmonic_target_norm_le_of_ball_volume {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) {p q : X} {R r D : ℝ}
    (hR : 0 < R) (hr : 0 < r) (hD : 0 ≤ D)
    (hsub : ball q r ⊆ ball p R)
    (hvol : (hausdorff n X).real (ball p R) ≤ D*(hausdorff n X).real (ball q r))
    (w : SobolevSpace (hausdorff n X) hX.quadratic) :
    harmonicTargetNorm hX q r w ≤ Real.sqrt D*harmonicTargetNorm hX p R w := by
  have hfinR := (hX.finiteOnBounded (ball p R) isBounded_ball).ne
  have hfinr := (hX.finiteOnBounded (ball q r) isBounded_ball).ne
  have hposR := ENNReal.toReal_pos (hX.fullSupport p R hR).ne' hfinR
  have hposr := ENNReal.toReal_pos (hX.fullSupport q r hr).ne' hfinr
  have hnormR : (harmonicTargetNorm hX p R w)^2 =
      ((hausdorff n X).real (ball p R))⁻¹*
        ∫ x in ball p R, (SobolevSpace.toLp (hausdorff n X) hX.quadratic w x)^2
          ∂hausdorff n X := normalized_sobolev_mean_sq _ _ _ hfinR w
  have hnormr : (harmonicTargetNorm hX q r w)^2 =
      ((hausdorff n X).real (ball q r))⁻¹*
        ∫ x in ball q r, (SobolevSpace.toLp (hausdorff n X) hX.quadratic w x)^2
          ∂hausdorff n X := normalized_sobolev_mean_sq _ _ _ hfinr w
  have hb := average_nonneg_le_of_subset (hausdorff n X) hsub hposr hposR
    (Lp.memLp (SobolevSpace.toLp (hausdorff n X) hX.quadratic w)).integrable_sq.integrableOn
    (fun _ => sq_nonneg _) (sq_nonneg (harmonicTargetNorm hX p R w)) hvol hnormR.ge
  rw [← hnormr] at hb
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rwa [mul_pow,Real.sq_sqrt hD]

theorem harmonic_interior_mean_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    (hmean : LocalHarmonicL2MeanValueInput hX) {a τ : ℝ}
    (ha : 0≤a) (hτ : 0<τ) (hτ1 : τ<1) :
    ∃ C : ℝ, 1≤C ∧ ∀ (p : X) (R : ℝ), 0<R → -a≤K*R^2 →
      ∀ u : SobolevSpace (hausdorff n X) hX.quadratic,
        IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p R) u →
        ∀ᵐ x ∂(hausdorff n X).restrict (ball p (τ*R)),
          |SobolevSpace.toLp (hausdorff n X) hX.quadratic u x|≤
            C*harmonicTargetNorm hX p R u := by
  let := hX.separable
  let δ := (1-τ)/2
  have hδ : 0<δ := by dsimp only [δ]; linarith
  have hδ1 : δ≤1 := by dsimp only [δ]; linarith
  obtain ⟨D,hD,hvolume⟩ := hX.rescaled_ball_volume_factor hn ha hδ hδ1
  obtain ⟨M,hM,hbound⟩ := hmean hn a ha
  let C := 1+M*Real.sqrt D
  have hM0 : 0≤M := zero_le_one.trans hM
  have hD0 : 0≤D := zero_le_one.trans hD
  refine ⟨C,by
    dsimp only [C]
    exact le_add_of_nonneg_right (mul_nonneg hM0 (Real.sqrt_nonneg _)),?_⟩
  intro p R hR hcurv u hu
  have hδR : 0<δ*R := mul_pos hδ hR
  have hcurvsmall : -a≤K*(δ*R)^2 := by
    have hsq : δ^2≤1 := by nlinarith [hδ]
    have hm := mul_le_mul_of_nonneg_right hcurv (sq_nonneg δ)
    have hh := mul_le_mul_of_nonneg_left hsq ha
    nlinarith only [hm,hh]
  have hlocal (q : ball p (τ*R)) :
      ∀ᵐ x ∂(hausdorff n X).restrict (ball q.val (δ*R/2)),
      |SobolevSpace.toLp (hausdorff n X) hX.quadratic u x|≤C*harmonicTargetNorm hX p R u := by
    have hq : dist q.val p<τ*R := q.property
    have hqR : dist q.val p≤R := by nlinarith
    have hsub : ball q.val (δ*R) ⊆ ball p R := by
      apply ball_subset_ball'
      dsimp only [δ]
      nlinarith
    have hnorm := harmonic_target_norm_le_of_ball_volume hX hR hδR hD0 hsub
      (hvolume p R hR hcurv q.val hqR) u
    filter_upwards [hbound q.val (δ*R) hδR hcurvsmall u (hu.mono _ _ hsub)] with x hx
    have hm := mul_le_mul_of_nonneg_left hnorm hM0
    have hT : 0≤harmonicTargetNorm hX p R u := norm_nonneg _
    exact hx.trans (by dsimp only [C]; nlinarith only [hm,hT])
  let U : ball p (τ*R) → Set X := fun q => ball q.val (δ*R/2)
  obtain ⟨s,hs,hcover⟩ := (HereditarilyLindelofSpace.isLindelof (ball p (τ*R))).elim_countable_subcover
    U (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (by positivity)⟩)
  exact ae_restrict_of_ae_restrict_of_subset hcover
    ((ae_restrict_biUnion_iff U hs _).mpr (fun q _ => hlocal q))

end RegularPointCoordinates

end

end OAI
