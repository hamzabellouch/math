import OAI.Geometry.RCD.Harmonic.DyadicRadialTargets
import OAI.Geometry.RCD.Coordinates.AffineFitDifference

namespace OAI

/-! # Center differences of the actual dyadic radial fits -/

open Set Metric MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Both fits concern the same local radial derivative. The change of
outer distance cutoff introduces no extra term in their center difference. -/
theorem canonical_affine_center_difference {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [IsFiniteMeasureOnCompacts (hausdorff n X)]
    (hmean : LocalHarmonicL2MeanValueInput hX) (hn : 2 ≤ n) {κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ {κ r0 B J C L : ℝ} {p : X}
      (S : DyadicDistanceSources (hausdorff n X) hX.quadratic n κ p r0)
      (T : DyadicDistanceReplacements (hausdorff n X) hX.quadratic S B J C)
      (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
      (hbase : ∀ i j, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (distanceSourceRadius r0 i / 64)),
        localGamma (hausdorff n X) hX.quadratic (u j) (u j) x ≤ L ^ 2)
      (v : X → Euclidean n) (i j : ℕ), i ≤ j →
      -κ₀ ≤ K * (distanceSourceRadius r0 j / 64) ^ 2 →
      (∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
        (ball p (distanceSourceRadius r0 j / 64)) (u k)) →
      ContinuousOn v (ball p (distanceSourceRadius r0 j / 64)) →
      (∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) =ᵐ[
        (hausdorff n X).restrict (ball p (distanceSourceRadius r0 j / 64))] fun x => v x k) →
    ∀ (b ai aj : Euclidean n) (ci cj : ℝ),
      let μ := hausdorff n X
      let ri := distanceSourceRadius r0 i / 64
      let rj := distanceSourceRadius r0 j / 64
      let hi := ne_of_lt (hX.finiteOnBounded (ball p ri) isBounded_ball)
      let hj := ne_of_lt (hX.finiteOnBounded (ball p rj) isBounded_ball)
      affineProjection μ hX.quadratic u (ball p ri) hi (dyadicRadialTarget hX T u hbase i b) =
        affineCoordinateMap μ hX.quadratic u (ball p ri) hi (ci, ai) →
      affineProjection μ hX.quadratic u (ball p rj) hj (dyadicRadialTarget hX T u hbase j b) =
        affineCoordinateMap μ hX.quadratic u (ball p rj) hj (cj, aj) →
      |(ci + ⟪v p, ai⟫_ℝ) - (cj + ⟪v p, aj⟫_ℝ)| ≤
        M * (Real.sqrt (μ.real (ball p ri)) / Real.sqrt (μ.real (ball p rj))) *
          (ri * dyadicRadialFit hX T u L hbase i b) +
        M * (rj * dyadicRadialFit hX T u L hbase j b) := by
  obtain ⟨M, hM, hdiff⟩ := affineFit_center_difference hX hmean hn hκ₀
  refine ⟨M, hM, ?_⟩
  intro κ r0 B J C L p S T u hbase v i j hij hcurv hu hv hrep b ai aj ci cj
  dsimp only
  intro hfi hfj
  let μ := hausdorff n X
  let ri := distanceSourceRadius r0 i / 64
  let rj := distanceSourceRadius r0 j / 64
  have hri : 0 < ri := div_pos (distanceSourceRadius_pos S.radius_pos i) (by norm_num)
  have hrj : 0 < rj := div_pos (distanceSourceRadius_pos S.radius_pos j) (by norm_num)
  have hrji : rj ≤ ri := div_le_div_of_nonneg_right
    (distanceSourceRadius_antitone S.radius_pos.le hij) (by norm_num)
  have hη : SobolevSpace.toLp μ hX.quadratic (T.cutoff j).sobolev =ᵐ[μ.restrict (ball p rj)]
      fun _ => (1 : ℝ) := by
    filter_upwards [ae_restrict_of_ae (T.cutoff j).representative,
      ae_restrict_mem measurableSet_ball] with x hx hxr
    exact hx.trans ((T.cutoff j).one x ((ball_subset_ball
      (show rj ≤ 4 * distanceSourceRadius r0 j by dsimp only [rj] at hrj ⊢; linarith)) hxr))
  have htarget := dyadicRadialTarget_restrict hX T u hbase hij b
  dsimp only at htarget
  have hfj' : affineProjection μ hX.quadratic u (ball p rj)
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (localL2Restriction μ (ball p ri) (ball p rj) (ball_subset_ball hrji)
        (dyadicRadialTarget hX T u hbase i b)) =
      affineCoordinateMap μ hX.quadratic u (ball p rj)
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (cj, aj) := by
    rw [htarget]
    exact hfj
  have hb := hdiff p rj ri hrj hrji hcurv u v hu hv hrep (T.cutoff j).sobolev hη
    (dyadicRadialTarget hX T u hbase i b) ci cj ai aj hfi hfj'
  rw [htarget] at hb
  have hnorm (k : ℕ) :
      ‖normalizeLocalL2 μ (ball p (distanceSourceRadius r0 k / 64))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (affineResidual μ hX.quadratic u (ball p (distanceSourceRadius r0 k / 64))
          (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (dyadicRadialTarget hX T u hbase k b))‖ =
      (distanceSourceRadius r0 k / 64) * dyadicRadialFit hX T u L hbase k b := by
    unfold dyadicRadialFit radialFitError dyadicRadialTarget
    change _ = (distanceSourceRadius r0 k / 64) * (_ / (distanceSourceRadius r0 k / 64))
    field_simp [(distanceSourceRadius_pos S.radius_pos k).ne']
    rfl
  rw [hnorm i, hnorm j] at hb
  exact hb

end RegularPointCoordinates

end

end OAI
