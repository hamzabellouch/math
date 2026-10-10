import OAI.Geometry.RCD.Harmonic.HarmonicMeanValueInput
import OAI.Geometry.RCD.Harmonic.LocalConstantHarmonic
import OAI.Geometry.RCD.Harmonic.ColumnRepresentatives
import OAI.Geometry.RCD.Coordinates.AffineFitPerturbation

namespace OAI

/-! # Uniform evaluation of affine fits at their center -/

open Set Metric MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [BorelSpace X] [ProperSpace X] in
theorem affineSobolev_representative (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    {n : ℕ} (u : Fin n → SobolevSpace μ hQ) (s : Set X) (v : X → Euclidean n)
    (hu : ∀ i, SobolevSpace.toLp μ hQ (u i) =ᵐ[μ.restrict s] fun x => v x i)
    (η : SobolevSpace μ hQ) (hη : SobolevSpace.toLp μ hQ η =ᵐ[μ.restrict s] fun _ => (1 : ℝ))
    (c : ℝ) (a : Euclidean n) :
    SobolevSpace.toLp μ hQ (c • η + sobolevColumnMap μ hQ u a) =ᵐ[μ.restrict s]
      fun x => c + ⟪v x, a⟫_ℝ := by
  change SobolevSpace.toLpCLM μ hQ (c • η + sobolevColumnMap μ hQ u a) =ᵐ[μ.restrict s] _
  rw [map_add, map_smul]
  change (c • SobolevSpace.toLp μ hQ η + SobolevSpace.toLp μ hQ (sobolevColumnMap μ hQ u a))
    =ᵐ[μ.restrict s] _
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_add (c • SobolevSpace.toLp μ hQ η)
      (SobolevSpace.toLp μ hQ (sobolevColumnMap μ hQ u a))),
    ae_restrict_of_ae (Lp.coeFn_smul c (SobolevSpace.toLp μ hQ η)), hη,
    sobolevColumnMap_representative μ hQ u s v hu a] with x hadd hsmul hconst hcol
  rw [hadd]
  simp only [Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul, hconst, mul_one, hcol]

/-- Moser's mean-value estimate bounds affine evaluation without requiring
a choice of unique affine coefficients. -/
theorem affine_evaluation_of_mean_value {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
    (hmean : LocalHarmonicL2MeanValueInput hX) (hn : 2 ≤ n) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : X) (r : ℝ), 0 < r → -κ ≤ K * r ^ 2 →
    ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
      (∀ i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p r) (u i)) →
      ContinuousOn v (ball p r) →
      (∀ i, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u i) =ᵐ[
        (hausdorff n X).restrict (ball p r)] fun x => v x i) →
      ∀ η : SobolevSpace (hausdorff n X) hX.quadratic,
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic η =ᵐ[
          (hausdorff n X).restrict (ball p r)] fun _ => (1 : ℝ)) →
      ∀ (c : ℝ) (a : Euclidean n),
        |c + ⟪v p, a⟫_ℝ| ≤ C *
          ‖normalizeLocalL2 (hausdorff n X) (ball p r)
            (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
            (affineCoordinateMap (hausdorff n X) hX.quadratic u (ball p r)
              (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c, a))‖ := by
  obtain ⟨C, hC, hcenter⟩ := hmean.center_bound hn hκ
  refine ⟨C, hC, ?_⟩
  intro p r hr hcurv u v hu hv hrep η hη c a
  let μ := hausdorff n X
  let F := c • η + sobolevColumnMap μ hX.quadratic u a
  have hηharm := isSobolevHarmonicOn_of_local_constant μ hX.quadratic
    (ball p r) measurableSet_ball η 1 hη
  have hFharm : IsSobolevHarmonicOn μ hX.quadratic (ball p r) F :=
    (hηharm.smul μ hX.quadratic c).add μ hX.quadratic
      (IsSobolevHarmonicOn.linearCombination μ hX.quadratic hu a)
  have hFrep := affineSobolev_representative μ hX.quadratic u (ball p r) v hrep η hη c a
  have hFcont : ContinuousOn (fun x => c + ⟪v x, a⟫_ℝ) (ball p r) :=
    continuousOn_const.add (hv.inner continuousOn_const)
  have hb := hcenter p r hr hcurv F (fun x => c + ⟪v x, a⟫_ℝ) hFharm hFcont hFrep
  have hrest : SobolevSpace.restrictLp μ hX.quadratic (ball p r) F =
      affineCoordinateMap μ hX.quadratic u (ball p r)
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball)) (c, a) := by
    rw [affineCoordinateMap_apply]
    change SobolevSpace.restrictLp μ hX.quadratic (ball p r)
      (c • η + sobolevColumnMap μ hX.quadratic u a) = _
    rw [map_add, map_smul, restrictLp_eq_one_of_representative μ hX.quadratic η _ _ hη]
  change |c + ⟪v p, a⟫_ℝ| ≤ C * ‖normalizeLocalL2 μ (ball p r) _
    (SobolevSpace.restrictLp μ hX.quadratic (ball p r) F)‖ at hb
  rwa [hrest] at hb

end RegularPointCoordinates

end

end OAI
