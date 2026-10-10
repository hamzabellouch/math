import OAI.Geometry.RCD.Harmonic.PinchingPairingRestriction
import OAI.Geometry.RCD.Harmonic.FullMassPinching

namespace OAI

/-! # Full Bochner mass from the centered Poisson pair estimates -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] [IsFiniteMeasureOnCompacts μ] in
/-- A local scalar multiple of the common cutoff is the indicated constant. -/
theorem local_cutoff_smul_representative (S : Set X) (eta : SobolevSpace μ hQ)
    (heta : SobolevSpace.toLp μ hQ eta =ᵐ[μ.restrict S] fun _ => (1 : ℝ)) (c : ℝ) :
    SobolevSpace.toLp μ hQ (c • eta) =ᵐ[μ.restrict S] fun _ => c := by
  change SobolevSpace.toLpCLM μ hQ (c • eta) =ᵐ[μ.restrict S] _
  rw [map_smul]
  filter_upwards [heta, ae_restrict_of_ae (Lp.coeFn_smul c (SobolevSpace.toLp μ hQ eta))] with x hx hc
  change (c • SobolevSpace.toLp μ hQ eta) x = c
  simp only [hc, Pi.smul_apply, smul_eq_mul, hx, mul_one]

/-- Centering and exact frame changes preserve every input to the full
mass estimate. The mass tested here is the actual joint Poisson measure. -/
theorem centered_poisson_directional_mass {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (f : Fin 2 → SobolevSpace μ hQ)
    (eta : SobolevSpace μ hQ) (z delta b : Euclidean n) (c : ℝ)
    (F N : Euclidean n ≃L[ℝ] Euclidean n)
    (Hpair : Euclidean n →L[ℝ] SobolevSpace μ hQ)
    (M : PositiveBilinearMeasure X (Euclidean (n + 2)))
    {p : X} {r rho C κ beta P H D : ℝ} {L : ℝ≥0}
    (chi : GoodLaplacianCutoff μ hQ p rho C)
    (hrho : 0 < rho) (hroom : rho < r)
    (hC : 0 ≤ C) (hκ : 0 ≤ κ) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hvol : 0 < μ.real (ball p rho))
    (heta : SobolevSpace.toLp μ hQ eta =ᵐ[μ.restrict (closedBall p (2 * rho))] fun _ => (1 : ℝ))
    (hN : IsExactMeanNormalization μ hQ
      ((centeredSobolevMap μ hQ u eta z).comp F.toContinuousLinearMap)
      (ball p rho) measurableSet_ball N)
    (G : ∀ v, LocalHarmonicEnergy μ hQ (sobolevColumnMap μ hQ (poissonSpan μ hQ u f)) M κ p r L v)
    (hgradient : ∀ᵐ x ∂μ.restrict (closedBall p (2 * rho)),
      localGamma μ hQ (f 1 - f 0 - (c • eta + centeredSobolevMap μ hQ u eta z (F b)))
        (f 1 - f 0 - (c • eta + centeredSobolevMap μ hQ u eta z (F b))) x ≤ beta)
    (hcoordinates : ∀ v, ∀ᵐ x ∂μ.restrict (closedBall p (2 * rho)),
      localGamma μ hQ (centeredSobolevMap μ hQ u eta z (F (N v)))
        (centeredSobolevMap μ hQ u eta z (F (N v))) x ≤ H * ‖v‖ ^ 2)
    (hrep : ∀ v, SobolevSpace.toLp μ hQ (Hpair v) =ᵐ[μ.restrict (ball p rho)]
      localGamma μ hQ (f 1 - f 0) (centeredSobolevMap μ hQ u eta z (F (N v))))
    (herror : ∀ v, ‖normalizeLocalL2 μ (ball p rho) (ne_of_lt (measure_ball_lt_top (μ := μ)))
      (SobolevSpace.restrictLp μ hQ (ball p rho) (Hpair v) -
        ⟪N.toContinuousLinearMap.adjoint delta, v⟫_ℝ •
          restrictedOne μ (ball p rho) (ne_of_lt (measure_ball_lt_top (μ := μ))))‖ ≤ D * ‖v‖)
    (hraw :
      let a : Euclidean (n + 2) := EuclideanSpace.single (Fin.natAdd n (1 : Fin 2)) 1 -
        EuclideanSpace.single (Fin.natAdd n (0 : Fin 2)) 1
      ⟪a, M.massOperator (ball p rho) a⟫_ℝ ≤ P) :
    let v := poissonCoordinateLift (F (N (N.toContinuousLinearMap.adjoint delta)))
    let Q := ((C / rho ^ 2) / 2 + κ) * μ.real (closedBall p (2 * rho))
    ⟪v, M.massOperator (ball p rho) v⟫_ℝ ≤
      4 * (P + Q * beta) + 4 * (Q * H) * (D ^ 2 + beta) := by
  let U := sobolevColumnMap μ hQ (poissonSpan μ hQ u f)
  let A := (poissonCoordinateLiftLinear n).comp (F.toContinuousLinearMap.comp N.toContinuousLinearMap)
  let a : Euclidean (n + 2) := EuclideanSpace.single (Fin.natAdd n (1 : Fin 2)) 1 -
    EuclideanSpace.single (Fin.natAdd n (0 : Fin 2)) 1
  have ha : U a = f 1 - f 0 := by
    rw [map_sub]
    exact congrArg₂ HSub.hSub (poissonSpanMap_right μ hQ u f 1) (poissonSpanMap_right μ hQ u f 0)
  have hA (v : Euclidean n) : U (A v) = sobolevColumnMap μ hQ u (F (N v)) :=
    poissonSpanMap_lift μ hQ u f (F (N v))
  have hAb : U (A (N.symm b)) = sobolevColumnMap μ hQ u (F b) := by
    rw [hA, N.apply_symm_apply]
  have hclosed : ball p rho ⊆ closedBall p (2 * rho) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have heta' := ae_restrict_of_ae_restrict_of_subset hclosed heta
  have hnormal : sobolevMeanGram μ hQ (U.comp A) (ball p rho) measurableSet_ball =
      ContinuousLinearMap.id ℝ (Euclidean n) := by
    have hcomp : U.comp A = (sobolevColumnMap μ hQ u).comp (F.toContinuousLinearMap.comp N.toContinuousLinearMap) := by
      apply ContinuousLinearMap.ext
      intro v
      exact hA v
    rw [hcomp]
    exact uncentered_frame_normalization μ hQ u eta z F N _ measurableSet_ball heta' hN
  have hgrad : ∀ᵐ x ∂μ.restrict (closedBall p (2 * rho)),
      localGamma μ hQ (U (a - A (N.symm b))) (U (a - A (N.symm b))) x ≤ beta := by
    have heq : U (a - A (N.symm b)) -
        (f 1 - f 0 - (c • eta + centeredSobolevMap μ hQ u eta z (F b))) =
        (c - ⟪z, F b⟫_ℝ) • eta := by
      rw [map_sub, ha, hAb]
      simp only [centeredSobolevMap_apply, centeredAffineSobolev]
      module
    have he := localGamma_self_eq_of_constant_difference μ hQ (closedBall p (2 * rho))
      (U (a - A (N.symm b))) (f 1 - f 0 - (c • eta + centeredSobolevMap μ hQ u eta z (F b)))
      (c - ⟪z, F b⟫_ℝ) (by
        rw [heq]
        exact local_cutoff_smul_representative μ hQ _ eta heta _)
    filter_upwards [he, hgradient] with x hx hb
    exact hx.trans_le hb
  have hcoord (v : Euclidean n) : ∀ᵐ x ∂μ.restrict (closedBall p (2 * rho)),
      localGamma μ hQ (U (A v)) (U (A v)) x ≤ H * ‖v‖ ^ 2 := by
    rw [hA]
    have he := localGamma_self_eq_of_constant_difference μ hQ (closedBall p (2 * rho))
      (centeredSobolevMap μ hQ u eta z (F (N v))) (sobolevColumnMap μ hQ u (F (N v)))
      (-⟪z, F (N v)⟫_ℝ) (centered_sobolev_constant_difference μ hQ _ u eta z (F (N v)) heta)
    filter_upwards [he, hcoordinates v] with x hx hb
    exact hx.symm.trans_le hb
  have hpair (v : Euclidean n) : SobolevSpace.toLp μ hQ (Hpair v) =ᵐ[μ.restrict (ball p rho)]
      localGamma μ hQ (U a) ((U.comp A) v) := by
    rw [ContinuousLinearMap.comp_apply, ha, hA]
    have he := localGamma_eq_of_constant_difference μ hQ (ball p rho)
      (centeredSobolevMap μ hQ u eta z (F (N v))) (sobolevColumnMap μ hQ u (F (N v)))
      (f 1 - f 0) (-⟪z, F (N v)⟫_ℝ)
      (centered_sobolev_constant_difference μ hQ _ u eta z (F (N v)) heta')
    filter_upwards [hrep v, he,
      ae_restrict_of_ae (localGamma_comm μ hQ (f 1 - f 0) (centeredSobolevMap μ hQ u eta z (F (N v)))),
      ae_restrict_of_ae (localGamma_comm μ hQ (sobolevColumnMap μ hQ u (F (N v))) (f 1 - f 0))]
      with x h1 h2 h3 h4
    exact h1.trans (h3.trans (h2.trans h4))
  exact directional_mass_from_pairing_bounds μ hQ U A Hpair M a (N.symm b)
    (N.toContinuousLinearMap.adjoint delta) chi hrho hroom hC hκ hH hD hvol
    (ne_of_lt (measure_ball_lt_top (μ := μ))) (ne_of_gt (ENNReal.toReal_pos_iff.mp hvol).1)
    hnormal G hgrad hcoord hpair herror hraw

end RegularPointCoordinates

end

end OAI
