import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchrodingerForcedDuhamel
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevTaylorRemainder

namespace OAI

/-! # Stability near an approximate physical Schrödinger trajectory

These estimates retain the actual Fourier generator and pointwise Sobolev
nonlinearity.  They apply on a fixed Sobolev ball; no uniform estimate for a
rescaled growing torus is asserted here.
-/

open Set Metric
open scoped NNReal

namespace DefocusingNLS

/-- A bounded residual gives a quantitative comparison with an exact physical solution. -/
theorem exists_sobolevSchrodinger_residual_stability_constant
    (k : ℝ) (hk : 6 < k) (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ≥0, ∀ (u q r : ℝ → FourierL2) (a' b' a b ε : ℝ),
      Icc a b ⊆ Ioo a' b' →
      ContinuousOn u (Ioo a' b') → ContinuousOn q (Ioo a' b') →
      ContinuousOn r (Ioo a' b') →
      (∀ t ∈ Ioo a' b', HasDerivAt (fun s => lowerSobolevInclusion (u s))
        (lowerSobolevGenerator (u t) -
          Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (u t))) t) →
      (∀ t ∈ Ioo a' b', HasDerivAt (fun s => lowerSobolevInclusion (q s))
        (lowerSobolevGenerator (q t) -
          Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (q t)) +
            lowerSobolevInclusion (r t)) t) →
      (∀ t ∈ Icc a b, ‖u t‖ ≤ R) → (∀ t ∈ Icc a b, ‖q t‖ ≤ R) →
      (∀ t ∈ Icc a b, ‖r t‖ ≤ ε) →
      ∀ t ∈ Icc a b, dist (u t) (q t) ≤
        gronwallBound (dist (u a) (q a)) K ε (t - a) := by
  obtain ⟨_, K, _, hK, _, hlip⟩ := exists_schrodingerInteractionField_ball_bounds k hk m R hR
  refine ⟨⟨K, hK⟩, ?_⟩
  intro u q r a' b' a b ε hsub huc hqc hrc hu hq hub hqb hrb t ht
  let v := inverseSchrodingerCurve u
  let w := inverseSchrodingerCurve q
  have hv : ∀ s ∈ Icc a b,
      HasDerivAt v (schrodingerInteractionField k hk m s (v s)) s :=
    fun s hs => hasDerivAt_inverseSchrodingerCurve k hk m u a' b' s huc hu (hsub hs)
  have hw : ∀ s ∈ Icc a b,
      HasDerivAt w (schrodingerInteractionField k hk m s (w s) +
        schrodingerFlow (-s) (r s)) s :=
    fun s hs => hasDerivAt_residual_inverseSchrodingerCurve k hk m q r a' b' s hqc hrc hq
      (hsub hs)
  have h := dist_le_of_approx_trajectories_ODE_of_mem
    (v := schrodingerInteractionField k hk m) (s := fun _ => closedBall 0 R)
    (K := (⟨K, hK⟩ : ℝ≥0)) (f := v) (g := w)
    (f' := fun s => schrodingerInteractionField k hk m s (v s))
    (g' := fun s => schrodingerInteractionField k hk m s (w s) +
      schrodingerFlow (-s) (r s)) (εf := 0) (εg := ε)
    (δ := dist (v a) (w a))
    (fun s hs => LipschitzOnWith.of_dist_le_mul (fun f hf g hg => by
      rw [dist_eq_norm, dist_eq_norm]
      exact hlip s f g (by simpa using hf) (by simpa using hg)))
    (fun s hs => (hv s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hv s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (fun s hs => by simp)
    (fun s hs => by simpa [v, inverseSchrodingerCurve] using hub s (Ico_subset_Icc_self hs))
    (fun s hs => (hw s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hw s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (fun s hs => by simpa [dist_eq_norm] using hrb s (Ico_subset_Icc_self hs))
    (fun s hs => by simpa [w, inverseSchrodingerCurve] using hqb s (Ico_subset_Icc_self hs))
    le_rfl t ht
  simpa only [v, w, inverseSchrodingerCurve, LinearIsometry.dist_map, zero_add] using h

/-- Subtracting an approximate profile gives the actual linearized equation plus its
quadratic Taylor remainder and the negative profile residual. -/
theorem hasDerivAt_sobolevProfilePerturbation
    (k : ℝ) (hk : 6 < k) (m : ℕ) (u q : ℝ → FourierL2) (r : FourierL2) (t : ℝ)
    (hu : HasDerivAt (fun s => lowerSobolevInclusion (u s))
      (lowerSobolevGenerator (u t) -
        Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (u t))) t)
    (hq : HasDerivAt (fun s => lowerSobolevInclusion (q s))
      (lowerSobolevGenerator (q t) -
        Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (q t)) +
          lowerSobolevInclusion r) t) :
    HasDerivAt (fun s => lowerSobolevInclusion (u s - q s))
      (lowerSobolevGenerator (u t - q t) -
        Complex.I • lowerSobolevInclusion
          (fderiv ℝ (sobolevOddPower k hk m) (q t) (u t - q t) +
            sobolevNonlinearRemainder k hk m (q t) (u t - q t)) -
        lowerSobolevInclusion r) t := by
  have hnonlin : fderiv ℝ (sobolevOddPower k hk m) (q t) (u t - q t) +
      sobolevNonlinearRemainder k hk m (q t) (u t - q t) =
        sobolevOddPower k hk m (u t) - sobolevOddPower k hk m (q t) := by
    unfold sobolevNonlinearRemainder
    have hsum : q t + (u t - q t) = u t := by abel
    rw [hsum]
    abel
  have h := hu.sub hq
  rw [hnonlin]
  simp only [map_sub, smul_sub]
  convert h using 1; abel

end DefocusingNLS

end OAI
