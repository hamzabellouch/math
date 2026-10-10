import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevDuhamelIntegral

namespace OAI

/-! # Quantitative continuous dependence on Sobolev balls -/

open Filter Topology Set Metric
open scoped NNReal

namespace DefocusingNLS

/-- On a fixed norm ball, one exponential bound applies to all interaction trajectories. -/
theorem exists_sobolevInteraction_gronwall_constant
    (k : ℝ) (hk : 6 < k) (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ≥0, ∀ (v w : ℝ → FourierL2) (a b : ℝ),
      (∀ t ∈ Icc a b, HasDerivAt v (schrodingerInteractionField k hk m t (v t)) t) →
      (∀ t ∈ Icc a b, HasDerivAt w (schrodingerInteractionField k hk m t (w t)) t) →
      (∀ t ∈ Icc a b, ‖v t‖ ≤ R) → (∀ t ∈ Icc a b, ‖w t‖ ≤ R) →
      ∀ t ∈ Icc a b, dist (v t) (w t) ≤ dist (v a) (w a) * Real.exp (K * (t - a)) := by
  obtain ⟨_, K, _, hK, _, hlip⟩ :=
    exists_schrodingerInteractionField_ball_bounds k hk m R hR
  refine ⟨⟨K, hK⟩, ?_⟩
  intro v w a b hv hw hvb hwb
  apply dist_le_of_trajectories_ODE_of_mem
    (v := schrodingerInteractionField k hk m) (s := fun _ => closedBall 0 R)
    (K := ⟨K, hK⟩)
  · intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro f hf g hg
    rw [dist_eq_norm, dist_eq_norm]
    change ‖schrodingerInteractionField k hk m t f -
      schrodingerInteractionField k hk m t g‖ ≤ K * ‖f - g‖
    exact hlip t f g (by simpa using hf) (by simpa using hg)
  · intro t ht
    exact (hv t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hv t (Ico_subset_Icc_self ht)).hasDerivWithinAt
  · intro t ht
    simpa using hvb t (Ico_subset_Icc_self ht)
  · intro t ht
    exact (hw t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hw t (Ico_subset_Icc_self ht)).hasDerivWithinAt
  · intro t ht
    simpa using hwb t (Ico_subset_Icc_self ht)
  · exact le_rfl

/-- The same exponential estimate holds for strong physical Schrödinger solutions. -/
theorem exists_sobolevSchrodinger_gronwall_constant
    (k : ℝ) (hk : 6 < k) (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ≥0, ∀ (u v : ℝ → FourierL2) (a' b' a b : ℝ),
      Icc a b ⊆ Ioo a' b' →
      ContinuousOn u (Ioo a' b') → ContinuousOn v (Ioo a' b') →
      (∀ t ∈ Ioo a' b', HasDerivAt (fun s => lowerSobolevInclusion (u s))
        (lowerSobolevGenerator (u t) -
          Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (u t))) t) →
      (∀ t ∈ Ioo a' b', HasDerivAt (fun s => lowerSobolevInclusion (v s))
        (lowerSobolevGenerator (v t) -
          Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (v t))) t) →
      (∀ t ∈ Icc a b, ‖u t‖ ≤ R) → (∀ t ∈ Icc a b, ‖v t‖ ≤ R) →
      ∀ t ∈ Icc a b, dist (u t) (v t) ≤ dist (u a) (v a) * Real.exp (K * (t - a)) := by
  obtain ⟨K, hK⟩ := exists_sobolevInteraction_gronwall_constant k hk m R hR
  refine ⟨K, ?_⟩
  intro u v a' b' a b hsub huc hvc hu hv hub hvb t ht
  have h := hK (inverseSchrodingerCurve u) (inverseSchrodingerCurve v) a b
    (fun s hs => hasDerivAt_inverseSchrodingerCurve k hk m u a' b' s huc hu (hsub hs))
    (fun s hs => hasDerivAt_inverseSchrodingerCurve k hk m v a' b' s hvc hv (hsub hs))
    (fun s hs => by simpa [inverseSchrodingerCurve] using hub s hs)
    (fun s hs => by simpa [inverseSchrodingerCurve] using hvb s hs) t ht
  simpa only [inverseSchrodingerCurve, LinearIsometry.dist_map] using h

end DefocusingNLS

end OAI
