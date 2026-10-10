import OAI.Geometry.RCD.Sobolev.RadialCutoffIdentity

namespace OAI

/-!
# Source mass from the squared-distance weak identity

Gigli (2015), Corollary 5.15, equation (5.29), supplies the local positive
Laplacian defect of squared distance. Applying that defect to the explicit
radial test gives this volume-drop bound directly. The only calculus premise
is the actual radial pairing, obtained from the distance eikonal identity;
no mass bound or radial distribution identity is assumed.
-/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X]

theorem radialPowerRep_bounds {n r R : ℝ} (hn : 0 < n) (hr : 0 < r)
    (hrR : r ≤ R) (c x : X) :
    0 ≤ radialPowerRep n r R c x ∧
      radialPowerRep n r R c x ≤ (r ^ (-n) - R ^ (-n)) / n := by
  have hm : Monotone (radialPowerPrimitive n r R) :=
    monotone_of_hasDerivAt_nonneg (fun s => radialPowerPrimitive_hasDerivAt n R s hr)
      (fun s => (radialPowerWeight_bounds hn hr s).1)
  have ht0 : 0 ≤ positiveClip (R - r) (inwardDistance c R x) :=
    le_min (le_max_right _ _) (sub_nonneg.mpr hrR)
  have htt : positiveClip (R - r) (inwardDistance c R x) ≤ R - r := min_le_right _ _
  constructor
  · change 0 ≤ radialPowerPrimitive n r R (positiveClip (R - r) (inwardDistance c R x))
    simpa only [radialPowerPrimitive_zero] using hm ht0
  · have he := radialPowerPrimitive_formula hn hr (sub_nonneg.mpr hrR) le_rfl
    rw [sub_sub_cancel] at he
    exact (hm htt).trans_eq he

variable [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

omit [MeasurableSpace X] [BorelSpace X] [ProperSpace X] in
/-- The radial test has support strictly inside any larger working ball. -/
theorem radialPowerRep_tsupport {n r R T : ℝ} (hrR : r ≤ R) (hRT : R < T) (c : X) :
    tsupport (radialPowerRep n r R c) ⊆ ball c T := by
  have hs : tsupport (radialPowerRep n r R c) ⊆ closedBall c R := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hnot
    apply hx
    apply radialPowerRep_zero hrR
    exact (lt_of_not_ge (show ¬ dist c x ≤ R by simpa only [mem_closedBall, dist_comm] using hnot)).le
  exact hs.trans (closedBall_subset_ball hRT)

/-- The positive squared-distance Laplacian defect has an annular volume
budget, with an explicit coefficient and curvature term. -/
theorem radial_source_cutoff_mass_le {n r R T curvature : ℝ}
    (hn : 0 < n) (hr : 0 < r) (hrR : r < R) (hRT : R < T)
    (hcurvature : 0 ≤ curvature) (c : X) (q : SobolevSpace μ hQ)
    (σ : Measure X) [IsFiniteMeasure σ]
    (hdefect : ∀ (ψ : SobolevSpace μ hQ) (v : X → ℝ) (C : ℝ≥0),
      LipschitzWith C v → HasCompactSupport v → tsupport v ⊆ ball c T →
      SobolevSpace.toLp μ hQ ψ =ᵐ[μ] v →
      energyForm μ hQ q ψ + (n + curvature) * (∫ x, v x ∂μ) = ∫ x, v x ∂σ)
    (hpair : ∀ᵐ x ∂μ, x ∈ ball c R →
      localGamma μ hQ q (inwardSobolev μ hQ c R) x = -dist c x)
    (hsphere : μ (sphere c r) = 0) :
    ((r ^ (-n) - R ^ (-n)) / n) * σ.real (ball c r) ≤
      r ^ (-n) * μ.real (ball c r) - R ^ (-n) * μ.real (ball c R) +
      curvature * ((r ^ (-n) - R ^ (-n)) / n) * μ.real (ball c R) := by
  let v := radialPowerRep n r R c
  let H := (r ^ (-n) - R ^ (-n)) / n
  have hv := radialPowerRep_lipschitz (R := R) hn hr c
  have hvc := radialPowerRep_compact (n := n) hrR.le c
  have hiμ : Integrable v μ := hv.continuous.integrable_of_hasCompactSupport hvc
  have hiσ : Integrable v σ := hv.continuous.integrable_of_hasCompactSupport hvc
  have hlow : H * σ.real (ball c r) ≤ ∫ x, v x ∂σ := by
    have h := integral_mono
      ((integrableOn_const (measure_ne_top σ _)).integrable_indicator isOpen_ball.measurableSet)
      hiσ (fun x => show (ball c r).indicator (fun _ => H) x ≤ v x from ?_)
    · simpa only [integral_indicator_const _ isOpen_ball.measurableSet, smul_eq_mul, mul_comm] using h
    by_cases hx : x ∈ ball c r
    · rw [indicator_of_mem hx]
      have hd : dist c x < r := by simpa only [mem_ball, dist_comm] using hx
      exact (radialPowerRep_inner hn hr hrR.le c x
        hd.le).ge
    · rw [indicator_of_notMem hx]
      exact (radialPowerRep_bounds hn hr hrR.le c x).1
  have hupp : (∫ x, v x ∂μ) ≤ H * μ.real (ball c R) := by
    have h := integral_mono hiμ
      ((integrableOn_const measure_ball_lt_top.ne).integrable_indicator isOpen_ball.measurableSet)
      (fun x => show v x ≤ (ball c R).indicator (fun _ => H) x from ?_)
    · simpa only [integral_indicator_const _ isOpen_ball.measurableSet, smul_eq_mul, mul_comm] using h
    by_cases hx : x ∈ ball c R
    · rw [indicator_of_mem hx]
      exact (radialPowerRep_bounds hn hr hrR.le c x).2
    · rw [indicator_of_notMem hx]
      exact (radialPowerRep_zero hrR.le c x
        (by simpa only [mem_ball, dist_comm, not_lt] using hx)).le
  have hd := hdefect (radialPowerTest μ hQ (inwardSobolev μ hQ c R) hn hr hrR.le) v _ hv hvc
    (radialPowerRep_tsupport hrR.le hRT c) (radialPowerTest_inward_coe μ hQ hn hr hrR.le c)
  have hvol := radialPowerTest_volume_identity μ hQ hn hr hrR c q hpair hsphere
  have he : (∫ x, v x ∂σ) =
      r ^ (-n) * μ.real (ball c r) - R ^ (-n) * μ.real (ball c R) + curvature * ∫ x, v x ∂μ := by
    dsimp only [v] at hd ⊢
    linarith
  rw [he] at hlow
  have hc := mul_le_mul_of_nonneg_left hupp hcurvature
  dsimp only [H] at hlow hc
  nlinarith

end RegularPointCoordinates

end

end OAI
