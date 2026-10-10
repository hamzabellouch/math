import OAI.Geometry.RCD.Sobolev.PositiveSourceTruncation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-!
# Radial inverse-power tests

A bounded continuous weight is integrated before clipping the argument.
The resulting Sobolev test has the exact annular derivative needed to
convert the squared-distance weak Laplacian into a volume drop.
-/

open Set MeasureTheory Filter
open scoped NNReal

noncomputable section

namespace RegularPointCoordinates

/-- The global derivative used before clipping at the inner radius. -/
def radialPowerWeight (n r R s : ℝ) : ℝ := (max r (R - s)) ^ (-(n + 1))

def radialPowerPrimitive (n r R s : ℝ) : ℝ :=
  ∫ t in 0..s, radialPowerWeight n r R t

theorem radialPowerWeight_continuous (n R : ℝ) {r : ℝ} (hr : 0 < r) :
    Continuous (radialPowerWeight n r R) := by
  apply (continuous_const.max (continuous_const.sub continuous_id)).rpow_const
  intro s
  left
  exact ne_of_gt (hr.trans_le (le_max_left _ _))

theorem radialPowerWeight_bounds {n r R : ℝ} (hn : 0 < n) (hr : 0 < r) (s : ℝ) :
    0 ≤ radialPowerWeight n r R s ∧ radialPowerWeight n r R s ≤ r ^ (-(n + 1)) := by
  constructor
  · exact Real.rpow_nonneg (hr.le.trans (le_max_left _ _)) _
  · exact Real.rpow_le_rpow_of_nonpos hr (le_max_left _ _) (by linarith)

theorem radialPowerPrimitive_hasDerivAt (n R s : ℝ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (radialPowerPrimitive n r R) (radialPowerWeight n r R s) s :=
  intervalIntegral.integral_hasDerivAt_right
    ((radialPowerWeight_continuous n R hr).intervalIntegrable 0 s)
    (radialPowerWeight_continuous n R hr).aestronglyMeasurable.stronglyMeasurableAtFilter
    (radialPowerWeight_continuous n R hr).continuousAt

@[simp] theorem radialPowerPrimitive_zero (n r R : ℝ) : radialPowerPrimitive n r R 0 = 0 := by
  simp only [radialPowerPrimitive, intervalIntegral.integral_same]

theorem radialPowerPrimitive_lipschitz {n r R : ℝ} (hn : 0 < n) (hr : 0 < r) :
    LipschitzWith ⟨r ^ (-(n + 1)), Real.rpow_nonneg hr.le _⟩
      (radialPowerPrimitive n r R) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun s => (radialPowerPrimitive_hasDerivAt n R s hr).differentiableAt)
  intro s
  rw [(radialPowerPrimitive_hasDerivAt n R s hr).deriv]
  have hb := radialPowerWeight_bounds (R := R) hn hr s
  show ‖radialPowerWeight n r R s‖₊ ≤ _
  exact_mod_cast (show ‖radialPowerWeight n r R s‖ ≤ r ^ (-(n + 1)) by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2)

/-- On the unclipped interval this primitive is the inverse-power cutoff. -/
theorem radialPowerPrimitive_formula {n r R s : ℝ} (hn : 0 < n) (hr : 0 < r)
    (hs : 0 ≤ s) (hsR : s ≤ R - r) :
    radialPowerPrimitive n r R s = ((R - s) ^ (-n) - R ^ (-n)) / n := by
  have hR : 0 < R := by linarith
  let F := fun t : ℝ => ((R - t) ^ (-n) - R ^ (-n)) / n
  have hF : ContinuousOn F (Icc 0 s) := by
    apply ContinuousOn.div_const
    apply ContinuousOn.sub _ continuousOn_const
    apply (continuousOn_const.sub continuousOn_id).rpow_const
    intro t ht
    left
    change R - t ≠ 0
    exact ne_of_gt (by linarith [ht.2])
  have hd (t : ℝ) (ht : t ∈ Ioo 0 s) : HasDerivAt F (radialPowerWeight n r R t) t := by
    have hrt : r ≤ R - t := by linarith [ht.2]
    have hpos : 0 < R - t := hr.trans_le hrt
    have h := ((((hasDerivAt_const t R).sub (hasDerivAt_id t)).rpow_const
      (Or.inl hpos.ne') (p := -n)).sub_const (R ^ (-n))).div_const n
    convert h using 1
    · rfl
    · simp only [radialPowerWeight, max_eq_right hrt, Pi.sub_apply, id_eq]
      rw [show -n - 1 = -(n + 1) by ring]
      field_simp
      ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs hF hd
    ((radialPowerWeight_continuous n R hr).intervalIntegrable 0 s)
  simpa only [radialPowerPrimitive, F, sub_zero, sub_self, zero_div, sub_zero] using he

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Clipping has the same locality formula when paired with any Sobolev function. -/
theorem positiveTruncation_gamma_pair (q u : SobolevSpace μ hQ)
    (hu : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ u x) {t : ℝ} (ht : 0 ≤ t) :
    localGamma μ hQ q (positiveTruncation μ hQ u t ht) =ᵐ[μ]
      fun x => if SobolevSpace.toLp μ hQ u x < t then localGamma μ hQ q u x else 0 := by
  let T := positiveTruncation μ hQ u t ht
  filter_upwards [positiveTruncation_coe μ hQ u ht, hu,
    localGamma_comm μ hQ q T, localGamma_comm μ hQ q u,
    localGamma_eq_on_eq μ hQ T u q,
    localGamma_zero_on_level μ hQ T q t] with x hx h0 hc hc' he hz
  rw [hc]
  by_cases hlt : SobolevSpace.toLp μ hQ u x < t
  · rw [ite_eq_left hlt, hc']
    apply he
    rw [hx, positiveClip, max_eq_left h0, min_eq_left hlt.le]
  · rw [ite_eq_right hlt]
    apply hz
    rw [hx, positiveClip, max_eq_left h0, min_eq_right (le_of_not_gt hlt)]

/-- The actual radial Sobolev test obtained by clipping an inward distance. -/
def radialPowerTest (u : SobolevSpace μ hQ) {n r R : ℝ}
    (hn : 0 < n) (hr : 0 < r) (hrR : r ≤ R) : SobolevSpace μ hQ :=
  SobolevSpace.comp μ hQ (radialPowerPrimitive_lipschitz hn hr)
    (radialPowerPrimitive_zero n r R)
    (positiveTruncation μ hQ u (R - r) (sub_nonneg.mpr hrR))

omit [BorelSpace X] [ProperSpace X] in
theorem radialPowerTest_coe (u : SobolevSpace μ hQ) {n r R : ℝ}
    (hn : 0 < n) (hr : 0 < r) (hrR : r ≤ R) :
    SobolevSpace.toLp μ hQ (radialPowerTest μ hQ u hn hr hrR) =ᵐ[μ]
      fun x => radialPowerPrimitive n r R (positiveClip (R - r) (SobolevSpace.toLp μ hQ u x)) := by
  filter_upwards [SobolevSpace.comp_coe μ hQ (radialPowerPrimitive_lipschitz hn hr)
      (radialPowerPrimitive_zero n r R) (positiveTruncation μ hQ u (R - r) (sub_nonneg.mpr hrR)),
    positiveTruncation_coe μ hQ u (sub_nonneg.mpr hrR)] with x hc ht
  exact hc.trans (by simp only [Function.comp_apply, ht])

theorem radialPowerTest_gamma (q u : SobolevSpace μ hQ)
    (hu : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ u x)
    {n r R : ℝ} (hn : 0 < n) (hr : 0 < r) (hrR : r ≤ R) :
    localGamma μ hQ q (radialPowerTest μ hQ u hn hr hrR) =ᵐ[μ]
      fun x => if SobolevSpace.toLp μ hQ u x < R - r then
        radialPowerWeight n r R (SobolevSpace.toLp μ hQ u x) * localGamma μ hQ q u x else 0 := by
  filter_upwards [localGamma_comp_C1_right μ hQ q
      (positiveTruncation μ hQ u (R - r) (sub_nonneg.mpr hrR))
      (radialPowerPrimitive_lipschitz hn hr) (radialPowerPrimitive_zero n r R)
      (radialPowerWeight_continuous n R hr) (fun s => radialPowerPrimitive_hasDerivAt n R s hr)
      ⟨r ^ (-(n + 1)), Real.rpow_nonneg hr.le _⟩
      (fun s => by rw [abs_of_nonneg (radialPowerWeight_bounds hn hr s).1];
                   exact (radialPowerWeight_bounds hn hr s).2),
    positiveTruncation_gamma_pair μ hQ q u hu (sub_nonneg.mpr hrR),
    positiveTruncation_coe μ hQ u (sub_nonneg.mpr hrR), hu] with x hc hg ht h0
  change localGamma μ hQ q (radialPowerTest μ hQ u hn hr hrR) x = _ at hc
  rw [hc, hg]
  by_cases hlt : SobolevSpace.toLp μ hQ u x < R - r
  · rw [ite_eq_left hlt, ite_eq_left hlt, ht, positiveClip, max_eq_left h0,
      min_eq_left hlt.le]
  · rw [ite_eq_right hlt, ite_eq_right hlt, mul_zero]

end RegularPointCoordinates

end

end OAI
