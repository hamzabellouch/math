import OAI.Geometry.RCD.Sobolev.PositiveSourceTruncation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-!
# The bounded nonlinear test for positive sources

A primitive of `(1+|s|)^(-1-alpha)` is a global normal contraction and
is bounded by `1/alpha` on the positive half-line. Its actual Sobolev
composition gives the reciprocal-weight energy bound.
-/

open Set MeasureTheory Filter
open scoped InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

def positiveSourceWeight (alpha s : ℝ) : ℝ := (1 + |s|) ^ (-(1 + alpha))

def positiveSourceTest (alpha s : ℝ) : ℝ := ∫ r in 0..s, positiveSourceWeight alpha r

theorem positiveSourceWeight_continuous (alpha : ℝ) : Continuous (positiveSourceWeight alpha) := by
  apply (continuous_const.add continuous_abs).rpow_const
  intro s
  left
  change 1 + |s| ≠ 0
  exact ne_of_gt (by linarith [abs_nonneg s])

theorem positiveSourceWeight_bounds {alpha : ℝ} (ha : 0 < alpha) (s : ℝ) :
    0 ≤ positiveSourceWeight alpha s ∧ positiveSourceWeight alpha s ≤ 1 := by
  constructor
  · exact Real.rpow_nonneg (by positivity) _
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg s]) (by linarith)

theorem positiveSourceTest_hasDerivAt (alpha s : ℝ) :
    HasDerivAt (positiveSourceTest alpha) (positiveSourceWeight alpha s) s :=
  intervalIntegral.integral_hasDerivAt_right
    ((positiveSourceWeight_continuous alpha).intervalIntegrable 0 s)
    (positiveSourceWeight_continuous alpha).aestronglyMeasurable.stronglyMeasurableAtFilter
    (positiveSourceWeight_continuous alpha).continuousAt

theorem positiveSourceTest_zero (alpha : ℝ) : positiveSourceTest alpha 0 = 0 := by
  simp only [positiveSourceTest, intervalIntegral.integral_same]

theorem positiveSourceTest_lipschitz {alpha : ℝ} (ha : 0 < alpha) :
    LipschitzWith 1 (positiveSourceTest alpha) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun s => (positiveSourceTest_hasDerivAt alpha s).differentiableAt)
  intro s
  rw [(positiveSourceTest_hasDerivAt alpha s).deriv]
  have hn : ‖positiveSourceWeight alpha s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (positiveSourceWeight_bounds ha s).1]
    exact (positiveSourceWeight_bounds ha s).2
  exact_mod_cast hn

theorem positiveSourceTest_formula {alpha s : ℝ} (ha : 0 < alpha) (hs : 0 ≤ s) :
    positiveSourceTest alpha s = (1 - (1 + s) ^ (-alpha)) / alpha := by
  let F := fun r : ℝ => (1 - (1 + r) ^ (-alpha)) / alpha
  have hF : ContinuousOn F (Icc 0 s) := by
    apply ContinuousOn.div_const
    apply continuousOn_const.sub
    apply (continuousOn_const.add continuousOn_id).rpow_const
    intro r hr
    left
    change 1 + r ≠ 0
    exact ne_of_gt (by linarith [hr.1])
  have hd (r : ℝ) (hr : r ∈ Ioo 0 s) : HasDerivAt F (positiveSourceWeight alpha r) r := by
    have hp : 0 < 1 + r := by linarith [hr.1]
    have hh := ((hasDerivAt_const r (1 : ℝ)).sub
      (((hasDerivAt_const r (1 : ℝ)).add (hasDerivAt_id r)).rpow_const (Or.inl hp.ne') (p := -alpha))).div_const alpha
    convert hh using 1
    · rfl
    · simp only [positiveSourceWeight, abs_of_pos hr.1, zero_add, Pi.add_apply, id_eq]
      rw [show -alpha - 1 = -(1 + alpha) by ring]
      field_simp
      ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs hF hd
    ((positiveSourceWeight_continuous alpha).intervalIntegrable 0 s)
  simpa only [positiveSourceTest, F, add_zero, Real.one_rpow, sub_self, zero_div, sub_zero] using he

theorem positiveSourceTest_bounds {alpha s : ℝ} (ha : 0 < alpha) (hs : 0 ≤ s) :
    0 ≤ positiveSourceTest alpha s ∧ positiveSourceTest alpha s ≤ alpha⁻¹ := by
  constructor
  · exact intervalIntegral.integral_nonneg_of_forall hs (fun r => (positiveSourceWeight_bounds ha r).1)
  · rw [positiveSourceTest_formula ha hs]
    calc
      _ ≤ 1 / alpha := div_le_div_of_nonneg_right
        (sub_le_self _ (Real.rpow_nonneg (by linarith) _)) ha.le
      _ = _ := one_div _

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The nonlinear test gives the weighted square-gradient bound, with
linear dependence on the mass `P` of the source functional. -/
theorem positive_source_weighted_energy (Ω : Set X)
    (H : SobolevSpace.dirichlet μ hQ Ω)
    (hH : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ H.val x)
    (P : ℝ)
    (hsource : ∀ φ : SobolevSpace.dirichlet μ hQ Ω, ∀ s : ℝ, 0 ≤ s →
      (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x ∧ SobolevSpace.toLp μ hQ φ.val x ≤ s) →
      energyForm μ hQ H.val φ.val ≤ P * s)
    {alpha : ℝ} (ha : 0 < alpha) :
    Integrable (fun x => (SobolevSpace.minimalSlope μ hQ H.val x) ^ 2 /
      (1 + SobolevSpace.toLp μ hQ H.val x) ^ (1 + alpha)) μ ∧
      (∫ x, (SobolevSpace.minimalSlope μ hQ H.val x) ^ 2 /
        (1 + SobolevSpace.toLp μ hQ H.val x) ^ (1 + alpha) ∂μ) ≤ P / alpha := by
  let hl := positiveSourceTest_lipschitz ha
  let hz := positiveSourceTest_zero alpha
  let T := SobolevSpace.comp μ hQ hl hz H.val
  have hT : T ∈ SobolevSpace.dirichlet μ hQ Ω := by
    have he : T = SobolevSpace.compContraction μ hQ hl hz H.val := by
      apply Subtype.ext
      rfl
    rw [he]
    exact SobolevSpace.compContraction_mem_dirichlet μ hQ hl hz Ω H.val H.property
  have hTe : SobolevSpace.toLp μ hQ T =ᵐ[μ]
      fun x => positiveSourceTest alpha (SobolevSpace.toLp μ hQ H.val x) :=
    hl.coeFn_compLp hz _
  have hb : energyForm μ hQ H.val T ≤ P / alpha := by
    have hbound := hsource ⟨T, hT⟩ alpha⁻¹ (inv_nonneg.mpr ha.le) (by
      filter_upwards [hTe, hH] with x hx h0
      rw [hx]
      exact positiveSourceTest_bounds ha h0)
    simpa only [div_eq_mul_inv] using hbound
  have hg : localGamma μ hQ H.val T =ᵐ[μ] fun x =>
      (SobolevSpace.minimalSlope μ hQ H.val x) ^ 2 /
        (1 + SobolevSpace.toLp μ hQ H.val x) ^ (1 + alpha) := by
    filter_upwards [localGamma_comp_C1_right μ hQ H.val H.val hl hz
      (positiveSourceWeight_continuous alpha) (positiveSourceTest_hasDerivAt alpha) 1
      (fun s => by rw [abs_of_nonneg (positiveSourceWeight_bounds ha s).1]; exact (positiveSourceWeight_bounds ha s).2),
      localGamma_self μ hQ H.val, hH] with x hx hs h0
    rw [hx, hs]
    dsimp only [positiveSourceWeight]
    rw [abs_of_nonneg h0, Real.rpow_neg (by linarith)]
    ring
  refine ⟨(localGamma_memL1 μ hQ H.val T).congr hg, ?_⟩
  rw [← integral_congr_ae hg, integral_localGamma_eq_energyForm]
  exact hb

end RegularPointCoordinates

end

end OAI
