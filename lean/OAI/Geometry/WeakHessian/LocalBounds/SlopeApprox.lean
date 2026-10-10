import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.SpeedApprox

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace

namespace WeakHessian
variable {X : Type*} [MetricSpace X]

def slopeApprox (f : X → ℝ) (n : ℕ) (x : X) : ℝ≥0∞ :=
  ⨆ (y : X) (_ : dist y x < 1 / (n + 1 : ℝ)),
    ENNReal.ofReal (|f y - f x| / dist y x)

lemma localSlope_eq_iInf_slopeApprox (f : X → ℝ) (x : X) :
    localSlope f x = ⨅ n : ℕ, slopeApprox f n x := by
  rw [localSlope, nhdsWithin,
    ((Metric.nhds_basis_ball_inv_nat_succ (x := x)).inf_principal ({x}ᶜ)).limsup_eq_iInf_iSup]
  simp only [iInf_true]
  apply iInf_congr
  intro n
  apply le_antisymm
  · apply iSup_le
    intro y
    apply iSup_le
    intro hy
    exact le_iSup_of_le y (le_iSup_of_le hy.1 le_rfl)
  · apply iSup_le
    intro y
    apply iSup_le
    intro hy
    by_cases hyx : y = x
    · simp [hyx]
    · exact le_iSup_of_le y (le_iSup_of_le
        (show y ∈ Metric.ball x (1 / (n + 1 : ℝ)) ∩ {x}ᶜ from ⟨hy, hyx⟩) le_rfl)

lemma lowerSemicontinuous_slopeApprox {f : X → ℝ} (hf : Continuous f) (n : ℕ) :
    LowerSemicontinuous (slopeApprox f n) := by
  intro x a ha
  obtain ⟨y, hy⟩ := lt_iSup_iff.mp ha
  obtain ⟨hy, hay⟩ := lt_iSup_iff.mp hy
  have hyx : y ≠ x := by
    intro heq
    simp [heq] at hay
  have hdist : ContinuousAt (fun z => dist y z) x := continuous_const.dist continuous_id |>.continuousAt
  have hq : ContinuousAt (fun z => ENNReal.ofReal (|f y - f z| / dist y z)) x :=
    ENNReal.continuous_ofReal.continuousAt.comp
      (((continuous_const.sub hf).abs.continuousAt).div hdist (dist_ne_zero.mpr hyx))
  filter_upwards [hdist.eventually_lt continuousAt_const hy,
    (continuousAt_const.eventually_lt hq hay)] with z hz hqz
  exact hqz.trans_le (le_iSup_of_le y (le_iSup_of_le hz le_rfl))

lemma measurable_localSlope [MeasurableSpace X] [BorelSpace X]
    {f : X → ℝ} (hf : Continuous f) : Measurable (localSlope f) := by
  simp_rw [show localSlope f = fun x => ⨅ n, slopeApprox f n x from
    funext (localSlope_eq_iInf_slopeApprox f)]
  exact Measurable.iInf fun n => (lowerSemicontinuous_slopeApprox hf n).measurable

lemma slopeApprox_le_lipschitz {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (n : ℕ) (x : X) : slopeApprox f n x ≤ L := by
  apply iSup_le
  intro y
  apply iSup_le
  intro _hy
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  by_cases hyx : y = x
  · simp [hyx]
  · apply (div_le_iff₀ (dist_pos.mpr hyx)).mpr
    simpa only [Real.dist_eq] using hf.dist_le_mul y x

lemma localSlope_le_lipschitz {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (x : X) : localSlope f x ≤ L := by
  rw [localSlope_eq_iInf_slopeApprox]
  exact (iInf_le _ 0).trans (slopeApprox_le_lipschitz hf 0 x)

lemma deriv_comp_le_slopeApprox {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (γ : Curve X) (t : ℝ) (n : ℕ) :
    ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t| ≤
      slopeApprox f n (evalReal γ t) * metricSpeed γ t := by
  by_cases hd : DifferentiableAt ℝ (fun s => f (evalReal γ s)) t
  · have hlim : Tendsto
        (fun s => ENNReal.ofReal (|f (evalReal γ s) - f (evalReal γ t)| / |s-t|))
        (𝓝[≠] t) (𝓝 (ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t|)) := by
      simpa only [slope, vsub_eq_sub, smul_eq_mul, norm_mul, norm_inv,
        Real.norm_eq_abs, div_eq_mul_inv, mul_comm] using
        ENNReal.tendsto_ofReal (hasDerivAt_iff_tendsto_slope.mp hd.hasDerivAt).norm
    have hγc : Continuous (evalReal γ) :=
      continuous_evalReal.comp (continuous_const.prodMk continuous_id)
    have hnear : ∀ᶠ s in 𝓝 t,
        dist (evalReal γ s) (evalReal γ t) < 1 / (n + 1 : ℝ) := by
      apply (hγc.dist continuous_const).continuousAt.eventually_lt continuousAt_const
      simp only [dist_self]
      positivity
    calc
      _ = limsup (fun s => ENNReal.ofReal
          (|f (evalReal γ s) - f (evalReal γ t)| / |s-t|)) (𝓝[≠] t) := hlim.limsup_eq.symm
      _ ≤ limsup (fun s => slopeApprox f n (evalReal γ t) * ENNReal.ofReal
          (dist (evalReal γ s) (evalReal γ t) / |s-t|)) (𝓝[≠] t) := by
        refine limsup_le_limsup ?_
        filter_upwards [hnear.filter_mono nhdsWithin_le_nhds] with s hs
        by_cases heq : evalReal γ s = evalReal γ t
        · simp [heq]
        have hdne : dist (evalReal γ s) (evalReal γ t) ≠ 0 := dist_ne_zero.mpr heq
        have hid : |f (evalReal γ s) - f (evalReal γ t)| / |s-t| =
            (|f (evalReal γ s) - f (evalReal γ t)| / dist (evalReal γ s) (evalReal γ t)) *
              (dist (evalReal γ s) (evalReal γ t) / |s-t|) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
          calc
            _ = |f (evalReal γ s) - f (evalReal γ t)| *
                ((dist (evalReal γ s) (evalReal γ t))⁻¹ * dist (evalReal γ s) (evalReal γ t)) * |s-t|⁻¹ := by
              rw [inv_mul_cancel₀ hdne, mul_one]
            _ = _ := by ring
        rw [hid, ENNReal.ofReal_mul (div_nonneg (abs_nonneg _) dist_nonneg)]
        apply mul_le_mul_left
        exact le_iSup_of_le (evalReal γ s) (le_iSup_of_le hs le_rfl)
      _ = _ := ENNReal.limsup_const_mul_of_ne_top
          (ne_top_of_le_ne_top ENNReal.coe_ne_top (slopeApprox_le_lipschitz hf n _))
  · simp only [deriv_zero_of_not_differentiableAt hd, abs_zero, ENNReal.ofReal_zero]
    exact bot_le

lemma deriv_comp_le_localSlope {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (γ : Curve X) (t : ℝ) (hspeed : metricSpeed γ t ≠ ∞) :
    ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t| ≤
      localSlope f (evalReal γ t) * metricSpeed γ t := by
  rw [localSlope_eq_iInf_slopeApprox, ENNReal.iInf_mul (fun h => (hspeed h).elim)]
  exact le_iInf fun n => deriv_comp_le_slopeApprox hf γ t n

variable [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma localSlope_isLocalWeakUpperGradient (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    IsLocalWeakUpperGradient m f (fun x => (localSlope f x).toReal) := by
  have hm : Measurable (fun x => (localSlope f x).toReal) :=
    (measurable_localSlope hf.continuous).ennreal_toReal
  have hbound : ∀ x, ‖(localSlope f x).toReal‖ ≤ (L : ℝ) := by
    intro x
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact (ENNReal.toReal_mono ENNReal.coe_ne_top (localSlope_le_lipschitz hf x)).trans_eq
      (ENNReal.coe_toReal L)
  have hsl : ∀ x, localSlope f x ≠ ∞ := fun x =>
    ne_top_of_le_ne_top ENNReal.coe_ne_top (localSlope_le_lipschitz hf x)
  refine ⟨?_, ae_of_all m fun _ => ENNReal.toReal_nonneg, ?_⟩
  · intro o R _hR
    let : IsFiniteMeasure (m.restrict (Metric.ball o R)) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using
        hfinite (Metric.ball o R) Metric.isBounded_ball⟩
    exact MemLp.of_bound hm.aestronglyMeasurable (L : ℝ) (ae_of_all _ hbound)
  · intro π hπ _hb
    let : IsProbabilityMeasure π := hπ.1
    have hsm : Measurable (fun p : Curve X × ℝ => metricSpeed p.1 p.2 ^ 2) :=
      measurable_metricSpeed.pow_const 2
    have hfin := ae_lt_top hsm.lintegral_prod_right hπ.2.2.2.ne
    apply lintegral_mono_ae
    filter_upwards [hπ.2.2.1, hfin] with γ hγ hfinγ
    have hfiniteSpeed : ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) 1), metricSpeed γ t ≠ ∞ := by
      have hh := ae_lt_top (hsm.comp measurable_prodMk_left) hfinγ.ne
      filter_upwards [hh] with t ht
      exact fun heq => by simp [heq] at ht
    have hac := lipschitz_comp_absolutelyContinuous hf hγ.absolutelyContinuous
    calc
      ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| =
          ‖∫ t in Set.Icc (0 : ℝ) 1, deriv (fun s => f (evalReal γ s)) t‖ₑ := by
        rw [← ofReal_norm, Real.norm_eq_abs, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le zero_le_one, hac.integral_deriv_eq_sub]
        simp [evalReal, clampTime, timeOne, timeZero]
        rfl
      _ ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖deriv (fun s => f (evalReal γ s)) t‖ₑ :=
        enorm_integral_le_lintegral_enorm _
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [hfiniteSpeed] with t ht
        simpa only [← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_toReal (hsl _)]
          using deriv_comp_le_localSlope hf γ t ht

end WeakHessian

end
end InlinedFile0

end OAI
