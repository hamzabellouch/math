import Mathlib
import OAI.Geometry.CAT0Fillings.Rearrangement.Energy
import OAI.Geometry.CAT0Fillings.Rearrangement.Euclidean

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal Topology

namespace CAT0Fillings.Rearrangement
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

lemma map_norm_absolutelyContinuous : μ.map (fun x : E => ‖x‖) ≪ volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hnull
  rw [Measure.map_apply (by fun_prop) hs]
  have hpolar := lintegral_fun_norm_addHaar μ (s.indicator (fun _ => (1:ℝ≥0∞)))
    (measurable_const.indicator hs)
  have he : ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^(Module.finrank ℝ E-1))*
      s.indicator (fun _ => (1:ℝ≥0∞)) r = 0 := by
    apply (lintegral_congr_ae _).trans (lintegral_zero)
    filter_upwards [ae_restrict_of_ae (show ∀ᵐ r ∂volume, r ∉ s from by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hnull)] with r hr
    simp [indicator_of_notMem hr]
  rw [he,mul_zero] at hpolar
  simpa only [←indicator_comp_right,Function.comp_def,
    lintegral_indicator (hs.preimage (continuous_norm.measurable : Measurable (norm : E → ℝ))),
    lintegral_const,Measure.restrict_apply_univ,mul_one,one_mul] using hpolar

lemma ae_norm_of_ae {p : ℝ → Prop} (hp : ∀ᵐ r : ℝ, p r) : ∀ᵐ x ∂μ, p ‖x‖ := by
  exact (ae_of_ae_map (by fun_prop)) ((map_norm_absolutelyContinuous μ).ae_le hp)

lemma ae_norm_fderiv_radial {h : ℝ → ℝ} {K : ℝ≥0} (hh : LipschitzWith K h) :
    ∀ᵐ x ∂μ, ‖fderiv ℝ (fun y : E => h ‖y‖) x‖ = |deriv h ‖x‖| := by
  filter_upwards [ae_norm_of_ae μ (hh.ae_differentiableAt (μ := volume)),
    (lipschitzWith_one_norm (E := E)).ae_differentiableAt (μ := μ)] with x hx hn
  have he : fderiv ℝ (fun y : E => h ‖y‖) x =
      deriv h ‖x‖ • fderiv ℝ (norm : E → ℝ) x := by
    simpa only [Function.comp_def] using (hx.hasDerivAt.comp_hasFDerivAt x hn.hasFDerivAt).fderiv
  rw [he]
  simp only [norm_smul,Real.norm_eq_abs,norm_fderiv_norm hn,mul_one]

lemma radial_energy_identity {h : ℝ → ℝ} {K : ℝ≥0} (hh : LipschitzWith K h) :
    ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ (fun y : E => h ‖y‖) x‖^2) ∂μ =
      (Module.finrank ℝ E : ℝ≥0∞)*μ (ball 0 1) *
        ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^(Module.finrank ℝ E-1)) *
          (ENNReal.ofReal (|deriv h r|))^2 := by
  calc
    _ = ∫⁻ x, (ENNReal.ofReal (|deriv h ‖x‖|))^2 ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_norm_fderiv_radial μ hh] with x hx
      rw [hx,ENNReal.ofReal_pow (abs_nonneg _)]
    _ = _ := lintegral_fun_norm_addHaar μ _
      ((measurable_deriv h).abs.ennreal_ofReal.pow_const 2)

end CAT0Fillings.Rearrangement
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Rearrangement

lemma radialInverse_deriv_zero_outside {R : ℝ → ℝ} {U r : ℝ}
    (hU : 0 ≤ U) (hR : AntitoneOn R (Icc 0 U)) (hr : R 0 < r) :
    deriv (radialInverse R U) r = 0 := by
  have he : radialInverse R U =ᶠ[𝓝 r] (fun _ => (0:ℝ)) := by
    filter_upwards [eventually_gt_nhds hr] with s hs
    exact radialInverse_zero_outside hU hR hs.le
  rw [he.deriv_eq]
  simp

lemma radialInverse_energy_support {R : ℝ → ℝ} {U : ℝ}
    (hU : 0 ≤ U) (hR : AntitoneOn R (Icc 0 U)) (hR0 : 0 ≤ R 0)
    (w : ℝ → ℝ≥0∞) :
    ∫⁻ r in Ioi (0:ℝ), w r * (ENNReal.ofReal (|deriv (radialInverse R U) r|))^2 =
      ∫⁻ r in Icc 0 (R 0), w r * (ENNReal.ofReal (-deriv (radialInverse R U) r))^2 := by
  have he : ∫⁻ r in Ioi (R 0), w r * (ENNReal.ofReal (|deriv (radialInverse R U) r|))^2 = 0 := by
    apply (lintegral_congr_ae _).trans lintegral_zero
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simp [radialInverse_deriv_zero_outside hU hR hr]
  have hset : Ioc 0 (R 0) ∪ Ioi (R 0) = Ioi 0 := by
    exact Ioc_union_Ioi_eq_Ioi hR0
  rw [←hset,lintegral_union measurableSet_Ioi (by exact disjoint_left.mpr (fun r hr ht => (not_le_of_gt ht) hr.2)),
    he,add_zero,restrict_Ioc_eq_restrict_Icc]
  apply lintegral_congr
  intro r
  rw [abs_of_nonpos (radialInverse_antitone R U).deriv_nonpos]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (ν : Measure E) [ν.IsAddHaarMeasure]

theorem euclidean_rearrangement_energy_bound (μ ζ : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ζ] {U K η : ℝ} (hU : 0 < U) (hK : 0 < K) (hη : η < 1)
    {P : ℝ → ℝ}
    (hpos : ∀ t ∈ Ico 0 U, 0 < μ.real (Ioi t))
    (hco : ∀ᵐ t ∂volume.restrict (Ioo 0 U),
      (1-η)*((Module.finrank ℝ E:ℝ)*ν.real (ball 0 1)*
        (radiusDistribution μ (ν.real (ball 0 1)) (Module.finrank ℝ E) t)^(Module.finrank ℝ E-1)) ≤ P t ∧
      P t ≤ K*(μ.rnDeriv volume t).toReal ∧
      P t^2 ≤ (μ.rnDeriv volume t).toReal*(ζ.rnDeriv volume t).toReal) :
    ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ (euclideanRearrangement ν μ U) x‖^2) ∂ν ≤
      ENNReal.ofReal (((1-η)⁻¹)^2)*ζ univ := by
  let n := Module.finrank ℝ E
  let ω := ν.real (ball 0 1)
  let R := radiusDistribution μ ω n
  have hω : 0 < ω := unitBall_real_pos ν
  have hn : 0 < n := Module.finrank_pos (R := ℝ) (M := E)
  have hc : 0 < (1-η)/K := div_pos (sub_pos.mpr hη) hK
  have hD := radius_secant_from_coarea μ hω hn hK
    (fun t ht => hpos t ⟨ht.1.le,ht.2⟩) (hco.mono fun _ h => ⟨h.1,h.2.1⟩)
  have hh := radialInverse_lipschitz hU.le hc ((radius_antitone μ hω.le).antitoneOn _) hD
  have hid := radial_energy_identity ν hh
  have hs := radialInverse_energy_support (R := R) hU.le ((radius_antitone μ hω.le).antitoneOn _)
    (radius_nonneg μ hω.le 0) (fun r => ENNReal.ofReal (r^(n-1)))
  change ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ (fun y : E => radialInverse R U ‖y‖) x‖^2) ∂ν ≤ _
  rw [hid,hs]
  have hconst : (n:ℝ≥0∞)*ν (ball 0 1) = ENNReal.ofReal ((n:ℝ)*ω) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast,ofReal_measureReal]
  rw [hconst,←lintegral_const_mul _ (by fun_prop)]
  have he : (fun r : ℝ => ENNReal.ofReal ((n:ℝ)*ω)*
      (ENNReal.ofReal (r^(n-1))*(ENNReal.ofReal (-deriv (radialInverse R U) r))^2)) =
      (fun r : ℝ => ENNReal.ofReal ((n:ℝ)*ω*r^(n-1))*
        (ENNReal.ofReal (-deriv (radialInverse R U) r))^2) := by
    ext r
    rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) hω.le),mul_assoc]
  rw [he]
  exact rearranged_profile_energy_bound μ ζ hω hn hU hK hη hpos hco

end CAT0Fillings.Rearrangement
end

end OAI
