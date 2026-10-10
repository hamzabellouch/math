import OAI.Probability.SLE.Geometry.ComplexAngularEnergy

namespace OAI

/-! A vertical segment's squared oscillation is bounded by its height
times the one-dimensional derivative energy. -/
noncomputable section
open Set Filter Function Complex Metric MeasureTheory
open scoped Topology ENNReal

namespace SLEExactGauge

lemma integral_norm_le_interval_energy {h : ℝ} (hh : 0<h) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Ioc 0 h))) :
    (∫ y in Ioc 0 h, ‖g y‖)≤
      Real.sqrt h*Real.sqrt (∫ y in Ioc 0 h, ‖g y‖^2) := by
  have h1 : MemLp (fun _ : ℝ => (1:ℝ)) 2 (volume.restrict (Ioc 0 h)) := memLp_const 1
  have hb := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ (fun y => norm_nonneg (g y))) (ae_of_all _ (fun _ => zero_le_one))
    (by simpa using hg.norm) (by simpa using h1)
  simpa only [mul_one,Real.rpow_two,one_pow,integral_const,smul_eq_mul,one_mul,
    Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,sub_zero,
    ENNReal.toReal_ofReal hh.le,Real.sqrt_eq_rpow,mul_comm] using hb

theorem complex_interval_energy_oscillation {h : ℝ} (hh : 0<h)
    {f : ℝ → ℂ} {x y : ℝ} (hx : x∈Ioc 0 h) (hy : y∈Ioc 0 h)
    (hf : ∀ t∈uIcc x y, DifferentiableAt ℝ f t)
    (hd : MemLp (deriv f) 2 (volume.restrict (Ioc 0 h))) :
    ‖f y-f x‖^2≤h*(∫ t in Ioc 0 h, ‖deriv f t‖^2) := by
  have hsub : uIoc x y⊆Ioc 0 h := fun t ht =>
    ordConnected_Ioc.uIcc_subset hx hy (uIoc_subset_uIcc ht)
  have hi : IntegrableOn (fun t => ‖deriv f t‖) (Ioc 0 h) :=
    (hd.integrable (by norm_num)).norm
  have hi' : IntegrableOn (deriv f) (Ioc 0 h) := hd.integrable (by norm_num)
  have hid : IntervalIntegrable (deriv f) volume x y :=
    intervalIntegrable_iff.mpr (hi'.mono_set hsub)
  have hb : ‖f y-f x‖≤Real.sqrt h*Real.sqrt (∫ t in Ioc 0 h, ‖deriv f t‖^2) := by
    calc
      ‖f y-f x‖ = ‖∫ t in x..y, deriv f t‖ :=
        congrArg norm (intervalIntegral.integral_deriv_eq_sub hf hid).symm
      _ ≤ ∫ t in uIoc x y, ‖deriv f t‖ := intervalIntegral.norm_integral_le_integral_norm_uIoc
      _ ≤ ∫ t in Ioc 0 h, ‖deriv f t‖ :=
        setIntegral_mono_set hi (ae_of_all _ (fun _ => norm_nonneg _)) hsub.eventuallySubset
      _ ≤ _ := integral_norm_le_interval_energy hh hd
  have hE : 0≤∫ t in Ioc 0 h, ‖deriv f t‖^2 := integral_nonneg (fun _ => sq_nonneg _)
  have hs := mul_nonneg (Real.sqrt_nonneg h) (Real.sqrt_nonneg (∫ t in Ioc 0 h, ‖deriv f t‖^2))
  have hsquare := mul_le_mul hb hb (norm_nonneg _) hs
  simpa only [←pow_two,mul_pow,Real.sq_sqrt hh.le,Real.sq_sqrt hE] using hsquare

end SLEExactGauge

end

end OAI
