import Mathlib
import OAI.MeasureTheory.Falconer.Fourier.DistanceSincCollision
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Shells.IntegralDyadicShellBound

namespace OAI

/-! Fourier kernels and oscillatory estimates. -/

open _root_.OAI.PlanarFalconer

section
section
namespace CriticalFourierSupport
namespace CurrentFalconer
open MeasureTheory Set
open scoped ENNReal
section HalfDimensionalFourierSum
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem halfDimensional_fourier_with_cutoff (χ : SchwartzMap V ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ ξ : Measure V), IsProbabilityMeasure μ →
      IsFiniteMeasure ξ → (∀ᵐ x ∂μ, χ x = 1) →
      ∀ (K L H R : ℝ), 1 ≤ K → 1 ≤ L → 1 ≤ H → H ≤ R →
      (∀ (x : V) (r : ℝ), H⁻¹ ≤ r → r ≤ 1 →
        μ (Metric.ball x r) ≤ ENNReal.ofReal (K*r^((Module.finrank ℝ V : ℝ)/2))) →
      ξ Set.univ ≤ 1 → (∀ᵐ w ∂ξ, ‖w‖ = 1) →
      (∀ (w : V), ‖w‖ = 1 → ∀ r : ℝ, R⁻¹ ≤ r → r ≤ 1 →
        ξ (Metric.ball w r) ≤ ENNReal.ofReal (L*r^((Module.finrank ℝ V : ℝ)/2))) →
      (∫ s : ℝ in Set.Icc (-H) H,
        ∫ w : V, ‖PlanarFalconer.sourceFourier μ (s • w)‖^2 ∂ξ) ≤
          C*L*K*(1+Real.log H) := by
  obtain ⟨C₀,hC₀,hshell⟩ := halfDimensional_fourier_shell χ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2+C₀*(1+(Real.log 2)⁻¹), by positivity, ?_⟩
  intro μ ξ hμ hξ hχ K L H R hK hL hH hHR hball hmass hsphere hcap
  let := hμ
  let := hξ
  have hKL : 1 ≤ L*K := by nlinarith
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg hH
  have hlo : (∫ s : ℝ in Set.Icc (-1) 1, angularFourierEnergy μ ξ s) ≤ 2 := by
    have hi : IntegrableOn (angularFourierEnergy μ ξ) (Set.Icc (-1) 1) :=
      (angularFourierEnergy_continuous μ ξ).integrableOn_Icc
    have hh := integral_mono hi (integrable_const (1 : ℝ))
      (fun s => angularFourierEnergy_le_one μ ξ hmass s)
    norm_num at hh
    exact hh
  have hh := integral_dyadic_shell_bound (angularFourierEnergy μ ξ)
    (angularFourierEnergy_continuous μ ξ) (angularFourierEnergy_nonneg μ ξ)
    hH (show 0 ≤ C₀*L*K by positivity) hlo
    (fun B hB hBH => hshell μ ξ hμ hξ hχ K L B H R hK hL hB hBH hHR
      hball hmass hsphere hcap)
  have hc : 0 ≤ C₀*(1+(Real.log 2)⁻¹) := by positivity
  have hx : Real.log H / Real.log 2 + 1 ≤
      (1+(Real.log 2)⁻¹)*(1+Real.log H) := by
    rw [div_eq_mul_inv]
    nlinarith [inv_pos.mpr hlog2]
  have htwo : (2 : ℝ) ≤ 2*(L*K)*(1+Real.log H) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hKL) hlogH]
  change (∫ s : ℝ in Set.Icc (-H) H, angularFourierEnergy μ ξ s) ≤ _
  apply hh.trans
  have hmul := mul_le_mul_of_nonneg_right hx (show 0 ≤ C₀*L*K by positivity)
  nlinarith

end HalfDimensionalFourierSum
end CurrentFalconer
end CriticalFourierSupport
end
end

section
section
namespace CriticalFourierSupport
namespace CurrentFalconer
open MeasureTheory Set
open scoped ENNReal

theorem integral_div_le (f : ℝ → ℝ) (hf : Continuous f)
    (hn : ∀ s, 0 ≤ f s) {H c : ℝ} (hH : 0 ≤ H) (hc : 1 ≤ c) :
    (∫ s : ℝ in Set.Icc (-H) H, f (s/c)) ≤
      c * ∫ s : ℝ in Set.Icc (-H) H, f s := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hHc : H/c ≤ H := (div_le_self hH hc)
  have he : (∫ s : ℝ in Set.Icc (-H) H, f (s/c)) =
      c * ∫ s : ℝ in Set.Icc (-(H/c)) (H/c), f s := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      intervalIntegral.integral_comp_div f hc0.ne',
      intervalIntegral.integral_of_le (by rw [neg_div]; linarith [div_nonneg hH hc0.le] : -H/c ≤ H/c),
      ← integral_Icc_eq_integral_Ioc, neg_div, smul_eq_mul]
  rw [he]
  apply mul_le_mul_of_nonneg_left _ hc0.le
  apply setIntegral_mono_set (hf.integrableOn_Icc) (ae_of_all _ hn)
  exact (Set.Icc_subset_Icc (by linarith) hHc).eventuallyLE

section SourceFourierConvention
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def manuscriptFourier (μ : Measure V) (v : V) : ℂ := charFun μ (-v)

omit [FiniteDimensional ℝ V] [BorelSpace V] in
theorem manuscriptFourier_eq_normalized (μ : Measure V) (v : V) :
    manuscriptFourier μ v = PlanarFalconer.sourceFourier μ ((2*Real.pi)⁻¹ • v) := by
  unfold manuscriptFourier PlanarFalconer.sourceFourier
  congr 1
  rw [smul_smul, neg_mul, mul_inv_cancel₀ (by positivity : 2*Real.pi ≠ 0), neg_one_smul]

theorem halfDimensional_manuscriptFourier_with_cutoff (χ : SchwartzMap V ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ ξ : Measure V), IsProbabilityMeasure μ →
      IsFiniteMeasure ξ → (∀ᵐ x ∂μ, χ x = 1) →
      ∀ (K L H R : ℝ), 1 ≤ K → 1 ≤ L → 1 ≤ H → H ≤ R →
      (∀ (x : V) (r : ℝ), H⁻¹ ≤ r → r ≤ 1 →
        μ (Metric.ball x r) ≤ ENNReal.ofReal (K*r^((Module.finrank ℝ V : ℝ)/2))) →
      ξ Set.univ ≤ 1 → (∀ᵐ w ∂ξ, ‖w‖ = 1) →
      (∀ (w : V), ‖w‖ = 1 → ∀ r : ℝ, R⁻¹ ≤ r → r ≤ 1 →
        ξ (Metric.ball w r) ≤ ENNReal.ofReal (L*r^((Module.finrank ℝ V : ℝ)/2))) →
      (∫ s : ℝ in Set.Icc (-H) H,
        ∫ w : V, ‖manuscriptFourier μ (s • w)‖^2 ∂ξ) ≤
          C*L*K*(1+Real.log H) := by
  obtain ⟨C₀,hC₀,hfourier⟩ := halfDimensional_fourier_with_cutoff χ
  refine ⟨(2*Real.pi)*C₀, by positivity, ?_⟩
  intro μ ξ hμ hξ hχ K L H R hK hL hH hHR hball hmass hsphere hcap
  let := hμ
  let := hξ
  have he (s : ℝ) : (∫ w : V, ‖manuscriptFourier μ (s • w)‖^2 ∂ξ) =
      angularFourierEnergy μ ξ (s/(2*Real.pi)) := by
    simp only [manuscriptFourier_eq_normalized, angularFourierEnergy, smul_smul,
      div_eq_inv_mul]
  simp_rw [he]
  have hscale := integral_div_le (angularFourierEnergy μ ξ)
    (angularFourierEnergy_continuous μ ξ) (angularFourierEnergy_nonneg μ ξ)
    (show 0 ≤ H by linarith) (show 1 ≤ 2*Real.pi by linarith [Real.pi_gt_three])
  have hh := hfourier μ ξ hμ hξ hχ K L H R hK hL hH hHR hball hmass hsphere hcap
  have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*Real.pi by positivity)
  exact hscale.trans (by simpa only [angularFourierEnergy, mul_assoc] using hh')

omit [MeasurableSpace V] [BorelSpace V] in

theorem exists_schwartz_cutoff_ball (T : ℝ) :
    ∃ χ : SchwartzMap V ℂ, ∀ x : V, ‖x‖ ≤ T → χ x = 1 := by
  let b : ContDiffBump (0 : V) := ⟨|T|+1, |T|+2, by positivity, by linarith⟩
  have hcompact : HasCompactSupport (Complex.ofRealCLM ∘ b) :=
    b.hasCompactSupport.comp_left rfl
  refine ⟨hcompact.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), ?_⟩
  intro x hx
  change (b x : ℂ) = 1
  rw [b.one_of_mem_closedBall, Complex.ofReal_one]
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact hx.trans (by dsimp [b]; linarith [le_abs_self T])

end SourceFourierConvention
end CurrentFalconer
end CriticalFourierSupport
end
end

section
section
namespace CriticalFourierSupport
namespace CurrentFalconer
open MeasureTheory Set
open scoped ENNReal
section HalfDimensionalFourierBoundedSupport
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ V] in
theorem manuscriptFourier_norm_translate (μ : Measure V) (z v : V) :
    ‖manuscriptFourier (μ.map (· + z)) v‖ = ‖manuscriptFourier μ v‖ := by
  simp [manuscriptFourier, charFun_map_add_const, Complex.norm_exp]

omit [FiniteDimensional ℝ V] [InnerProductSpace ℝ V] in
theorem translate_measure_ball (μ : Measure V) (z x : V) (r : ℝ) :
    μ.map (· + z) (Metric.ball x r) = μ (Metric.ball (x-z) r) := by
  rw [Measure.map_apply (by fun_prop) measurableSet_ball]
  congr 1
  ext y
  simp only [mem_preimage, Metric.mem_ball, dist_eq_norm]
  rw [show y+z-x = y-(x-z) by abel]

theorem halfDimensional_fourier (T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ ξ : Measure V), IsProbabilityMeasure μ →
      IsFiniteMeasure ξ → (∃ z : V, ∀ᵐ x ∂μ, dist x z ≤ T) →
      ∀ (K L H R : ℝ), 1 ≤ K → 1 ≤ L → 1 ≤ H → H ≤ R →
      (∀ (x : V) (r : ℝ), H⁻¹ ≤ r → r ≤ 1 →
        μ (Metric.ball x r) ≤ ENNReal.ofReal (K*r^((Module.finrank ℝ V : ℝ)/2))) →
      ξ Set.univ ≤ 1 → (∀ᵐ w ∂ξ, ‖w‖ = 1) →
      (∀ (w : V), ‖w‖ = 1 → ∀ r : ℝ, R⁻¹ ≤ r → r ≤ 1 →
        ξ (Metric.ball w r) ≤ ENNReal.ofReal (L*r^((Module.finrank ℝ V : ℝ)/2))) →
      (∫ s : ℝ in Set.Icc (-H) H,
        ∫ w : V, ‖manuscriptFourier μ (s • w)‖^2 ∂ξ) ≤
          C*L*K*(1+Real.log H) := by
  obtain ⟨χ,hχ⟩ := exists_schwartz_cutoff_ball (V := V) T
  obtain ⟨C,hC,hh⟩ := halfDimensional_manuscriptFourier_with_cutoff χ
  refine ⟨C,hC,?_⟩
  intro μ ξ hμ hξ hsupp K L H R hK hL hH hHR hball hmass hsphere hcap
  let := hμ
  let := hξ
  obtain ⟨z,hz⟩ := hsupp
  let μ₀ := μ.map (· + -z)
  have hp : IsProbabilityMeasure μ₀ := inferInstance
  have hs : ∀ᵐ x ∂μ₀, χ x = 1 := by
    apply (ae_map_iff (by fun_prop) (measurableSet_eq_fun (by fun_prop) measurable_const)).mpr
    filter_upwards [hz] with x hx
    apply hχ
    simpa only [dist_eq_norm, sub_eq_add_neg] using hx
  have hb : ∀ (x : V) (r : ℝ), H⁻¹ ≤ r → r ≤ 1 →
      μ₀ (Metric.ball x r) ≤ ENNReal.ofReal (K*r^((Module.finrank ℝ V : ℝ)/2)) := by
    intro x r hr hr1
    rw [show μ₀ = μ.map (· + -z) from rfl, translate_measure_ball]
    exact hball _ r hr hr1
  have h := hh μ₀ ξ hp hξ hs K L H R hK hL hH hHR hb hmass hsphere hcap
  simpa only [μ₀, manuscriptFourier_norm_translate] using h

end HalfDimensionalFourierBoundedSupport
end CurrentFalconer
end CriticalFourierSupport
end
end

section
section
namespace GraphLiteralSupport.CurrentFalconer.Exceptional
open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def projectionCollision (μ : Measure V) (ε : ℝ) (w : V) : ℝ :=
  (μ.prod μ).real {xy | |inner ℝ (xy.1-xy.2) w| ≤ ε}

lemma projectionCollision_measurable (μ : Measure V) [IsFiniteMeasure μ] (ε : ℝ) :
    Measurable (projectionCollision μ ε) := by
  apply Measurable.ennreal_toReal
  exact measurable_measure_prodMk_left (show MeasurableSet
    {z : V × (V × V) | |inner ℝ (z.2.1-z.2.2) z.1| ≤ ε} from by measurability)

omit [FiniteDimensional ℝ V] [BorelSpace V] in
lemma projectionCollision_le_one (μ : Measure V) [IsProbabilityMeasure μ] (ε : ℝ) (w : V) :
    projectionCollision μ ε w ≤ 1 := by
  exact (measureReal_mono (subset_univ _)).trans_eq (by simp)

lemma projectionCollision_integrable (μ ξ : Measure V) [IsProbabilityMeasure μ]
    [IsFiniteMeasure ξ] (ε : ℝ) : Integrable (projectionCollision μ ε) ξ := by
  apply (integrable_const (1:ℝ)).mono' (projectionCollision_measurable μ ε).aestronglyMeasurable
  filter_upwards with w
  rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ projectionCollision μ ε w from ENNReal.toReal_nonneg)]
  exact projectionCollision_le_one μ ε w

lemma charFun_projection (μ : Measure V) [IsFiniteMeasure μ] (w : V) (r : ℝ) :
    charFun (μ.map (fun x => inner ℝ x w)) r = charFun μ (r • w) := by
  rw [charFun_apply_real,integral_map_of_stronglyMeasurable (by fun_prop) (by fun_prop),
    charFun_apply]
  apply integral_congr_ae
  filter_upwards with x
  simp only [inner_smul_right,Complex.ofReal_mul]

lemma projectionCollision_map (μ : Measure V) [IsFiniteMeasure μ] (w : V) (ε : ℝ) :
    let ν := μ.map (fun x => inner ℝ x w)
    (ν.prod ν).real {z : ℝ × ℝ | |z.1-z.2| ≤ ε} = projectionCollision μ ε w := by
  dsimp only
  rw [measureReal_def,Measure.map_prod_map μ μ (by fun_prop) (by fun_prop),
    Measure.map_apply (by fun_prop) (by measurability)]
  change ((μ.prod μ) _).toReal = ((μ.prod μ) _).toReal
  congr 2
  ext z
  change |inner ℝ z.1 w - inner ℝ z.2 w| ≤ ε ↔ |inner ℝ (z.1-z.2) w| ≤ ε
  rw [inner_sub_left]

lemma projection_collision_frequency_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (μ : Measure V) [IsProbabilityMeasure μ] (ε H : ℝ),
      0 < ε → 0 < H → 100/ε ≤ H → ∀ w : V,
      projectionCollision μ ε w ≤ C*ε*(∫ r in Icc (-H) H, ‖charFun μ (r • w)‖^2) := by
  obtain ⟨C,hC,hbound⟩ := PlanarFalconer.finite_measure_distance_collision_fourier
  refine ⟨C/100,by positivity,?_⟩
  intro μ _ ε H hε hH hscale w
  let ν := μ.map (fun x => inner ℝ x w)
  have hb := hbound ν (100/ε) (by positivity)
  have he : 100/(100/ε)=ε := by field_simp
  rw [he,projectionCollision_map] at hb
  dsimp [ν] at hb
  simp_rw [charFun_projection] at hb
  have hi : IntegrableOn (fun r : ℝ => ‖charFun μ (r • w)‖^2) (Icc (-H) H) := by
    apply ContinuousOn.integrableOn_Icc
    fun_prop
  have hm := integral_mono_measure (Measure.restrict_mono
    (show Icc (-(100/ε)) (100/ε) ⊆ Icc (-H) H from Icc_subset_Icc (by linarith) hscale) le_rfl)
    (Filter.Eventually.of_forall (fun r => sq_nonneg ‖charFun μ (r • w)‖)) hi
  have hb' := hb.trans (mul_le_mul_of_nonneg_left hm hC.le)
  apply (le_of_mul_le_mul_left ?_ (by positivity : 0 < 100/ε))
  calc
    (100/ε)*projectionCollision μ ε w ≤ _ := hb'
    _ = _ := by field_simp
end GraphLiteralSupport.CurrentFalconer.Exceptional
end
end

end OAI
