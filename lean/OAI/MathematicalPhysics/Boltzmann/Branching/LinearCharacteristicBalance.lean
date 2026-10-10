import OAI.MathematicalPhysics.Boltzmann.Branching.LogRenormalization
import OAI.MathematicalPhysics.Boltzmann.Branching.VariableSurvival
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityCutoffEntropyError

namespace OAI

section

/-! # A logarithmic gain estimate for a nonnegative characteristic path -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.TransportPrimitive

theorem logarithmic_gain_bound {T m : ℝ} (hT : 0 ≤ T) (hm : 0 < m)
    {U k g : ℝ → ℝ} (hU : AbsolutelyContinuousOnInterval U 0 T)
    (hUn : ∀ t ∈ Icc 0 T, 0 ≤ U t)
    (hk : IntervalIntegrable k volume 0 T) (hg : IntervalIntegrable g volume 0 T)
    (hkn : ∀ t ∈ Icc 0 T, 0 ≤ k t)
    (hd : ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt U (g t-k t*U t) t) :
    (∫ t in 0..T, g t/(1+U t/m)) ≤ U T+m*(∫ t in 0..T, k t) := by
  have hpos t (ht : t ∈ Icc 0 T) : 0 < 1+U t/m := by
    have := hUn t ht
    positivity
  have hUc : ContinuousOn U (Icc 0 T) := by simpa only [uIcc_of_le hT] using hU.continuousOn
  have hc : ContinuousOn (fun t => (1+U t/m)⁻¹) (Icc 0 T) :=
    (continuousOn_const.add (hUc.div_const m)).inv₀ (fun t ht => (hpos t ht).ne')
  have hc' : ContinuousOn (fun t => (1+U t/m)⁻¹) (uIcc 0 T) := by
    simpa only [uIcc_of_le hT] using hc
  have hu' : ContinuousOn U (uIcc 0 T) := hU.continuousOn
  have hgi : IntervalIntegrable (fun t => g t/(1+U t/m)) volume 0 T := by
    simpa only [div_eq_mul_inv] using hg.mul_continuousOn hc'
  have hki : IntervalIntegrable (fun t => k t*U t/(1+U t/m)) volume 0 T := by
    have hcU : ContinuousOn (fun t => U t*(1+U t/m)⁻¹) (uIcc 0 T) := hu'.mul hc'
    simpa only [div_eq_mul_inv,mul_assoc] using hk.mul_continuousOn hcU
  have he := Renormalization.logarithm.weighted_chain_rule hT hm hU hUn hd
  dsimp only [Renormalization.logarithm] at he
  have he' : (∫ t in 0..T, g t/(1+U t/m))-
      (∫ t in 0..T, k t*U t/(1+U t/m)) =
      m*Real.log (1+U T/m)-m*Real.log (1+U 0/m) := by
    rw [← intervalIntegral.integral_sub hgi hki]
    change _ = _ at he
    convert he using 1
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc 0 T := by simpa only [uIcc_of_le hT] using ht
    change g t/(1+U t/m)-k t*U t/(1+U t/m) =
      derivWithin (fun x : ℝ => Real.log (1+x)) (Ici 0) (U t/m)*(g t-k t*U t)
    rw [Renormalization.logOneAdd_derivWithin (div_nonneg (hUn t ht') hm.le)]
    ring
  have hL : (∫ t in 0..T, k t*U t/(1+U t/m)) ≤ m*(∫ t in 0..T, k t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hT hki (hk.const_mul m)
    intro t ht
    have hu : U t/(1+U t/m) ≤ m := by
      apply (div_le_iff₀ (hpos t ht)).mpr
      have hm' : m ≠ 0 := hm.ne'
      field_simp
      nlinarith
    calc
      _ = k t*(U t/(1+U t/m)) := by ring
      _ ≤ k t*m := mul_le_mul_of_nonneg_left hu (hkn t ht)
      _ = _ := by ring
  have hE := Renormalization.weighted_log_le_self hm (hUn T ⟨hT,le_rfl⟩)
  have h0 : 0 ≤ m*Real.log (1+U 0/m) := mul_nonneg hm.le
    (Real.log_nonneg (by have := div_nonneg (hUn 0 ⟨le_rfl,hT⟩) hm.le; linarith))
  linarith

end BoltzmannNonuniqueness.TransportPrimitive

end

end

section

/-! # The positive linear characteristic solution with locally integrable data -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.TransportPrimitive

def linearSolution (a : ℝ) (k g : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(∫ s in 0..t, k s))*(a+
    ∫ s in 0..t, Real.exp (∫ r in 0..s, k r)*g s)

theorem linearSolution_initial (a : ℝ) (k g : ℝ → ℝ) : linearSolution a k g 0 = a := by
  simp [linearSolution]

theorem linearSolution_formula (a : ℝ) (k g : ℝ → ℝ) (t : ℝ) :
    linearSolution a k g t = Real.exp (-(∫ s in 0..t, k s))*a+
      ∫ s in 0..t, Real.exp (-((∫ r in 0..t, k r)-(∫ r in 0..s, k r)))*g s := by
  rw [linearSolution,mul_add,← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [← mul_assoc,← Real.exp_add]
  congr 2
  ring

theorem linearSolution_absolutelyContinuous {T : ℝ} (a : ℝ) {k g : ℝ → ℝ}
    (hk : IntervalIntegrable k volume 0 T) (hg : IntervalIntegrable g volume 0 T) :
    AbsolutelyContinuousOnInterval (linearSolution a k g) 0 T := by
  let K t := ∫ s in 0..t, k s
  have hK : AbsolutelyContinuousOnInterval K 0 T :=
    hk.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have he := exp_absolutelyContinuous hK
  have hgi : IntervalIntegrable (fun t => Real.exp (K t)*g t) volume 0 T :=
    hg.continuousOn_mul he.continuousOn
  have hG := hgi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => a) 0 T :=
    (LipschitzWith.const a).lipschitzOnWith.absolutelyContinuousOnInterval
  exact (exp_absolutelyContinuous hK.neg).mul (hc.add hG)

theorem linearSolution_hasDerivAt_ae {T : ℝ} (hT : 0 ≤ T) (a : ℝ) {k g : ℝ → ℝ}
    (hk : IntervalIntegrable k volume 0 T) (hg : IntervalIntegrable g volume 0 T) :
    ∀ᵐ t ∂volume, t ∈ Icc 0 T →
      HasDerivAt (linearSolution a k g) (g t-k t*linearSolution a k g t) t := by
  let K t := ∫ s in 0..t, k s
  have hK : AbsolutelyContinuousOnInterval K 0 T :=
    hk.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hgi : IntervalIntegrable (fun t => Real.exp (K t)*g t) volume 0 T :=
    hg.continuousOn_mul (exp_absolutelyContinuous hK).continuousOn
  filter_upwards [hk.ae_hasDerivAt_integral,hgi.ae_hasDerivAt_integral] with t hkt hgt ht
  have htm : t ∈ uIcc 0 T := by simpa only [uIcc_of_le hT] using ht
  have hkd : HasDerivAt K (k t) t := hkt htm 0 left_mem_uIcc
  have hgd := (hgt htm 0 left_mem_uIcc).const_add a
  have hd := hkd.neg.exp.mul hgd
  have he : Real.exp (-K t)*Real.exp (K t) = 1 := by
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  change HasDerivAt (linearSolution a k g)
    (Real.exp (-K t)*(-k t)*(a+∫ s in 0..t, Real.exp (K s)*g s)+
      Real.exp (-K t)*(Real.exp (K t)*g t)) t at hd
  convert hd using 1
  change g t-k t*(Real.exp (-K t)*(a+∫ s in 0..t, Real.exp (K s)*g s)) =
    Real.exp (-K t)*(-k t)*(a+∫ s in 0..t, Real.exp (K s)*g s)+
      Real.exp (-K t)*(Real.exp (K t)*g t)
  rw [← mul_assoc (Real.exp (-K t)) (Real.exp (K t)),he,one_mul]
  ring

end BoltzmannNonuniqueness.TransportPrimitive

end

end

section

/-! # Stability of a signed characteristic equation with nonnegative damping -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.TransportPrimitive

theorem linear_path_eq_solution {T : ℝ} (hT : 0 ≤ T) {u k r : ℝ → ℝ}
    (hu : AbsolutelyContinuousOnInterval u 0 T)
    (hk : IntervalIntegrable k volume 0 T) (hr : IntervalIntegrable r volume 0 T)
    (hd : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt u (r t-k t*u t) t) :
    u T = linearSolution (u 0) k r T := by
  have hl := variable_survival_with_source hT hu hk hr hd
    (ae_of_all _ (fun _ _ => le_rfl))
  have hdn : ∀ᵐ t, t ∈ Icc 0 T →
      HasDerivAt (fun s => -u s) ((-r t)-k t*(-u t)) t := by
    filter_upwards [hd] with t ht hmem
    convert (ht hmem).neg using 1
    ring
  have hn := variable_survival_with_source hT hu.neg hk hr.neg hdn
    (ae_of_all _ (fun _ _ => le_rfl))
  simp only [Pi.neg_apply,mul_neg,intervalIntegral.integral_neg] at hn
  rw [linearSolution_formula]
  linarith

theorem damped_path_abs_le {T : ℝ} (hT : 0 ≤ T) {u k r : ℝ → ℝ}
    (hu : AbsolutelyContinuousOnInterval u 0 T)
    (hk : IntervalIntegrable k volume 0 T) (hr : IntervalIntegrable r volume 0 T)
    (hk0 : ∀ t ∈ Icc 0 T, 0 ≤ k t)
    (hd : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt u (r t-k t*u t) t) :
    |u T| ≤ |u 0|+∫ t in 0..T, |r t| := by
  rw [linear_path_eq_solution hT hu hk hr hd,linearSolution_formula]
  have hK : 0 ≤ ∫ t in 0..T, k t := intervalIntegral.integral_nonneg hT hk0
  have he : Real.exp (-(∫ t in 0..T, k t)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hK)
  have hs : |Real.exp (-(∫ t in 0..T, k t))*u 0| ≤ |u 0| := by
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (abs_nonneg _) he
  have hkae : 0 ≤ᵐ[volume.restrict (Ioc 0 T)] k := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hk0 t ⟨ht.1.le,ht.2⟩
  have hsource : |∫ t in 0..T,
      Real.exp (-((∫ s in 0..T, k s)-(∫ s in 0..t, k s)))*r t| ≤
      ∫ t in 0..T, |r t| := by
    have hb : ∀ᵐ t ∂volume, t ∈ Ioc 0 T →
        ‖Real.exp (-((∫ s in 0..T, k s)-(∫ s in 0..t, k s)))*r t‖ ≤ ‖r t‖ := by
      filter_upwards [] with t ht
      have hKt : (∫ s in 0..t, k s) ≤ ∫ s in 0..T, k s :=
        intervalIntegral.integral_mono_interval le_rfl ht.1.le ht.2 hkae hk
      have hex : Real.exp (-((∫ s in 0..T, k s)-(∫ s in 0..t, k s))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith)
      rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_left (abs_nonneg _) hex
    simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_of_norm_le hT hb hr.norm
  exact (abs_add_le _ _).trans (add_le_add hs hsource)

end BoltzmannNonuniqueness.TransportPrimitive

end

end

section

/-! # Integrability of the linear velocity tests used for conserved moments -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

theorem linearVelocityTest_integrable {μ : Measure (X × Velocity)}
    {F : X × Velocity → ℝ} (hF : Measurable F) (hFn : ∀ p, 0 ≤ F p)
    (hFi : Integrable (entropyGauge F) μ) {ψ : Velocity → ℝ}
    (hψ : Measurable ψ) (D : ℝ≥0) (hD : ∀ v, |ψ v| ≤ D*(1+‖v‖)) :
    Integrable (fun p => ψ p.2*F p) μ := by
  apply ((linearMoment_integrable hF hFn hFi).const_mul (D:ℝ)).mono'
    ((hψ.comp measurable_snd).mul hF).aestronglyMeasurable
  filter_upwards [] with p
  change ‖ψ p.2*F p‖ ≤ (D:ℝ)*linearMoment F p
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hFn p)]
  simpa only [linearMoment,mul_assoc] using
    mul_le_mul_of_nonneg_right (hD p.2) (hFn p)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The linear characteristic solution satisfies its exact integral balance -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.TransportPrimitive

theorem linearSolution_balance {T : ℝ} (hT : 0 ≤ T) (a : ℝ) {k g : ℝ → ℝ}
    (hk : IntervalIntegrable k volume 0 T) (hg : IntervalIntegrable g volume 0 T) :
    linearSolution a k g T = a+
      ∫ t in 0..T, g t-k t*linearSolution a k g t := by
  have hu := linearSolution_absolutelyContinuous a hk hg
  have hd := linearSolution_hasDerivAt_ae hT a hk hg
  have he : (∫ t in 0..T, g t-k t*linearSolution a k g t) =
      ∫ t in 0..T, deriv (linearSolution a k g) t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hd] with t ht hmem
    exact (ht (by simpa only [uIcc_of_le hT] using uIoc_subset_uIcc hmem)).deriv.symm
  rw [he,hu.integral_deriv_eq_sub,linearSolution_initial]
  ring

end BoltzmannNonuniqueness.TransportPrimitive

end

end

end OAI
