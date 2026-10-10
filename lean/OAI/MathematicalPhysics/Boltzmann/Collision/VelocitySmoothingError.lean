import OAI.MathematicalPhysics.Boltzmann.Branching.L2PairingBound
import OAI.MathematicalPhysics.Boltzmann.Compactness.PairBoundedTruncation
import OAI.MathematicalPhysics.Boltzmann.Model
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

section

/-! # Smooth compact velocity cutoffs preserving a prescribed test -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.Compactness

theorem exists_velocity_cutoff {ψ : Velocity → ℝ} (hc : HasCompactSupport ψ) :
    ∃ β : Velocity → ℝ, ContDiff ℝ (⊤ : ℕ∞) β ∧ HasCompactSupport β ∧
      (∀ v, 0 ≤ β v) ∧ (∀ v, ψ v*β v = ψ v) := by
  obtain ⟨R,hR,hball⟩ := hc.isBounded.subset_ball_lt 0 (0 : Velocity)
  let b : ContDiffBump (0 : Velocity) := ⟨R,R+1,hR,by linarith⟩
  refine ⟨b,b.contDiff,b.hasCompactSupport,fun v => b.nonneg,fun v => ?_⟩
  by_cases hv : v ∈ tsupport ψ
  · have hb : v ∈ Metric.closedBall (0 : Velocity) b.rIn :=
      Metric.ball_subset_closedBall (hball hv)
    rw [b.one_of_mem_closedBall hb,mul_one]
  · rw [image_eq_zero_of_notMem_tsupport hv,zero_mul]

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Moving velocity translations onto bounded measurable tests -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X]

def velocityShift (a : Velocity) : (X × Velocity) ≃ᵐ (X × Velocity) where
  toFun p := (p.1,p.2+a)
  invFun p := (p.1,p.2-a)
  left_inv p := by simp only [add_sub_cancel_right]
  right_inv p := by simp only [sub_add_cancel]
  measurable_toFun := measurable_fst.prodMk (measurable_snd.add_const a)
  measurable_invFun := measurable_fst.prodMk (measurable_snd.sub_const a)

theorem velocityShift_preserving (μ : Measure X) [SFinite μ] (a : Velocity) :
    MeasurePreserving (velocityShift (X := X) a) (μ.prod volume) (μ.prod volume) :=
  (MeasurePreserving.id μ).prod (measurePreserving_add_right (volume : Measure Velocity) a)

theorem velocityShift_test (μ : Measure X) [SFinite μ] (F ψ : X × Velocity → ℝ) (a : Velocity) :
    (∫ p, ψ p*F (p.1,p.2+a) ∂μ.prod volume) =
      ∫ p, ψ (p.1,p.2-a)*F p ∂μ.prod volume := by
  have h := (velocityShift_preserving μ a).integral_comp (velocityShift a).measurableEmbedding
    (fun p => ψ (p.1,p.2-a)*F p)
  change (∫ p, ψ (p.1,p.2+a-a)*F (p.1,p.2+a) ∂μ.prod volume) = _ at h
  simpa only [add_sub_cancel_right] using h

theorem velocityShift_difference_test {μ : Measure X} [SFinite μ] {F ψ : X × Velocity → ℝ}
    (hF : Integrable F (μ.prod volume)) (hψ : Measurable ψ)
    {C : ℝ} (hC : ∀ z, |ψ z| ≤ C) (a : Velocity) :
    (∫ p, ψ p*(F (p.1,p.2+a)-F p) ∂μ.prod volume) =
      ∫ p, (ψ (p.1,p.2-a)-ψ p)*F p ∂μ.prod volume := by
  have hshift := (velocityShift_preserving μ a).integrable_comp_of_integrable hF
  have hA : Integrable (fun p => ψ p*F (p.1,p.2+a)) (μ.prod volume) :=
    hshift.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC)
  have hB := hF.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC)
  have hC' : Integrable (fun p => ψ (p.1,p.2-a)*F p) (μ.prod volume) :=
    hF.bdd_mul (hψ.comp (measurable_fst.prodMk (measurable_snd.sub_const a))).aestronglyMeasurable
      (ae_of_all _ (fun p => hC _))
  calc
    _ = (∫ p, ψ p*F (p.1,p.2+a) ∂μ.prod volume)-(∫ p, ψ p*F p ∂μ.prod volume) := by
      simp_rw [mul_sub]
      exact integral_sub hA hB
    _ = (∫ p, ψ (p.1,p.2-a)*F p ∂μ.prod volume)-(∫ p, ψ p*F p ∂μ.prod volume) := by
      rw [velocityShift_test]
    _ = _ := by
      simp_rw [sub_mul]
      exact (integral_sub hC' hB).symm

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # A countable smooth exhaustion of velocity space -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness

def velocityExhaustionBump (j : ℕ) : ContDiffBump (0 : Velocity) :=
  ⟨(j:ℝ)+1,(j:ℝ)+2,by positivity,by linarith⟩

def velocityExhaustion (j : ℕ) : Velocity → ℝ := velocityExhaustionBump j

theorem velocityExhaustion_smooth (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (velocityExhaustion j) := (velocityExhaustionBump j).contDiff

theorem velocityExhaustion_compact (j : ℕ) : HasCompactSupport (velocityExhaustion j) :=
  (velocityExhaustionBump j).hasCompactSupport

theorem velocityExhaustion_nonneg (j : ℕ) (v : Velocity) : 0 ≤ velocityExhaustion j v :=
  (velocityExhaustionBump j).nonneg

theorem velocityExhaustion_le_one (j : ℕ) (v : Velocity) : velocityExhaustion j v ≤ 1 :=
  (velocityExhaustionBump j).le_one

theorem velocityExhaustion_eq_one (j : ℕ) (v : Velocity) (hv : ‖v‖ ≤ (j:ℝ)+1) :
    velocityExhaustion j v = 1 := by
  apply (velocityExhaustionBump j).one_of_mem_closedBall
  simpa only [Metric.mem_closedBall,dist_zero_right,velocityExhaustionBump] using hv

theorem velocityExhaustion_error_tendsto (C : ℝ) :
    Tendsto (fun j : ℕ => ENNReal.ofReal (C/((j:ℝ)+1)^2)) atTop (𝓝 0) := by
  have hd : Tendsto (fun j : ℕ => 1/((j:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h : Tendsto (fun j : ℕ => C*(1/((j:ℝ)+1))^2) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero] using tendsto_const_nhds.mul (hd.pow 2)
  have he (j : ℕ) : C/((j:ℝ)+1)^2 = C*(1/((j:ℝ)+1))^2 := by
    simp only [div_eq_mul_inv,one_mul,inv_pow]
  simpa only [he,ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal h

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Integration of velocity translations against a finite convolution kernel -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

def parameterShift (z : Velocity × (X × Velocity)) : Velocity × (X × Velocity) :=
  (z.1,(z.2.1,z.2.2-z.1))

theorem parameterShift_measurable : Measurable (parameterShift (X := X)) :=
  measurable_fst.prodMk (measurable_snd.fst.prodMk (measurable_snd.snd.sub measurable_fst))

theorem parameterShift_preserving : MeasurePreserving (parameterShift (X := X))
    ((volume : Measure Velocity).prod (μ.prod volume))
    ((volume : Measure Velocity).prod (μ.prod volume)) := by
  have hmap (a : Velocity) :
      MeasurePreserving (fun p : X × Velocity => (p.1,p.2-a)) (μ.prod volume) (μ.prod volume) := by
    have he : (fun p : X × Velocity => (p.1,p.2-a)) = ⇑(velocityShift (X := X) (-a)) := by
      funext p
      exact Prod.ext rfl (sub_eq_add_neg p.2 a)
    rw [he]
    exact velocityShift_preserving μ (-a)
  exact (MeasurePreserving.id (volume : Measure Velocity)).skew_product
    (g := fun (a : Velocity) (p : X × Velocity) => (p.1,p.2-a))
    (by fun_prop) (ae_of_all _ (fun a => (hmap a).map_eq))

theorem integrable_velocity_kernel {χ : Velocity → ℝ} {F : X × Velocity → ℝ}
    (hχ : Integrable χ) (hF : Integrable F (μ.prod volume)) :
    Integrable (fun z : Velocity × (X × Velocity) => χ z.1*F (z.2.1,z.2.2-z.1))
      ((volume : Measure Velocity).prod (μ.prod volume)) := by
  have hi := parameterShift_preserving.integrable_comp_of_integrable (hχ.mul_prod hF)
  exact hi

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

section

/-! # The pointwise Fourier estimate for the actual velocity multiplier -/
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
namespace BoltzmannNonuniqueness.Published

attribute [local irreducible] complexVelocityMultiplier velocityMultiplierMass velocityMultiplier

theorem velocity_spectral_bound (R : ℝ) (n : ℕ) (k : SpaceTime)
    (r : Lp ℂ 2 (volume.restrict (Metric.closedBall (0 : Velocity) R))) :
    ‖∫ v in Metric.closedBall (0 : Velocity) R, complexVelocityMultiplier n k v*r v‖^2 ≤
      velocityMultiplierMass R n k * ‖r‖^2 := by
  let μ : Measure Velocity := volume.restrict (Metric.closedBall 0 R)
  have : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Velocity) R).measure_lt_top.ne
  have hmc : Continuous (fun v => conj (complexVelocityMultiplier n k v)) :=
    Complex.continuous_conj.comp ((complexVelocityMultiplier_continuous n).comp
      (continuous_const.prodMk continuous_id))
  have hm : MemLp (fun v => conj (complexVelocityMultiplier n k v)) 2 μ :=
    (memLp_const (1 : ℂ)).of_le hmc.aestronglyMeasurable
      (ae_of_all _ (fun v => by simpa using complexVelocityMultiplier_norm_le_one n k v))
  let a : Lp ℂ 2 μ := hm.toLp _
  have ha : (a : Velocity → ℂ) =ᵐ[μ] fun v => conj (complexVelocityMultiplier n k v) :=
    MemLp.coeFn_toLp _
  have he : (∫ v, complexVelocityMultiplier n k v*r v ∂μ) = inner ℂ a r := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha] with v hv
    simp [hv,RCLike.inner_apply,mul_comm]
  have hn : ‖a‖^2 = velocityMultiplierMass R n k := by
    rw [L2_norm_sq_integral,velocityMultiplierMass]
    apply integral_congr_ae
    filter_upwards [ha] with v hv
    rw [hv,Complex.norm_conj,complexVelocityMultiplier_norm_sq]
  change ‖∫ v, complexVelocityMultiplier n k v*r v ∂μ‖^2 ≤ _
  rw [he,← hn,← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm a r) 2

end BoltzmannNonuniqueness.Published

end

end

section

/-! # An L1 error bound for velocity smoothing by a probability kernel -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

def velocitySmooth (χ : Velocity → ℝ) (F : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  ∫ a : Velocity, χ a*F (p.1,p.2-a)

theorem velocitySmooth_integrable {χ : Velocity → ℝ} {F : X × Velocity → ℝ}
    (hχ : Integrable χ) (hF : Integrable F (μ.prod volume)) :
    Integrable (velocitySmooth χ F) (μ.prod volume) :=
  (integrable_velocity_kernel hχ hF).integral_prod_right

theorem velocitySmooth_difference {χ : Velocity → ℝ} {F : X × Velocity → ℝ}
    (hχ : Integrable χ) (hF : Integrable F (μ.prod volume)) (hmass : (∫ a, χ a) = 1) :
    (fun p => velocitySmooth χ F p-F p) =ᵐ[μ.prod volume]
      fun p => ∫ a : Velocity, χ a*(F (p.1,p.2-a)-F p) := by
  filter_upwards [(integrable_velocity_kernel hχ hF).prod_left_ae] with p hp
  change (∫ a : Velocity, χ a*F (p.1,p.2-a))-F p = _
  calc
    _ = (∫ a : Velocity, χ a*F (p.1,p.2-a))-(∫ a : Velocity, χ a*F p) := by
      rw [integral_mul_const,hmass,one_mul]
    _ = ∫ a : Velocity, χ a*F (p.1,p.2-a)-χ a*F p := (integral_sub hp (hχ.mul_const (F p))).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun _ => (mul_sub _ _ _).symm)

theorem velocitySmooth_error_le {χ : Velocity → ℝ} {F : X × Velocity → ℝ}
    (hχ : Integrable χ) (hF : Integrable F (μ.prod volume))
    (hχ0 : ∀ a, 0 ≤ χ a) (hmass : (∫ a, χ a) = 1) {ε : ℝ}
    (hsmall : ∀ a, χ a ≠ 0 →
      (∫ p, |F (p.1,p.2-a)-F p| ∂μ.prod volume) ≤ ε) :
    (∫ p, |velocitySmooth χ F p-F p| ∂μ.prod volume) ≤ ε := by
  let A : Velocity × (X × Velocity) → ℝ :=
    fun z => χ z.1*(F (z.2.1,z.2.2-z.1)-F z.2)
  have hAi : Integrable A ((volume : Measure Velocity).prod (μ.prod volume)) := by
    apply ((integrable_velocity_kernel hχ hF).sub (hχ.mul_prod hF)).congr
    exact ae_of_all _ (fun z => (mul_sub _ _ _).symm)
  have hnorm a : (∫ p, ‖A (a,p)‖ ∂μ.prod volume) =
      χ a*(∫ p, |F (p.1,p.2-a)-F p| ∂μ.prod volume) := by
    simp only [A,Real.norm_eq_abs,abs_mul,abs_of_nonneg (hχ0 a)]
    exact integral_const_mul _ _
  calc
    _ = ∫ p, |∫ a : Velocity, A (a,p)| ∂μ.prod volume := by
      apply integral_congr_ae
      filter_upwards [velocitySmooth_difference hχ hF hmass] with p hp
      exact congrArg abs hp
    _ ≤ ∫ p, (∫ a : Velocity, ‖A (a,p)‖) ∂μ.prod volume := by
      apply integral_mono hAi.integral_prod_right.norm hAi.integral_norm_prod_right
      intro p
      exact norm_integral_le_integral_norm _
    _ = ∫ a : Velocity, (∫ p, ‖A (a,p)‖ ∂μ.prod volume) :=
      (integral_integral_swap hAi.norm).symm
    _ ≤ ∫ a : Velocity, χ a*ε := by
      apply integral_mono_ae hAi.norm.integral_prod_left (hχ.mul_const ε)
      filter_upwards [] with a
      rw [hnorm]
      by_cases ha : χ a = 0
      · simp only [ha,zero_mul,le_refl]
      · exact mul_le_mul_of_nonneg_left (hsmall a ha) (hχ0 a)
    _ = ε := by rw [integral_mul_const,hmass,one_mul]

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
