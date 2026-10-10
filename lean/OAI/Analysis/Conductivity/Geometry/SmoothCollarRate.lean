import Mathlib
import OAI.Analysis.Conductivity.Geometry.PhysicalCollarBand
import OAI.Analysis.Conductivity.Fourier.PoissonTraceRate
import OAI.Analysis.Conductivity.Fourier.AttachedEndPoisson

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal

lemma sourceAngular_time_displacement (t b : ℝ) (θ : UnitAddTorus (Fin 2)) :
    ‖sourceAngularCollar t θ-sourceAngularCollar b θ‖≤8*|t-b| := by
  rw [show sourceAngularCollar t θ=sourceAngularCollar b θ+(t-b) • sourceAngularVelocity θ by
    simpa only [add_sub_cancel] using sourceAngular_affine b (t-b) θ,add_sub_cancel_left,norm_smul,
    Real.norm_eq_abs]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (sourceAngularVelocity_norm θ) (abs_nonneg (t-b))

lemma smooth_sourceCollar_lipschitz {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) :
    ∃ K : ℝ≥0,LipschitzOnWith K q (sourceClosedCollarBand (-(1:ℝ)/100) (1/100)) := by
  obtain ⟨R,hR⟩ := (isCompact_sourceClosedCollarBand (le_refl _) (le_refl _)).isBounded.subset_closedBall 0
  obtain ⟨K,hK⟩ := hq.contDiffOn.exists_lipschitzOnWith (s:=Metric.closedBall 0 R)
    (by simp) (convex_closedBall (0:Fin 3 → ℝ) R) (isCompact_closedBall _ _)
  exact ⟨K,hK.mono hR⟩

lemma smooth_sourceCollar_value_displacement {q : (Fin 3 → ℝ) → ℝ} {K : ℝ≥0}
    (hK : LipschitzOnWith K q (sourceClosedCollarBand (-(1:ℝ)/100) (1/100)))
    {t b : ℝ} (ht : t∈Icc (-(1:ℝ)/100) (1/100)) (hb : b∈Icc (-(1:ℝ)/100) (1/100))
    (θ : UnitAddTorus (Fin 2)) :
    |q (sourceAngularCollar t θ)-q (sourceAngularCollar b θ)|≤8*(K:ℝ)*|t-b| := by
  have ht' : sourceAngularCollar t θ∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) := by
    change sourceCollarTime (sourceAngularCollar t θ)∈Icc (-(1:ℝ)/100) (1/100)
    rw [sourceAngular_time ht]; exact ht
  have hb' : sourceAngularCollar b θ∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) := by
    change sourceCollarTime (sourceAngularCollar b θ)∈Icc (-(1:ℝ)/100) (1/100)
    rw [sourceAngular_time hb]; exact hb
  have H := (hK.dist_le_mul _ ht' _ hb').trans
    (mul_le_mul_of_nonneg_left (sourceAngular_time_displacement t b θ) K.coe_nonneg)
  simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs,mul_assoc,mul_left_comm] using H

local instance smoothCollarRateMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance smoothCollarRateProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma endPoissonField_eq_traceFlow {s : Fin 3 → ℝ}
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (q : C(UnitAddTorus (Fin 2),ℂ))
    (hq : ∀ h,f.val 0 h=mFourierCoeff q h) {t : ℝ} (ht : 0<t) (θ : UnitAddTorus (Fin 2)) :
    endPoissonField s f 0 (t,θ)=torusPoissonContinuous s t (q.toLp 2 volume ℂ) θ := by
  rw [torusPoissonContinuous_apply hs ht]
  unfold endPoissonField
  apply tsum_congr
  intro h
  simp only [endPoissonModeField,endModeCoefficient,Matrix.cons_val_zero,hq,mFourierCoeff_toLp]

lemma smooth_attachedEnd_fiber_rate {s : Fin 3 → ℝ}
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) {K : ℝ≥0}
    (hK : LipschitzOnWith K q (sourceClosedCollarBand (-(1:ℝ)/100) (1/100)))
    {a b t : ℝ} (hb : b∈Icc (-(1:ℝ)/100) (1/100)) (ht : t∈Icc (-(1:ℝ)/100) (1/100))
    (hpos : 0<a*(t-b)) (htrace : ∀ h,f.val 0 h=mFourierCoeff
      (fun θ => (q (sourceAngularCollar b θ):ℂ)) h)
    (g : SpectralL2 TorusModes) (hg : ∀ h,g h=(torusRate s h:ℂ)*f.val 0 h) :
    (∫ θ,((attachedEndPoissonField s f a b 0 (sourceAngularCollar t θ)).re-
      q (sourceAngularCollar t θ))^2)≤(2*a^2*‖g‖^2+2*(8*(K:ℝ))^2)*(t-b)^2 := by
  let Q : C(UnitAddTorus (Fin 2),ℂ) := ⟨fun θ => (q (sourceAngularCollar b θ):ℂ),
    Complex.continuous_ofReal.comp (hq.continuous.comp (continuous_sourceAngularCollar b))⟩
  let P := torusPoissonContinuous s (a*(t-b)) (Q.toLp 2 volume ℂ)
  have he (θ : UnitAddTorus (Fin 2)) :
      attachedEndPoissonField s f a b 0 (sourceAngularCollar t θ)=P θ :=
    (attachedEndPoissonField_angular s f a b 0 ht θ).trans
      (endPoissonField_eq_traceFlow hs f Q htrace hpos θ)
  have hP : Continuous (fun θ => (P θ).re-q (sourceAngularCollar t θ)) :=
    (Complex.continuous_re.comp P.continuous).sub (hq.continuous.comp (continuous_sourceAngularCollar t))
  simp_rw [he]
  have hbound (θ : UnitAddTorus (Fin 2)) :
      ((P θ).re-q (sourceAngularCollar t θ))^2≤
      2*‖P θ-Q θ‖^2+2*(8*(K:ℝ)*|t-b|)^2 := by
    have hp := Complex.abs_re_le_norm (P θ-Q θ)
    have hq' := smooth_sourceCollar_value_displacement hK ht hb θ
    have hq'' : |q (sourceAngularCollar b θ)-q (sourceAngularCollar t θ)|≤8*(K:ℝ)*|t-b| := by
      rwa [abs_sub_comm] at hq'
    have h1 := pow_le_pow_left₀ (abs_nonneg _) hp 2
    have h2 := pow_le_pow_left₀ (abs_nonneg _) hq'' 2
    simp only [sq_abs,Complex.sub_re,Complex.ofReal_re,Q,ContinuousMap.coe_mk] at h1 h2
    dsimp only [Q,ContinuousMap.coe_mk]
    nlinarith [sq_nonneg ((P θ).re-q (sourceAngularCollar b θ)-
      (q (sourceAngularCollar b θ)-q (sourceAngularCollar t θ)))]
  have hpint : Integrable (fun θ => ‖P θ-Q θ‖^2) :=
    (((P.continuous.sub Q.continuous).norm).pow 2).integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
  have hfin : Integrable (fun θ => ((P θ).re-q (sourceAngularCollar t θ))^2) :=
    (hP.pow 2).integrable_of_hasCompactSupport (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
  have H := integral_mono hfin ((hpint.const_mul 2).add (integrable_const _)) hbound
  simp only [Pi.add_apply] at H
  rw [integral_add (hpint.const_mul 2) (integrable_const _),integral_const_mul,integral_const] at H
  have hrate : (∫ θ,‖P θ-Q θ‖^2)≤(a*(t-b))^2*‖g‖^2 :=
    torusPoissonContinuous_trace_sq hs hpos Q g (fun h => by rw [hg,mFourierCoeff_toLp,htrace]; rfl)
  simp only [probReal_univ,one_smul] at H
  calc
    _ ≤ 2*((a*(t-b))^2*‖g‖^2)+2*(8*(K:ℝ)*|t-b|)^2 := by linarith
    _ = _ := by rw [mul_pow,mul_pow,sq_abs]; ring

end ScalarConductivity

end

end OAI
