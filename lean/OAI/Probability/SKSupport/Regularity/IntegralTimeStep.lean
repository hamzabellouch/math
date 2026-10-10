import Mathlib
import OAI.Probability.SKSupport.Moments.NormalFirstMoment
import OAI.Probability.SKSupport.Regularity.BoundedSmoothFamily
import OAI.Probability.SKSupport.Regularity.FamilyDifferentiation

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto
open Heat

lemma BoundedSmoothFamily_lipschitz {F : ℝ → ℝ → ℝ} (hF : BoundedSmoothFamily F) :
    ∃ L : ℝ≥0, ∀ t, LipschitzWith L (F t) := by
  obtain ⟨L,hL⟩ := hF.deriv.bound
  refine ⟨L,fun t => lipschitzWith_of_nnnorm_deriv_le
    ((hF.regular t).smooth.differentiable (by simp)) (fun x => ?_)⟩
  exact_mod_cast hL t x

lemma time_integral_spatial_bound {D : ℝ → ℝ → ℝ} (hD : BoundedSmoothFamily D)
    {L : ℝ≥0} (hL : ∀ t, LipschitzWith L (D t)) (a b x z : ℝ) :
    |(∫ r in a..b, D r z)-(∫ r in a..b, D r x)| ≤
      (L:ℝ)*|b-a| *|z-x| := by
  rw [← intervalIntegral.integral_sub (hD.intervalIntegrable z a b) (hD.intervalIntegrable x a b)]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun r => D r z-D r x) (C := (L:ℝ)*|z-x|)
    (fun r (_hr : r ∈ uIoc a b) => by
      simpa only [Real.norm_eq_abs] using (hL r).norm_sub_le z x)
  simpa only [Real.norm_eq_abs,mul_right_comm] using hh

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma integrable_family_comp [IsFiniteMeasure P] {F : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (t : ℝ) {Y : Ω → ℝ} (hY : Measurable Y) :
    Integrable (fun ω => F t (Y ω)) P := by
  obtain ⟨C,hC⟩ := hF.bound
  exact Integrable.of_bound (((hF.regular t).smooth.continuous.measurable).comp hY).aestronglyMeasurable
    C (Eventually.of_forall (fun ω => hC t (Y ω)))

lemma measurable_family_integral {D : ℝ → ℝ → ℝ} (hD : BoundedSmoothFamily D) (a b : ℝ) :
    Measurable (fun x => ∫ r in a..b, D r x) :=
  (show Differentiable ℝ (fun x => ∫ r in a..b, D r x) from
    fun x => (hD.hasDerivAt_integral a b x).differentiableAt).continuous.measurable

lemma integrable_family_integral_comp [IsFiniteMeasure P] {D : ℝ → ℝ → ℝ}
    (hD : BoundedSmoothFamily D) (a b : ℝ) {Y : Ω → ℝ} (hY : Measurable Y) :
    Integrable (fun ω => ∫ r in a..b, D r (Y ω)) P := by
  obtain ⟨C,hC⟩ := hD.bound
  apply Integrable.of_bound ((measurable_family_integral hD a b).comp hY).aestronglyMeasurable
    ((C:ℝ)*|b-a|)
  filter_upwards [] with ω
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun r _ => hC r (Y ω))

lemma expected_integral_time_step {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t)) (s h : ℝ≥0)
    {Y A : Ω → ℝ}
    (hY : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] Y)
    (hYi : Integrable Y P) (hA : Measurable A) (M : ℝ≥0)
    (hAb : ∀ ω, |A ω| ≤ (M:ℝ)*(h:ℝ)) {F D : ℝ → ℝ → ℝ}
    (hF : BoundedSmoothFamily F) (hD : BoundedSmoothFamily D)
    (C₁ C₂ C₃ L : ℝ≥0) (hC₁ : ∀ x, |deriv (F s) x| ≤ C₁)
    (hC₂ : ∀ x, |deriv (deriv (F s)) x| ≤ C₂)
    (hC₃ : ∀ x, |iteratedDeriv 3 (F s) x| ≤ C₃)
    (hL : ∀ r, LipschitzWith L (D r))
    (he : ∀ x, F ((s:ℝ)+(h:ℝ)) x-F s x = ∫ r in (s:ℝ)..((s:ℝ)+(h:ℝ)), D r x) :
    |(∫ ω, F ((s:ℝ)+(h:ℝ)) (Y ω+(B (s+h) ω-B s ω)+A ω) ∂P)-
      (∫ ω, F s (Y ω) ∂P)-(∫ ω, deriv (F s) (Y ω)*A ω ∂P)-
      (h:ℝ)/2*(∫ ω, deriv (deriv (F s)) (Y ω) ∂P)-
      (∫ ω, (∫ r in (s:ℝ)..((s:ℝ)+(h:ℝ)), D r (Y ω)) ∂P)| ≤
      (C₃:ℝ)/6*((h:ℝ)*Real.sqrt (h:ℝ)*normalThirdMoment)+
      (C₂:ℝ)*(M:ℝ)*(h:ℝ)*(Real.sqrt (h:ℝ)*normalFirstMoment+(M:ℝ)*(h:ℝ))+
      (L:ℝ)*(h:ℝ)*(Real.sqrt (h:ℝ)*normalFirstMoment+(M:ℝ)*(h:ℝ)) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hYm := hY.mono ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s) le_rfl
  let Z (ω : Ω) := Y ω+(B (s+h) ω-B s ω)+A ω
  have hZm : Measurable Z := (hYm.add ((hm _).sub (hm _))).add hA
  have hd : Integrable (fun ω => B (s+h) ω-B s ω) P :=
    (hB.integrable_eval _).sub (hB.integrable_eval _)
  let R (ω : Ω) := F ((s:ℝ)+(h:ℝ)) (Z ω)-F s (Z ω)-
    ∫ r in (s:ℝ)..((s:ℝ)+(h:ℝ)), D r (Y ω)
  have hiR : Integrable R P :=
    ((integrable_family_comp hF _ hZm).sub (integrable_family_comp hF _ hZm)).sub
      (integrable_family_integral_comp hD _ _ hYm)
  have hRb (ω : Ω) : |R ω| ≤ (L:ℝ)*(h:ℝ)*(|B (s+h) ω-B s ω|+(M:ℝ)*(h:ℝ)) := by
    dsimp only [R]
    rw [he]
    have hi := time_integral_spatial_bound hD hL (s:ℝ) ((s:ℝ)+(h:ℝ)) (Y ω) (Z ω)
    rw [add_sub_cancel_left,abs_of_nonneg h.coe_nonneg] at hi
    apply hi.trans
    have hz : |Z ω-Y ω| ≤ |B (s+h) ω-B s ω|+(M:ℝ)*(h:ℝ) := by
      have heq : Z ω-Y ω = (B (s+h) ω-B s ω)+A ω := by dsimp [Z]; ring
      rw [heq]
      exact (abs_add_le _ _).trans (add_le_add_right (hAb ω) _)
    exact mul_le_mul_of_nonneg_left hz (mul_nonneg L.coe_nonneg h.coe_nonneg)
  have hRe : |∫ ω, R ω ∂P| ≤
      (L:ℝ)*(h:ℝ)*(Real.sqrt (h:ℝ)*normalFirstMoment+(M:ℝ)*(h:ℝ)) := by
    calc
      _ ≤ ∫ ω, |R ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, (L:ℝ)*(h:ℝ)*(|B (s+h) ω-B s ω|+(M:ℝ)*(h:ℝ)) ∂P :=
        integral_mono hiR.abs ((hd.abs.add (integrable_const _)).const_mul _) hRb
      _ = _ := by
        rw [integral_const_mul,integral_add hd.abs (integrable_const _),increment_abs_first hB s h]
        simp
  have hRi : (∫ ω, R ω ∂P) =
      (∫ ω, F ((s:ℝ)+(h:ℝ)) (Z ω) ∂P)-(∫ ω, F s (Z ω) ∂P)-
      (∫ ω, (∫ r in (s:ℝ)..((s:ℝ)+(h:ℝ)), D r (Y ω)) ∂P) := by
    have h1 := integrable_family_comp (P := P) hF ((s:ℝ)+(h:ℝ)) hZm
    have h0 := integrable_family_comp (P := P) hF (s:ℝ) hZm
    have hdI := integrable_family_integral_comp (P := P) hD (s:ℝ) ((s:ℝ)+(h:ℝ)) hYm
    calc
      _ = (∫ ω, F ((s:ℝ)+(h:ℝ)) (Z ω)-F s (Z ω) ∂P)-
          (∫ ω, (∫ r in (s:ℝ)..((s:ℝ)+(h:ℝ)), D r (Y ω)) ∂P) :=
        integral_sub (h1.sub h0) hdI
      _ = _ := by rw [integral_sub h1 h0]

  have hS := expected_control_step hB hm s h hY hYi hA M hAb
    ((hF.regular s).smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)) C₁ C₂ C₃ hC₁ hC₂ hC₃
  rw [hRi] at hRe
  have ht := (abs_add_le
    ((∫ ω, F s (Z ω) ∂P)-(∫ ω, F s (Y ω) ∂P)-
      (∫ ω, deriv (F s) (Y ω)*A ω ∂P)-(h:ℝ)/2*(∫ ω, deriv (deriv (F s)) (Y ω) ∂P))
    ((∫ ω, F ((s:ℝ)+(h:ℝ)) (Z ω) ∂P)-(∫ ω, F s (Z ω) ∂P)-
      (∫ ω, (∫ r in (s:ℝ)..((s:ℝ)+(h:ℝ)), D r (Y ω)) ∂P))).trans
        (add_le_add hS hRe)
  convert ht using 1
  congr 1
  ring

end ZeroTemperatureSK.WeakIto

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto

lemma time_average_bound {f : ℝ → ℝ} {C a b : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t, |f t| ≤ C) : |(∫ t in a..b, f t)/(b-a)| ≤ C := by
  by_cases he : b=a
  · simp [he,hC]
  have hp : 0 < |b-a| := abs_pos.mpr (sub_ne_zero.mpr he)
  rw [abs_div,div_le_iff₀ hp]
  exact intervalIntegral.norm_integral_le_of_norm_le_const (f := f) (C := C) (fun t _ => by simpa only [Real.norm_eq_abs] using hb t)

lemma time_average_tendsto_right {f : ℝ → ℝ} (hm : Measurable f) (a : ℝ)
    (hc : ContinuousWithinAt f (Ioi a) a) :
    Tendsto (fun b => (∫ t in a..b, f t)/(b-a)) (𝓝[>] a) (𝓝 (f a)) := by
  have hh := intervalIntegral.integral_hasDerivWithinAt_right
    (a := a) (b := a) (s := Ici a) (t := Ioi a) IntervalIntegrable.refl
    hm.stronglyMeasurable.stronglyMeasurableAtFilter hc
  have hl := (hasDerivWithinAt_iff_tendsto_slope' (show a ∉ Ioi a by simp)).mp
    (hh.mono Ioi_subset_Ici_self)
  apply hl.congr
  intro b
  simp only [slope_def_field,intervalIntegral.integral_same,sub_zero]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma measurable_time_integral {f : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => f p.1 p.2)) (a b : ℝ) :
    Measurable (fun ω => ∫ t in a..b, f t ω) := by
  rw [show (fun ω => ∫ t in a..b, f t ω) =
    (fun ω => (∫ t in Ioc a b, f t ω)-(∫ t in Ioc b a, f t ω)) from rfl]
  exact hm.stronglyMeasurable.integral_prod_left.measurable.sub
    hm.stronglyMeasurable.integral_prod_left.measurable

lemma expected_time_average_tendsto_right [IsFiniteMeasure P] {f : ℝ → Ω → ℝ}
    (hm : Measurable (fun p : ℝ × Ω => f p.1 p.2)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ t ω, |f t ω| ≤ C) (a : ℝ)
    (hc : ∀ᵐ ω ∂P, ContinuousWithinAt (fun t => f t ω) (Ioi a) a) :
    Tendsto (fun b => ∫ ω, (∫ t in a..b, f t ω)/(b-a) ∂P)
      (𝓝[>] a) (𝓝 (∫ ω, f a ω ∂P)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => C)
  · exact Eventually.of_forall fun b => ((measurable_time_integral hm a b).div_const _).aestronglyMeasurable
  · exact Eventually.of_forall fun b => Eventually.of_forall fun ω =>
      time_average_bound hC (fun t => hb t ω)
  · exact integrable_const C
  · filter_upwards [hc] with ω hω
    exact time_average_tendsto_right (hm.comp measurable_prodMk_right) a hω

end ZeroTemperatureSK.WeakIto

end
end

end OAI
