import Mathlib
import OAI.Probability.SKSupport.Moments.StripSquareMoment
import OAI.Probability.SKSupport.Regularity.PositiveRegularity
import OAI.Probability.SKSupport.Foundations.RightCoeffApprox

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.BoundedLipschitzDrift
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma solution_stability_on (b b' : BoundedLipschitzDrift) (ℱ : Filtration ℝ≥0 mΩ)
    {B : ℝ≥0 → Ω → ℝ} (hB : IsProgressive ℱ B) (T : ℝ≥0) {E : ℝ} (hE : 0 ≤ E)
    (ω : Ω)
    (he : ∀ t ≤ T, |timePrimitive (b.action B (b'.correction B)) t ω-b'.correction B t ω| ≤ E)
    (t : ℝ≥0) (ht : t ≤ T) :
    |b.solution B t ω-b'.solution B t ω| ≤ 2*E*Real.exp (b.rate*t) := by
  let A : ℝ := ((b.bound:ℝ)+(b'.bound:ℝ))*(T:ℝ)
  have hA : 0 ≤ A := by dsimp [A];positivity
  have hbase (s : ℝ≥0) (hs : s ≤ T) : |b.correction B s ω-b'.correction B s ω| ≤ A := by
    apply (abs_sub _ _).trans
    have hb := b.correction_bound ℱ hB s ω
    have hb' := b'.correction_bound ℱ hB s ω
    have hst : (s:ℝ) ≤ T := hs
    dsimp [A]
    nlinarith [b.bound.coe_nonneg,b'.bound.coe_nonneg]
  have hest (n : ℕ) (s : ℝ≥0) (hs : s ≤ T) :
      |b.correction B s ω-b'.correction B s ω| ≤ (2*E+A*(1/2:ℝ)^n)*Real.exp (b.rate*s) := by
    induction n generalizing s with
    | zero =>
      simp only [pow_zero,mul_one]
      apply (hbase s hs).trans
      have hex : 1 ≤ Real.exp (b.rate*s) := Real.one_le_exp (mul_nonneg b.rate_pos.le s.coe_nonneg)
      nlinarith
    | succ n ih =>
      have hh := b.timePrimitive_action_sub_estimate ℱ hB (b.correction_progressive ℱ hB)
        (b'.correction_progressive ℱ hB) (show 0 ≤ 2*E+A*(1/2:ℝ)^n by positivity)
        s ω (fun u hu => ih u (hu.trans hs))
      rw [← b.correction_eq_integral ℱ hB] at hh
      have htri := abs_sub_le (b.correction B s ω)
        (timePrimitive (b.action B (b'.correction B)) s ω) (b'.correction B s ω)
      have her := he s hs
      have hex : 1 ≤ Real.exp (b.rate*s) := Real.one_le_exp (mul_nonneg b.rate_pos.le s.coe_nonneg)
      rw [pow_succ]
      nlinarith [mul_le_mul_of_nonneg_left hex hE]
  have hlim : Tendsto (fun n : ℕ => (2*E+A*(1/2:ℝ)^n)*Real.exp (b.rate*t)) atTop
      (𝓝 (2*E*Real.exp (b.rate*t))) := by
    have hh := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)
    simpa only [mul_zero,add_zero] using (tendsto_const_nhds.add (tendsto_const_nhds.mul hh) (a := 2*E)).mul_const (Real.exp (b.rate*t))
  have hh := ge_of_tendsto hlim (Eventually.of_forall (fun n => hest n t ht))
  simpa only [solution,add_sub_add_left_eq_sub] using hh

end ZeroTemperatureSK.BoundedLipschitzDrift

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.BoundedLipschitzDrift
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma residual_integral_bound (b b' : BoundedLipschitzDrift) (ℱ : Filtration ℝ≥0 mΩ)
    {B : ℝ≥0 → Ω → ℝ} (hB : IsProgressive ℱ B) (T : ℝ≥0) {e : ℝ → ℝ}
    (hei : IntervalIntegrable e volume 0 T)
    (hen : ∀ s ∈ Icc (0:ℝ) T, 0 ≤ e s)
    (he : ∀ᵐ s : ℝ, s ∈ Icc (0:ℝ) T → ∀ x, |b.f s x-b'.f s x| ≤ e s)
    (t : ℝ≥0) (ht : t ≤ T) (ω : Ω) :
    |timePrimitive (b.action B (b'.correction B)) t ω-b'.correction B t ω| ≤ ∫ s in (0:ℝ)..(T:ℝ), e s := by
  have hZ := b'.correction_progressive ℱ hB
  have hi := progressive_bounded_integrable ℱ (b.action_progressive ℱ hB hZ) (b.action_bound _ _) ω 0 t
  have hi' := progressive_bounded_integrable ℱ (b'.action_progressive ℱ hB hZ) (b'.action_bound _ _) ω 0 t
  rw [b'.correction_eq_integral ℱ hB,timePrimitive,timePrimitive,← intervalIntegral.integral_sub hi hi']
  calc
    _ ≤ ∫ s in (0:ℝ)..(t:ℝ), e s := by
      rw [← Real.norm_eq_abs]
      apply intervalIntegral.norm_integral_le_of_norm_le t.coe_nonneg _
        (hei.mono_set (by rw [uIcc_of_le t.coe_nonneg,uIcc_of_le T.coe_nonneg];exact Icc_subset_Icc le_rfl ht))
      filter_upwards [he] with s hs hst
      have hmem : s ∈ Icc (0:ℝ) T := ⟨hst.1.le,hst.2.trans ht⟩
      change |b.f (Real.toNNReal s) _-b'.f (Real.toNNReal s) _| ≤ e s
      rw [Real.coe_toNNReal _ hmem.1]
      exact hs hmem _
    _ ≤ _ := by
      apply intervalIntegral.integral_mono_interval le_rfl t.coe_nonneg ht _ hei
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact hen s ⟨hs.1.le,hs.2⟩

lemma solution_stability_integral (b b' : BoundedLipschitzDrift) (ℱ : Filtration ℝ≥0 mΩ)
    {B : ℝ≥0 → Ω → ℝ} (hB : IsProgressive ℱ B) (T : ℝ≥0) {e : ℝ → ℝ}
    (hei : IntervalIntegrable e volume 0 T)
    (hen : ∀ s ∈ Icc (0:ℝ) T, 0 ≤ e s)
    (he : ∀ᵐ s : ℝ, s ∈ Icc (0:ℝ) T → ∀ x, |b.f s x-b'.f s x| ≤ e s)
    (t : ℝ≥0) (ht : t ≤ T) (ω : Ω) :
    |b.solution B t ω-b'.solution B t ω| ≤
      2*(∫ s in (0:ℝ)..(T:ℝ), e s)*Real.exp (b.rate*t) := by
  exact solution_stability_on b b' ℱ hB T
    (intervalIntegral.integral_nonneg T.coe_nonneg (fun s hs => hen s hs)) ω
    (fun u hu => residual_integral_bound b b' ℱ hB T hei hen he u hu ω) t ht

end ZeroTemperatureSK.BoundedLipschitzDrift

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
namespace ZeroTemperatureSK
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

def positiveDrift (γ : OrderParameter) (n : ℕ) : BoundedLipschitzDrift :=
  finiteFeedback (regularDatum_softAbs (ne_of_gt (positiveTerminal_pos γ n)))
    (softAbs_lipschitz (ne_of_gt (positiveTerminal_pos γ n)))
    (positiveCoeff γ n) (approxMesh n) (n+1) 0

def positivePath (W : BrownianSystem Ω) (γ : OrderParameter) (n : ℕ) : ℝ≥0 → Ω → ℝ :=
  (positiveDrift γ n).solution W.driver

def positiveCoeffError (γ : OrderParameter) (n : ℕ) : ℝ :=
  ∫ s in (0:ℝ)..1, |positiveGamma γ n s-extend γ.val s|

lemma positiveCoeffError_nonneg (γ : OrderParameter) (n : ℕ) : 0 ≤ positiveCoeffError γ n := by
  exact intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => abs_nonneg _)

lemma positiveCoeffError_limit (γ : OrderParameter) : Tendsto (positiveCoeffError γ) atTop (𝓝 0) := positiveGamma_L1 γ

lemma mul_sub_mul_error {a b u v D δ : ℝ} (hδ : 0 ≤ δ) (hD : |a| ≤ D)
    (hv : |v| ≤ 1) (huv : |u-v| ≤ δ) : |a*u-b*v| ≤ |a-b|+D*δ := by
  calc
    _ = |(a-b)*v+a*(u-v)| := by congr 1;ring
    _ ≤ |(a-b)*v|+|a*(u-v)| := abs_add_le _ _
    _ = |a-b| * |v|+|a| * |u-v| := by rw [abs_mul,abs_mul]
    _ ≤ |a-b| * 1+D*δ := add_le_add (mul_le_mul_of_nonneg_left hv (abs_nonneg _))
      ((mul_le_mul_of_nonneg_left huv (abs_nonneg _)).trans (mul_le_mul_of_nonneg_right hD hδ))
    _ = _ := by ring

lemma positiveDrift_error (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time)
    (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hd : ∀ s ∈ Icc (0:ℝ) T, ∀ x, |deriv (positiveValue γ n s) x-gradient W γ s x| ≤ δ) :
    ∀ᵐ s : ℝ, s ∈ Icc (0:ℝ) T → ∀ x,
      |(stripDrift W γ T).f s x-(positiveDrift γ n).f s x| ≤
        |positiveGamma γ n s-extend γ.val s|+γ.val T*δ := by
  filter_upwards [rightCoeff_ae (positiveCoeff γ n) (approxMesh n) (n+1) 0] with s hs hst x
  rw [stripDrift_eq W γ T hst]
  change |extend γ.val s*gradient W γ s x-rightCoeff (positiveCoeff γ n) (approxMesh n) (n+1) 0 s*
    deriv (positiveValue γ n s) x| ≤ _
  rw [hs]
  have ha : |extend γ.val s| ≤ γ.val T := by
    have hmem : s ∈ Ico (0:ℝ) 1 := ⟨hst.1,hst.2.trans_lt T.property.2⟩
    simp only [extend,dite_eq_left hmem,abs_of_nonneg (γ.nonneg _)]
    exact γ.monotone hst.2
  have hu : |deriv (positiveValue γ n s) x| ≤ 1 := by
    exact norm_deriv_le_of_lipschitz (finiteValue_lipschitz
      (softAbs_lipschitz (ne_of_gt (positiveTerminal_pos γ n))) _ _ _ _ _) (x₀ := x)
  simpa only [positiveGamma,abs_sub_comm] using mul_sub_mul_error (b := positiveGamma γ n s) hδ ha hu (by simpa only [abs_sub_comm] using hd s hst x)

lemma positivePath_error (W : BrownianSystem Ω) (γ : OrderParameter) (T : Time)
    (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hd : ∀ s ∈ Icc (0:ℝ) T, ∀ x, |deriv (positiveValue γ n s) x-gradient W γ s x| ≤ δ)
    (t : ℝ≥0) (ht : (t:ℝ) ≤ T) (ξ : Ω) :
    |positivePath W γ n t ξ-diffusion W γ t ξ| ≤
      2*(positiveCoeffError γ n+γ.val T*(T:ℝ)*δ)*Real.exp ((stripDrift W γ T).rate*T) := by
  let e := fun s => |positiveGamma γ n s-extend γ.val s|+γ.val T*δ
  have hei (a b : ℝ) : IntervalIntegrable e volume a b :=
    (((finiteCoeff_intervalIntegrable (positiveCoeff γ n) (approxMesh n) (n+1) 0 a b).sub
      γ.integrable.intervalIntegrable).abs).add intervalIntegrable_const
  have hen (s : ℝ) : 0 ≤ e s := add_nonneg (abs_nonneg _) (mul_nonneg (γ.nonneg T) hδ)
  let TT : ℝ≥0 := ⟨T,T.property.1⟩
  have hh := (stripDrift W γ T).solution_stability_integral (positiveDrift γ n) _ W.driver_progressive TT
    (hei 0 T) (fun s _ => hen s) (positiveDrift_error W γ T n hδ hd) t ht ξ
  rw [← diffusion_eq_strip W γ T t ht] at hh
  rw [abs_sub_comm] at hh
  change |positivePath W γ n t ξ-diffusion W γ t ξ| ≤ _ at hh
  have hi0 : 0 ≤ ∫ s in (0:ℝ)..(T:ℝ), e s :=
    intervalIntegral.integral_nonneg T.property.1 (fun s _ => hen s)
  have hi : (∫ s in (0:ℝ)..(T:ℝ), e s) ≤ positiveCoeffError γ n+γ.val T*(T:ℝ)*δ := by
    have hgi (a b : ℝ) := ((finiteCoeff_intervalIntegrable (positiveCoeff γ n) (approxMesh n) (n+1) 0 a b).sub γ.integrable.intervalIntegrable).abs
    dsimp only [e,positiveGamma]
    rw [intervalIntegral.integral_add (hgi 0 T) intervalIntegrable_const,intervalIntegral.integral_const]
    dsimp only [positiveCoeffError]
    have hi := intervalIntegral.integral_mono_interval (a := (0:ℝ)) (b := (T:ℝ))
      (c := (0:ℝ)) (d := 1) le_rfl T.property.1 T.property.2.le
      (Eventually.of_forall (fun s => abs_nonneg (positiveGamma γ n s-extend γ.val s))) (hgi 0 1)
    dsimp only [e,positiveGamma] at *
    simp only [sub_zero,smul_eq_mul] at *
    nlinarith only [hi]
  have hex : Real.exp ((stripDrift W γ T).rate*t) ≤ Real.exp ((stripDrift W γ T).rate*T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht (stripDrift W γ T).rate_pos.le)
  exact hh.trans (mul_le_mul (mul_le_mul_of_nonneg_left hi (by norm_num)) hex
    (Real.exp_pos _).le (mul_nonneg (by norm_num) (hi0.trans hi)))

end ZeroTemperatureSK

end
end

end OAI
