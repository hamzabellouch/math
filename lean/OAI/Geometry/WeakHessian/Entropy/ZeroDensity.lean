import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.CompContDiff2
import OAI.Geometry.WeakHessian.Entropy.TruncatedLog
import OAI.Geometry.WeakHessian.Transport.IntegrableEvalBounded
import OAI.Geometry.WeakHessian.Transport.VariationQuotient
import OAI.Geometry.WeakHessian.Entropy.MulLogFenchel
import OAI.Geometry.WeakHessian.Entropy.ScalarEntropyLog

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile3
noncomputable section
namespace WeakHessian
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def squareDensityMeasure (n : Measure X) (w : X → ℝ) : Measure X :=
  n.withDensity (fun x => ENNReal.ofReal (w x ^ 2))

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_integral {n : Measure X} {w : X → ℝ} (hw : Measurable w) (f : X → ℝ) :
    (∫ x, f x ∂squareDensityMeasure n w) = ∫ x, w x^2*f x ∂n := by
  rw [squareDensityMeasure,integral_withDensity_eq_integral_toReal_smul₀
    (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul]

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_integrable {n : Measure X} {w f : X → ℝ} (hw : Measurable w) :
    Integrable f (squareDensityMeasure n w) ↔ Integrable (fun x => w x^2*f x) n := by
  rw [squareDensityMeasure,integrable_withDensity_iff_integrable_smul₀'
    (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul]

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_inv_integrable {n : Measure X} [IsFiniteMeasure n] {w : X → ℝ}
    (hw : Measurable w) : Integrable (fun x => (w x^2)⁻¹) (squareDensityMeasure n w) := by
  rw [squareDensity_integrable hw]
  apply Integrable.of_bound (by fun_prop) 1
  exact ae_of_all _ fun x => by
    by_cases h : w x^2 = 0
    · simp [h]
    · simp [mul_inv_cancel₀ h]

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_inv_mass {n : Measure X} [IsFiniteMeasure n] {w : X → ℝ}
    (hw : Measurable w) :
    (∫ x, (w x^2)⁻¹ ∂squareDensityMeasure n w) ≤ n.real univ := by
  rw [squareDensity_integral hw]
  have H := integral_mono ((squareDensity_integrable hw).mp (squareDensity_inv_integrable hw))
    (integrable_const (1:ℝ) (μ := n)) (fun x => show w x^2*(w x^2)⁻¹ ≤ 1 by
      by_cases h : w x^2 = 0
      · simp [h]
      · simp [mul_inv_cancel₀ h])
  simpa using H

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_pos_ae {n : Measure X} {w : X → ℝ}
    (hw : Measurable w) (hn : ∀ x, 0 ≤ w x) :
    ∀ᵐ x ∂squareDensityMeasure n w, 0 < w x := by
  apply (ae_withDensity_iff (by fun_prop)).mpr
  exact ae_of_all _ fun x hx => by
    have hs : w x^2 ≠ 0 := fun h => hx (by simp [h])
    exact lt_of_le_of_ne (hn x) (fun h => hs (by simp [← h]))

def squareLogFloor (a : ℝ) (w : X → ℝ) (x : X) : ℝ :=
  2*(regularizedLog a (w x)+Real.log a)

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma squareLogFloor_eq {a : ℝ} (ha : 0 < a) {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (x : X) :
    squareLogFloor a w x = 2*Real.log (w x+a) := by
  simp only [squareLogFloor,regularizedLog_eq ha (hw x),sub_add_cancel]

omit [MeasurableSpace X] [BorelSpace X] in
lemma squareLogFloor_lipschitz {a : ℝ} (ha : 0 < a) {w : X → ℝ} {L : ℝ≥0}
    (hw : LipschitzWith L w) :
    LipschitzWith (‖(2:ℝ)‖₊*(Real.toNNReal a⁻¹*L)) (squareLogFloor a w) := by
  have H : LipschitzWith (Real.toNNReal a⁻¹*L) (fun x => regularizedLog a (w x)+Real.log a) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have H := ((regularizedLog_lipschitz ha).comp hw).dist_le_mul x y
    change dist (regularizedLog a (w x)) (regularizedLog a (w y)) ≤ a⁻¹*(L:ℝ)*dist x y at H
    simpa only [dist_add_right,NNReal.coe_mul,Real.coe_toNNReal _ (inv_nonneg.mpr ha.le)] using H
  exact lipschitz_const_mul_real H 2

noncomputable def squareLogFloorBCF {a : ℝ} (ha : 0 < a) (w : X →ᵇ ℝ) : X →ᵇ ℝ :=
  (2:ℝ) • (BoundedContinuousFunction.comp (regularizedLog a) (regularizedLog_lipschitz ha) w +
    BoundedContinuousFunction.const X (Real.log a))

omit [MeasurableSpace X] [BorelSpace X] in
@[simp] lemma squareLogFloorBCF_apply {a : ℝ} (ha : 0 < a) (w : X →ᵇ ℝ) (x : X) :
    squareLogFloorBCF ha w x = squareLogFloor a w x := by rfl

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma exp_squareLogFloor {a : ℝ} (ha : 0 < a) {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (x : X) :
    Real.exp (squareLogFloor a w x) = (w x+a)^2 := by
  rw [squareLogFloor_eq ha hw,two_mul,Real.exp_add,Real.exp_log (add_pos_of_nonneg_of_pos (hw x) ha),pow_two]

lemma squareDensity_entropy_upper {n : Measure X} [IsFiniteMeasure n] (w : X →ᵇ ℝ)
    [IsFiniteMeasure (squareDensityMeasure n w)] (hw : ∀ x, 0 ≤ w x) {a : ℝ} (ha : 0 < a) :
    entropyReal n (squareDensityMeasure n w) ≤
      ∫ x, squareLogFloor a w x ∂squareDensityMeasure n w := by
  have habs : squareDensityMeasure n w ≪ n := withDensity_absolutelyContinuous _ _
  rw [entropyReal_eq_integral_density habs,squareDensity_integral w.continuous.measurable]
  have hrn := Measure.rnDeriv_withDensity n (show Measurable (fun x => ENNReal.ofReal (w x^2)) by fun_prop)
  have heq : (fun x => ((squareDensityMeasure n w).rnDeriv n x).toReal *
      Real.log ((squareDensityMeasure n w).rnDeriv n x).toReal) =ᵐ[n]
      fun x => w x^2*Real.log (w x^2) := by
    filter_upwards [hrn] with x hx
    simp only [squareDensityMeasure,hx,ENNReal.toReal_ofReal (sq_nonneg _)]
  rw [integral_congr_ae heq]
  have hi : Integrable (fun x => w x^2*Real.log (w x^2)) n := by
    have H : Continuous (fun x : X => w x^2*Real.log (w x^2)) :=
      Real.continuous_mul_log.comp (w.continuous.pow 2)
    obtain ⟨C,hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := ‖w‖^2)).exists_bound_of_continuousOn
      (f := fun r : ℝ => r*Real.log r) Real.continuous_mul_log.continuousOn
    apply Integrable.of_bound H.aestronglyMeasurable C
    refine ae_of_all _ fun x => hC _ ⟨sq_nonneg _,?_⟩
    have H := w.norm_coe_le_norm x
    simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg _) H 2
  have hi2 := (squareDensity_integrable (n := n) w.continuous.measurable).mp ((squareLogFloorBCF ha w).integrable _)
  apply integral_mono hi hi2
  intro x
  by_cases hx : w x = 0
  · simp [hx]
  have hx0 : 0 < w x := lt_of_le_of_ne (hw x) (Ne.symm hx)
  change w x^2*Real.log (w x^2) ≤ w x^2*squareLogFloor a w x
  rw [squareLogFloor_eq ha hw,Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (Real.log_le_log hx0 (by linarith)) (by norm_num)) (sq_nonneg _)

omit [MetricSpace X] [BorelSpace X] in
lemma squareDensity_mass {n : Measure X} {w : X → ℝ} (hw : Measurable w)
    [IsProbabilityMeasure (squareDensityMeasure n w)] : (∫ x, w x^2 ∂n) = 1 := by
  have H := squareDensity_integral (n := n) hw (fun _ => (1:ℝ))
  simpa using H.symm

lemma squareDensity_fenchel_defect {n μ : Measure X} [IsFiniteMeasure n]
    [IsProbabilityMeasure μ] (w : X →ᵇ ℝ) [IsProbabilityMeasure (squareDensityMeasure n w)]
    (hw : ∀ x, 0 ≤ w x) (hμ : FiniteEntropy n μ) {a : ℝ} (ha : 0 < a) :
    entropyReal n (squareDensityMeasure n w)-entropyReal n μ ≤
      (∫ x, squareLogFloor a w x ∂squareDensityMeasure n w)-
      (∫ x, squareLogFloor a w x ∂μ)+2*a*(∫ x,w x ∂n)+a^2*n.real univ := by
  have hu := squareDensity_entropy_upper (n := n) w hw ha
  have hl := entropyReal_fenchel hμ (squareLogFloorBCF ha w)
  have he : (∫ x, Real.exp (squareLogFloorBCF ha w x) ∂n) =
      1+2*a*(∫ x, w x ∂n)+a^2*n.real univ := by
    simp only [squareLogFloorBCF_apply,exp_squareLogFloor ha hw]
    have hf : (fun x => (w x+a)^2) = fun x => w x^2+(2*a)*w x+a^2 := by funext x; ring
    have hi : Integrable (fun x => w x^2) n := (w^2).integrable n
    rw [hf,integral_add (f := fun x => w x^2+(2*a)*w x) (g := fun _ => a^2)
      (hi.add ((w.integrable n).const_mul (2*a))) (integrable_const _),
      integral_add (f := fun x => w x^2) (g := fun x => (2*a)*w x) hi ((w.integrable n).const_mul (2*a)),integral_const_mul,
      squareDensity_mass w.continuous.measurable,integral_const,smul_eq_mul]
    ring
  simp only [squareLogFloorBCF_apply,Measure.real,measure_univ,ENNReal.toReal_one] at hl
  rw [show (∫ x,Real.exp (squareLogFloor a w x) ∂n) = _ from he] at hl
  linarith

lemma squareLogFloor_increment_comparison {Z : Type*} [MeasurableSpace Z]
    {π : Measure Z} [IsFiniteMeasure π] {n : Measure X} [IsFiniteMeasure n]
    {s r : Z → X} (hs : AEMeasurable s π) (hr : AEMeasurable r π)
    (w : X →ᵇ ℝ) (hw : ∀ x, 0 ≤ w x) (h0 : π.map s = squareDensityMeasure n w)
    {a b d : ℝ} (hb : 0 < b) (hba : b ≤ a) (hd : 0 ≤ d)
    (hmove : ∀ᵐ z ∂π, w (s z)-d ≤ w (r z)) :
    (∫ z, squareLogFloor b w (s z)-squareLogFloor b w (r z) ∂π) ≤
      (∫ z, squareLogFloor a w (s z)-squareLogFloor a w (r z) ∂π)+
      (4*a*d+8*d^2*Real.log ((2*d+b)/b))*n.real univ := by
  have ha := hb.trans_le hba
  have hip : Integrable (fun z => (w (s z)^2)⁻¹) π := by
    apply (integrable_map_measure (g := fun x => (w x^2)⁻¹) (by fun_prop) hs).mp
    rw [h0]
    exact squareDensity_inv_integrable w.continuous.measurable
  have hmass : (∫ z, (w (s z)^2)⁻¹ ∂π) ≤ n.real univ := by
    rw [← integral_map (f := fun x => (w x^2)⁻¹) hs (by fun_prop),h0]
    exact squareDensity_inv_mass w.continuous.measurable
  have hp : ∀ᵐ z ∂π, 0 < w (s z) := by
    apply ae_of_ae_map hs (p := fun x => 0 < w x)
    rw [h0]
    exact squareDensity_pos_ae w.continuous.measurable hw
  let C := 4*a*d+8*d^2*Real.log ((2*d+b)/b)
  have hC : 0 ≤ C := by
    have hR : 1 ≤ (2*d+b)/b := by rw [le_div_iff₀ hb]; linarith
    have hlog := Real.log_nonneg hR
    dsimp [C]
    positivity
  have his (c : ℝ) (hc : 0 < c) : Integrable (fun z => squareLogFloor c w (s z)) π := by
    exact (integrable_map_measure (squareLogFloorBCF hc w).continuous.aestronglyMeasurable hs).mp
      ((squareLogFloorBCF hc w).integrable _)
  have hir (c : ℝ) (hc : 0 < c) : Integrable (fun z => squareLogFloor c w (r z)) π := by
    exact (integrable_map_measure (squareLogFloorBCF hc w).continuous.aestronglyMeasurable hr).mp
      ((squareLogFloorBCF hc w).integrable _)
  have H := integral_mono_ae ((his b hb).sub (hir b hb))
    (((his a ha).sub (hir a ha)).add (hip.const_mul C)) (show ∀ᵐ z ∂π,
      squareLogFloor b w (s z)-squareLogFloor b w (r z) ≤
      (squareLogFloor a w (s z)-squareLogFloor a w (r z))+C*(w (s z)^2)⁻¹ from by
    filter_upwards [hp,hmove] with z hz hzm
    have H := WeakHessianEntropyScalar.log_floor_comparison hb hba hd (hw (s z)) (hw (r z)) hzm
    simp only [squareLogFloor_eq hb hw,squareLogFloor_eq ha hw]
    have hz2 : 0 < w (s z)^2 := sq_pos_of_pos hz
    have hh : (2*Real.log (w (s z)+b)-2*Real.log (w (r z)+b))-
        (2*Real.log (w (s z)+a)-2*Real.log (w (r z)+a)) ≤ C/(w (s z)^2) := by
      rw [le_div_iff₀ hz2]
      dsimp [C]
      nlinarith
    simpa only [div_eq_mul_inv,add_comm] using (sub_le_iff_le_add.mp hh))
  simp only [Pi.add_apply,Pi.sub_apply] at H
  rw [integral_add (f := fun z => squareLogFloor a w (s z)-squareLogFloor a w (r z))
    (g := fun z => C*(w (s z)^2)⁻¹) ((his a ha).sub (hir a ha)) (hip.const_mul C),integral_const_mul] at H
  exact H.trans (by dsimp only [C] at *; linarith [mul_le_mul_of_nonneg_left hmass hC])

lemma entropy_chord_squareRoot_approx {π : Measure (Curve X)} [IsProbabilityMeasure π]
    {n : Measure X} [IsFiniteMeasure n] (w : X →ᵇ ℝ) (hw : ∀ x, 0 ≤ w x)
    (h0 : interpolation π timeZero = squareDensityMeasure n w)
    {K A c : ℝ} (hc : 0 ≤ c)
    (hmove : ∀ t : Time, ∀ᵐ γ ∂π, w (γ timeZero)-c*(t:ℝ) ≤ w (γ t))
    (hcurv : ∀ t : Time, FiniteEntropy n (interpolation π t) ∧
      entropyReal n (interpolation π t) ≤
        (1-(t:ℝ))*entropyReal n (interpolation π timeZero)+
          (t:ℝ)*entropyReal n (interpolation π timeOne)-K/2*(t:ℝ)*(1-(t:ℝ))*A)
    {a D : ℝ} (ha : 0 < a)
    (hd : Tendsto (fun t : ℝ => (∫ γ, squareLogFloor a w (γ timeZero)-
      squareLogFloor a w (evalReal γ t) ∂π)/t) (𝓝[>] 0) (𝓝 D)) :
    entropyReal n (interpolation π timeZero)-entropyReal n (interpolation π timeOne)+K/2*A ≤
      D+4*a*c*n.real univ := by
  let E := entropyReal n (interpolation π timeZero)-entropyReal n (interpolation π timeOne)
  let M := n.real univ
  let W := ∫ x,w x ∂n
  let I (a t : ℝ) := (∫ γ, squareLogFloor a w (γ timeZero)-squareLogFloor a w (evalReal γ t) ∂π)
  let : IsProbabilityMeasure (squareDensityMeasure n w) := by
    rw [← h0]
    exact interpolation_probability π timeZero
  have ht0 : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hsq : ∀ᶠ t : ℝ in 𝓝[>] 0, t^2 < a := by
    exact (ht0.pow 2).eventually (gt_mem_nhds (by simpa using ha))
  have hl : Tendsto (fun t : ℝ => E+K/2*(1-t)*A) (𝓝[>] 0) (𝓝 (E+K/2*A)) := by
    simpa using (tendsto_const_nhds (x := E)).add ((((tendsto_const_nhds (x := (1:ℝ))).sub ht0).const_mul (K/2)).mul_const A)
  have hr : Tendsto (fun t : ℝ => I a t/t+4*a*c*M+
      8*c^2*M*(t*Real.log (1+2*c/t))+2*t*W+t^3*M)
      (𝓝[>] 0) (𝓝 (D+4*a*c*M)) := by
    have hlog := WeakHessianEntropyScalar.tendsto_time_log_reciprocal (show 0 ≤ 2*c by positivity)
    have HH := (((hd.add_const (4*a*c*M)).add (hlog.const_mul (8*c^2*M))).add
      ((ht0.const_mul 2).mul_const W)).add ((ht0.pow 3).mul_const M)
    simpa only [I,mul_zero,zero_mul,zero_pow (by norm_num : (3:ℕ) ≠ 0),add_zero] using HH
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [hsq,show ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioo (0:ℝ) 1 from Ioo_mem_nhdsGT zero_lt_one] with t hta ht
  let τ : Time := ⟨t,ht.1.le,ht.2.le⟩
  have hcl : clampTime t = τ := Subtype.ext (clampTime_of_mem τ.property)
  have hmap (b : ℝ) (hb : 0 < b) (s : Time) :
      (∫ x, squareLogFloor b w x ∂interpolation π s) = ∫ γ,squareLogFloor b w (γ s) ∂π :=
    integral_map (continuous_eval_const s).measurable.aemeasurable (squareLogFloorBCF hb w).continuous.aestronglyMeasurable
  have hit (b : ℝ) (hb : 0 < b) (s : Time) : Integrable (fun γ => squareLogFloor b w (γ s)) π := by
    exact (integrable_map_measure (squareLogFloorBCF hb w).continuous.aestronglyMeasurable
      (continuous_eval_const s).measurable.aemeasurable).mp ((squareLogFloorBCF hb w).integrable _)
  have ht2 : 0 < t^2 := sq_pos_of_pos ht.1
  let : IsProbabilityMeasure (interpolation π τ) := interpolation_probability π τ
  have hfen := squareDensity_fenchel_defect w hw (hcurv τ).1 ht2
  rw [← h0,hmap _ ht2 timeZero,hmap _ ht2 τ,← integral_sub (hit _ ht2 timeZero) (hit _ ht2 τ)] at hfen
  have hcomp := squareLogFloor_increment_comparison
    (continuous_eval_const timeZero).measurable.aemeasurable
    (continuous_eval_const τ).measurable.aemeasurable w hw h0 ht2 hta.le (mul_nonneg hc ht.1.le) (hmove τ)
  have he : ((2*(c*t)+t^2)/t^2) = 1+2*c/t := by field_simp [ht.1.ne']; ring
  have hnum : t*(E+K/2*(1-t)*A) ≤ I a t+
      (4*a*(c*t)+8*(c*t)^2*Real.log (1+2*c/t))*M+2*t^2*W+(t^2)^2*M := by
    have H := (hcurv τ).2
    change entropyReal n (interpolation π τ) ≤ (1-t)*entropyReal n (interpolation π timeZero)+
      t*entropyReal n (interpolation π timeOne)-K/2*t*(1-t)*A at H
    have heI : (∫ γ, squareLogFloor a w (γ timeZero)-squareLogFloor a w (γ τ) ∂π) = I a t := by
      simp only [I,evalReal,hcl]
    rw [heI,he] at hcomp
    dsimp only [E,M,W]
    nlinarith
  have hdiv : E+K/2*(1-t)*A ≤
      (I a t+(4*a*(c*t)+8*(c*t)^2*Real.log (1+2*c/t))*M+2*t^2*W+(t^2)^2*M)/t := by
    rw [le_div_iff₀ ht.1]
    nlinarith [hnum]
  have halg : (I a t+(4*a*(c*t)+8*(c*t)^2*Real.log (1+2*c/t))*M+2*t^2*W+(t^2)^2*M)/t =
      I a t/t+4*a*c*M+8*c^2*M*(t*Real.log (1+2*c/t))+2*t*W+t^3*M := by
    field_simp [ht.1.ne']
    ring
  rw [halg] at hdiv
  exact hdiv

variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma gamma_squareLogFloor (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {φ w : X → ℝ} {L T : ℝ≥0} (hφ : LipschitzWith L φ) (hw : LipschitzWith T w)
    (hn : ∀ x, 0 ≤ w x) {a : ℝ} (ha : 0 < a) :
    gamma m φ (squareLogFloor a w) =ᵐ[m] fun x => 2/(w x+a)*gamma m φ w x := by
  have hφS := localSobolev_of_lipschitz hfin hφ
  have hwS := localSobolev_of_lipschitz hfin hw
  have hrL := (regularizedLog_lipschitz ha).comp hw
  have hrS := localSobolev_of_lipschitz hfin hrL
  have hchain := gamma_comp_contDiff hfin hpar hwS hφS (regularizedLog_contDiff ha)
    hrS.1 (ae_of_all _ fun x => regularizedLog_deriv_bound ha (w x))
  filter_upwards [gamma_comm (m := m) φ (squareLogFloor a w),
    gamma_const_mul_left hfin hpar (hrS.add_const hfin (Real.log a)) hφS 2,
    gamma_add_const_left hfin hrS hφS (Real.log a),hchain,gamma_comm (m := m) w φ] with x hc hm ha' hh hs
  change gamma m (squareLogFloor a w) φ x = 2*gamma m (fun y => regularizedLog a (w y)+Real.log a) φ x at hm
  change gamma m (fun y => regularizedLog a (w y)+Real.log a) φ x = gamma m (regularizedLog a ∘ w) φ x at ha'
  rw [hc,hm,ha',hh,hs,regularizedLog_deriv ha,max_eq_right (by linarith [hn x])]
  simp only [div_eq_mul_inv]
  ring

lemma integrable_local_gamma_finite_ac (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {n : Measure X} [IsFiniteMeasure n] (hn : n ≪ m)
    {φ w : X → ℝ} {L T : ℝ≥0} (hφ : LipschitzWith L φ) (hw : LipschitzWith T w) :
    Integrable (gamma m φ w) n := by
  have hφS := localSobolev_of_lipschitz hfin hφ
  have hwS := localSobolev_of_lipschitz hfin hw
  apply Integrable.of_bound ((gamma_aestronglyMeasurable hfin hφS hwS).mono_ac hn) ((L:ℝ)*T)
  apply hn.ae_le
  filter_upwards [abs_gamma_le hfin hpar hφS hwS,weakGradient_le_lipschitz hfin hφ,
    weakGradient_le_lipschitz hfin hw,weakGradient_nonneg (m := m) w] with x h hx hy hn
  rw [Real.norm_eq_abs]
  exact h.trans (mul_le_mul hx hy hn L.coe_nonneg)

lemma squareLogFloor_contact_upper (hfin : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {n : Measure X} [IsFiniteMeasure n] (hn : n ≪ m)
    {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    (w : X →ᵇ ℝ) {φ : X → ℝ} {L T : ℝ≥0} (hφ : LipschitzWith L φ) (hw : LipschitzWith T (w: X → ℝ))
    (hwn : ∀ x, 0 ≤ w x) (h0 : interpolation π timeZero = squareDensityMeasure n w)
    {a : ℝ} (ha : 0 < a) :
    (∫ γ, gamma m φ (squareLogFloor a w) (γ timeZero) ∂π) ≤
      (∫ x, 2*w x*gamma m φ w x ∂n)+2*a*(∫ x,|gamma m φ w x| ∂n) := by
  let : IsProbabilityMeasure π := hπ.1
  have hφS := localSobolev_of_lipschitz hfin hφ
  have hwS := localSobolev_of_lipschitz hfin hw
  have hfl := squareLogFloor_lipschitz ha hw
  have hfS := localSobolev_of_lipschitz hfin hfl
  have hgm := gamma_aestronglyMeasurable hfin hφS hfS
  have hG := integrable_local_gamma_finite_ac hfin hpar hn hφ hw
  have hGm := (gamma_aestronglyMeasurable hfin hφS hwS).mono_ac hn
  have hΓ : Integrable (fun x => 2*w x*gamma m φ w x) n := by
    apply (hG.norm.const_mul (2*‖w‖)).mono' ((w.continuous.aestronglyMeasurable.const_mul 2).mul hGm)
    filter_upwards [] with x
    simp only [Pi.mul_apply,norm_mul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have H := w.norm_coe_le_norm x
    norm_num only [Real.norm_eq_abs] at H
    nlinarith [mul_le_mul_of_nonneg_right H (abs_nonneg (gamma m φ w x))]
  have hinit : interpolation π timeZero ≪ m := (hπ.2.1.choose_spec timeZero).absolutelyContinuous.trans
    (Measure.AbsolutelyContinuous.rfl.smul_left _)
  have him : Integrable (gamma m φ (squareLogFloor a w)) (squareDensityMeasure n w) := by
    rw [← h0]
    exact (integrable_map_measure (hgm.mono_ac hinit) (continuous_eval_const timeZero).measurable.aemeasurable).mpr
      (hπ.integrable_gamma_eval hfin hpar hφ hfl timeZero)
  rw [← integral_map (continuous_eval_const timeZero).measurable.aemeasurable (hgm.mono_ac hinit)]
  change (∫ x, gamma m φ (squareLogFloor a w) x ∂interpolation π timeZero) ≤ _
  rw [h0,squareDensity_integral hw.continuous.measurable]
  have hchain := hn.ae_eq (gamma_squareLogFloor hfin hpar hφ hw hwn ha)
  have hI := (squareDensity_integrable hw.continuous.measurable).mp him
  have H := integral_mono_ae hI (hΓ.add (hG.abs.const_mul (2*a))) (show ∀ᵐ x ∂n,
    w x^2*gamma m φ (squareLogFloor a w) x ≤ 2*w x*gamma m φ w x+2*a*|gamma m φ w x| from by
    filter_upwards [hchain] with x hx
    rw [hx]
    have hp : 0 < w x+a := add_pos_of_nonneg_of_pos (hwn x) ha
    have hwdiv : 0 ≤ w x/(w x+a) := div_nonneg (hwn x) hp.le
    have hwle : w x/(w x+a) ≤ 1 := by rw [div_le_one hp]; linarith
    have H := neg_abs_le (gamma m φ w x)
    have HH : -(2*a)*(w x/(w x+a))*gamma m φ w x ≤ 2*a*|gamma m φ w x| := by
      calc
        _ ≤ (2*a)*(w x/(w x+a))*|gamma m φ w x| := by nlinarith [mul_nonneg (by positivity : 0 ≤ (2*a)*(w x/(w x+a))) (by linarith : 0 ≤ gamma m φ w x+|gamma m φ w x|)]
        _ ≤ 2*a*|gamma m φ w x| := by nlinarith [mul_le_mul_of_nonneg_right hwle (by positivity : 0 ≤ 2*a*|gamma m φ w x|)]
    have he : w x^2*(2/(w x+a)*gamma m φ w x)-2*w x*gamma m φ w x =
        -(2*a)*(w x/(w x+a))*gamma m φ w x := by field_simp [hp.ne']; ring
    rw [← he] at HH
    linarith)
  simp only [Pi.add_apply] at H
  rw [integral_add (f := fun x => 2*w x*gamma m φ w x) (g := fun x => 2*a*|gamma m φ w x|)
    hΓ (hG.abs.const_mul (2*a)),integral_const_mul] at H
  exact H

lemma IsTestPlan.entropy_squareRoot_subdifferential (hfin : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {π : Measure (Curve X)} (hπ : IsTestPlan m π)
    (hb : BoundedTracks π) (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    {n : Measure X} [IsFiniteMeasure n] (hn : n ≪ m)
    (w : X →ᵇ ℝ) {φ ψ : X → ℝ} {L T : ℝ≥0} (hφ : LipschitzWith L φ)
    (hw : LipschitzWith T (w: X → ℝ)) (hwn : ∀ x, 0 ≤ w x)
    (hdual : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    (hcontact : ∀ᵐ γ ∂π, φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2)
    (h0 : interpolation π timeZero = squareDensityMeasure n w) {K : ℝ}
    (hcurv : ∀ t : Time, FiniteEntropy n (interpolation π t) ∧
      entropyReal n (interpolation π t) ≤
        (1-(t:ℝ))*entropyReal n (interpolation π timeZero)+
          (t:ℝ)*entropyReal n (interpolation π timeOne)-
          K/2*(t:ℝ)*(1-(t:ℝ))*(∫ γ,dist (γ timeZero) (γ timeOne)^2 ∂π)) :
    entropyReal n (interpolation π timeZero)-entropyReal n (interpolation π timeOne)+
      K/2*(∫ γ,dist (γ timeZero) (γ timeOne)^2 ∂π) ≤
      ∫ x,2*w x*gamma m φ w x ∂n := by
  let : IsProbabilityMeasure π := hπ.1
  obtain ⟨o,R,hR,htracks⟩ := hb
  let c : ℝ := (T:ℝ)*(2*R)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hmove (t : Time) : ∀ᵐ γ ∂π, w (γ timeZero)-c*(t:ℝ) ≤ w (γ t) := by
    filter_upwards [hgeo,htracks] with γ hγ ht
    have hl : dist (γ timeZero) (γ timeOne) ≤ 2*R := by
      have H := dist_triangle (γ timeZero) o (γ timeOne)
      rw [dist_comm o] at H
      linarith [ht timeZero,ht timeOne]
    have Hd : dist (γ timeZero) (γ t) = (t:ℝ)*dist (γ timeZero) (γ timeOne) := by
      rw [hγ timeZero t]
      simp only [timeZero,zero_sub,abs_neg,abs_of_nonneg t.2.1]
    have H := hw.le_add_mul (γ timeZero) (γ t)
    rw [Hd] at H
    have J := mul_le_mul_of_nonneg_left hl (mul_nonneg T.coe_nonneg t.2.1)
    dsimp only [c]
    nlinarith
  let G := ∫ x,2*w x*gamma m φ w x ∂n
  let C := (2*(∫ x,|gamma m φ w x| ∂n)+4*c*n.real univ)
  have hall (a : ℝ) (ha : 0 < a) :
      entropyReal n (interpolation π timeZero)-entropyReal n (interpolation π timeOne)+
        K/2*(∫ γ,dist (γ timeZero) (γ timeOne)^2 ∂π) ≤ G+a*C := by
    have hd := hπ.contact_first_variation hfin hpar ⟨o,R,hR,htracks⟩ hgeo hφ
      (squareLogFloor_lipschitz ha hw) hdual hcontact
    have H := entropy_chord_squareRoot_approx w hwn h0 hc hmove hcurv ha hd
    have J := squareLogFloor_contact_upper hfin hpar hn hπ w hφ hw hwn h0 ha
    dsimp only [G,C]
    nlinarith
  have hlim : Tendsto (fun a : ℝ => G+a*C) (𝓝[>] 0) (𝓝 G) := by
    simpa using (tendsto_const_nhds (x := G)).add
      ((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0)).mul_const C)
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
  exact hall a ha

end WeakHessian

end
end InlinedFile3

end OAI
