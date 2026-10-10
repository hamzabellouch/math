import OAI.Analysis.HenonEmden.Tails

namespace OAI

universe uE

section UniformBounds

open MeasureTheory Set Filter
open scoped ENNReal
namespace HenonLaneEmden.UniformTail

variable {E : Type uE} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma shifted_rpow_le {a : ℝ} (ha : 0 ≤ a) {x y : E} {R : ℝ}
    (hx : ‖x‖ ≤ R) (hy : 2*R ≤ ‖y‖) (hy0 : 0 < ‖y‖) :
    ‖x-y‖^(-a) ≤ 2^a*‖y‖^(-a) := by
  have hlo : ‖y‖/2 ≤ ‖x-y‖ := by
    have ht := norm_sub_norm_le y x
    rw [norm_sub_rev y x] at ht
    linarith
  have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < ‖y‖/2) hlo (neg_nonpos.mpr ha)
  calc
    _ ≤ (‖y‖/2)^(-a) := hh
    _ = 2^a*‖y‖^(-a) := by
      rw [Real.div_rpow (norm_nonneg _) (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      rw [div_inv_eq_mul,mul_comm]

lemma uniform_shifted_tail (μ : Measure E) {C a s : ℝ} (hC : 0 ≤ C)
    (ha : 0 ≤ a) (hs : s < a)
    (hball : ∀ r > 0, μ (Metric.ball (0:E) r) ≤ ENNReal.ofReal (C*r^s)) :
    ∀ x : E, ‖x‖ ≤ 4 →
      (∫⁻ y in (Metric.ball (0:E) 8)ᶜ, ENNReal.ofReal (‖x-y‖^(-a)) ∂μ) ≤
        ENNReal.ofReal (2^a*(C*2^s*8^(s-a)/(1-2^(s-a)))) := by
  let T := C*2^s*8^(s-a)/(1-2^(s-a))
  intro x hx
  calc
    _ ≤ ∫⁻ y in (Metric.ball (0:E) 8)ᶜ, ENNReal.ofReal (2^a) * ENNReal.ofReal (‖y‖^(-a)) ∂μ := by
      apply setLIntegral_mono' measurableSet_ball.compl
      intro y hy
      have hy' : 8 ≤ ‖y‖ := by simpa only [mem_compl_iff,Metric.mem_ball,dist_zero_right,not_lt] using hy
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (shifted_rpow_le ha hx (by linarith) (by linarith))
    _ = ENNReal.ofReal (2^a) * ∫⁻ y in (Metric.ball (0:E) 8)ᶜ, ENNReal.ofReal (‖y‖^(-a)) ∂μ := by
      rw [lintegral_const_mul'' _ (by fun_prop)]
    _ ≤ ENNReal.ofReal (2^a) * ENNReal.ofReal T := by
      gcongr
      exact lintegral_norm_rpow_compl_ball_le μ hC (by norm_num) ha hs hball
    _ = ENNReal.ofReal (2^a*T) := (ENNReal.ofReal_mul (by positivity)).symm


noncomputable def tailNumber (C a s : ℝ) : ℝ :=
  2^a*(C*2^s*8^(s-a)/(1-2^(s-a)))

lemma tailNumber_nonneg {C a s : ℝ} (hC : 0 ≤ C) (hs : s < a) :
    0 ≤ tailNumber C a s := by
  unfold tailNumber
  apply mul_nonneg (by positivity)
  apply div_nonneg (by positivity)
  exact sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (sub_nonpos.mpr hs.le))

lemma truncated_potential_bound (μ : Measure E) {C a s : ℝ} (hC : 0 ≤ C)
    (ha : 0 ≤ a) (hs : s < a)
    (hball : ∀ r > 0, μ (Metric.ball (0:E) r) ≤ ENNReal.ofReal (C*r^s))
    {x : E} (hx : ‖x‖ ≤ 4) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    (∫⁻ y in {y | l ≤ ‖x-y‖}, ENNReal.ofReal (‖x-y‖^(-a)) ∂μ) ≤
      ENNReal.ofReal ((C*8^s+tailNumber C a s)*l^(-a)) := by
  let S : Set E := {y | l ≤ ‖x-y‖}
  have hS : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
  have hpoint (y : E) :
      S.indicator (fun y => ENNReal.ofReal (‖x-y‖^(-a))) y ≤
        (Metric.ball (0:E) 8).indicator (fun _ => ENNReal.ofReal (l^(-a))) y +
        (Metric.ball (0:E) 8)ᶜ.indicator (fun y => ENNReal.ofReal (‖x-y‖^(-a))) y := by
    by_cases hy : y ∈ S
    · rw [indicator_of_mem hy]
      by_cases hy8 : y ∈ Metric.ball (0:E) 8
      · rw [indicator_of_mem hy8,indicator_of_notMem (not_not.mpr hy8),add_zero]
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hl hy (neg_nonpos.mpr ha))
      · rw [indicator_of_notMem hy8,indicator_of_mem hy8,zero_add]
    · rw [indicator_of_notMem hy]; exact zero_le
  have ht := uniform_shifted_tail μ hC ha hs hball x hx
  have hpow : 1 ≤ l^(-a) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hl hl1 (neg_nonpos.mpr ha)
  calc
    _ = ∫⁻ y, S.indicator (fun y => ENNReal.ofReal (‖x-y‖^(-a))) y ∂μ :=
      (lintegral_indicator hS _).symm
    _ ≤ ∫⁻ y, (Metric.ball (0:E) 8).indicator (fun _ => ENNReal.ofReal (l^(-a))) y +
        (Metric.ball (0:E) 8)ᶜ.indicator (fun y => ENNReal.ofReal (‖x-y‖^(-a))) y ∂μ := lintegral_mono hpoint
    _ = ENNReal.ofReal (l^(-a))*μ (Metric.ball (0:E) 8) +
        ∫⁻ y in (Metric.ball (0:E) 8)ᶜ, ENNReal.ofReal (‖x-y‖^(-a)) ∂μ := by
      rw [lintegral_add_left (measurable_const.indicator measurableSet_ball),
        lintegral_indicator measurableSet_ball,lintegral_indicator measurableSet_ball.compl,setLIntegral_const]
    _ ≤ ENNReal.ofReal (l^(-a))*ENNReal.ofReal (C*8^s)+ENNReal.ofReal (tailNumber C a s) := by
      apply add_le_add _ ht
      gcongr
      exact hball 8 (by norm_num)
    _ = ENNReal.ofReal (l^(-a)*(C*8^s)+tailNumber C a s) := by
      rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_add (by positivity) (tailNumber_nonneg hC hs)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [mul_le_mul_of_nonneg_left hpow (tailNumber_nonneg hC hs)])

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma local_kernel_mass_le (a : ℝ) {y : E} (hy : ‖y‖ < 8) :
    (∫⁻ x in Metric.ball (0:E) 4, ENNReal.ofReal (‖x-y‖^(-a))) ≤
      ∫⁻ z in Metric.ball (0:E) 12, ENNReal.ofReal (‖z‖^(-a)) := by
  rw [← lintegral_indicator measurableSet_ball,← lintegral_indicator measurableSet_ball]
  rw [← lintegral_sub_right_eq_self (fun z => (Metric.ball (0:E) 12).indicator
    (fun z => ENNReal.ofReal (‖z‖^(-a))) z) y]
  apply lintegral_mono
  intro x
  dsimp only
  by_cases hx : x ∈ Metric.ball (0:E) 4
  · have hx' : ‖x‖ < 4 := by simpa [Metric.mem_ball,dist_zero_right] using hx
    have hm : x-y ∈ Metric.ball (0:E) 12 := by
      simp only [Metric.mem_ball,dist_zero_right]
      exact lt_of_le_of_lt (norm_sub_le x y) (by linarith)
    rw [indicator_of_mem hx,indicator_of_mem hm]
  · rw [indicator_of_notMem hx]; exact zero_le

lemma local_potential_bound (μ : Measure E) [SFinite μ] {C a s : ℝ} (hC : 0 ≤ C)
    (ha : 0 ≤ a) (hs : s < a)
    (hball : ∀ r > 0, μ (Metric.ball (0:E) r) ≤ ENNReal.ofReal (C*r^s)) :
    (∫⁻ x in Metric.ball (0:E) 4, ∫⁻ y, ENNReal.ofReal (‖x-y‖^(-a)) ∂μ) ≤
      (∫⁻ z in Metric.ball (0:E) 12, ENNReal.ofReal (‖z‖^(-a))) * ENNReal.ofReal (C*8^s) +
      ENNReal.ofReal (tailNumber C a s) * volume (Metric.ball (0:E) 4) := by
  have hpoint (x : E) (hx : x ∈ Metric.ball (0:E) 4) :
      (∫⁻ y, ENNReal.ofReal (‖x-y‖^(-a)) ∂μ) ≤
      (∫⁻ y in Metric.ball (0:E) 8, ENNReal.ofReal (‖x-y‖^(-a)) ∂μ) +
        ENNReal.ofReal (tailNumber C a s) := by
    rw [← lintegral_add_compl (fun y => ENNReal.ofReal (‖x-y‖^(-a))) measurableSet_ball]
    gcongr
    exact uniform_shifted_tail μ hC ha hs hball x (le_of_lt (by simpa [Metric.mem_ball,dist_zero_right] using hx))
  calc
    _ ≤ ∫⁻ x in Metric.ball (0:E) 4,
        (∫⁻ y in Metric.ball (0:E) 8, ENNReal.ofReal (‖x-y‖^(-a)) ∂μ) +
          ENNReal.ofReal (tailNumber C a s) := setLIntegral_mono' measurableSet_ball hpoint
    _ = (∫⁻ x in Metric.ball (0:E) 4, ∫⁻ y in Metric.ball (0:E) 8, ENNReal.ofReal (‖x-y‖^(-a)) ∂μ) +
          ENNReal.ofReal (tailNumber C a s) * volume (Metric.ball (0:E) 4) := by
      rw [lintegral_add_right _ measurable_const,setLIntegral_const]
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      rw [lintegral_lintegral_swap (by fun_prop)]
      calc
        _ ≤ ∫⁻ y in Metric.ball (0:E) 8, (∫⁻ z in Metric.ball (0:E) 12, ENNReal.ofReal (‖z‖^(-a))) ∂μ := by
          apply setLIntegral_mono' measurableSet_ball
          intro y hy
          exact local_kernel_mass_le a (by simpa [Metric.mem_ball,dist_zero_right] using hy)
        _ = (∫⁻ z in Metric.ball (0:E) 12, ENNReal.ofReal (‖z‖^(-a))) * μ (Metric.ball (0:E) 8) :=
          setLIntegral_const _ _
        _ ≤ _ := by gcongr; exact hball 8 (by norm_num)

end HenonLaneEmden.UniformTail

namespace HenonLaneEmden
open UniformTail

noncomputable def sourceMeasure {n : ℕ} (u : Space n → ℝ) (q B : ℝ) : Measure (Space n) :=
  volume.withDensity (fun x => ENNReal.ofReal (source u q B x))

lemma IsSolution.sourceMeasure_ball {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (R : ℝ) :
    sourceMeasure v p A (Metric.ball (0:Space n) R) = ENNReal.ofReal (sourceMass v p A R) := by
  rw [sourceMeasure,withDensity_apply _ measurableSet_ball]
  exact (ofReal_integral_eq_lintegral_ofReal
    (((h.source_g_locallyIntegrable hn).integrableOn_isCompact (isCompact_closedBall _ R)).mono_set
      Metric.ball_subset_closedBall)
    (Eventually.of_forall (source_nonneg (fun y => (h.positive_v y).le) p A))).symm

lemma IsSolution.uniform_source_tail_g {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    ∀ x : Space n, ‖x‖ ≤ 4 →
      (∫⁻ y in (Metric.ball (0:Space n) 8)ᶜ, ENNReal.ofReal (‖x-y‖^(2-(n:ℝ)))
        ∂sourceMeasure v p A) ≤ ENNReal.ofReal
          (2^((n:ℝ)-2) * (sourceConstant n p q A B * 2^((n:ℝ)-2-alpha p q A B) *
            8^(-alpha p q A B) / (1-2^(-alpha p q A B)))) := by
  have hn3 := h.dimension_ge_three hn
  have hn3' : (3:ℝ) ≤ n := by exact_mod_cast hn3
  have hA := h.first_weight_gt_neg_two hn
  have hB := h.swap.first_weight_gt_neg_two hn
  have ha := alpha_pos hp hA hB (h.product_gt_one hn hp hq)
  simpa only [neg_sub,show (n:ℝ)-2-alpha p q A B-((n:ℝ)-2) = -alpha p q A B by ring] using uniform_shifted_tail (sourceMeasure v p A)
    (sourceConstant_pos hn3 hA hB).le (show 0 ≤ (n:ℝ)-2 by linarith)
    (show (n:ℝ)-2-alpha p q A B < (n:ℝ)-2 by linarith)
    (fun R hR => by rw [h.sourceMeasure_ball hn]; exact ENNReal.ofReal_le_ofReal (h.sourceMass_g_upper hn hp hq hR))


instance sourceMeasure_sigmaFinite {n : ℕ} (u : Space n → ℝ) (q B : ℝ) :
    SigmaFinite (sourceMeasure u q B) := by unfold sourceMeasure; infer_instance

lemma lintegral_sourceMeasure {n : ℕ} {u : Space n → ℝ} (hu : Continuous u) (q B : ℝ)
    {F : Space n → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂sourceMeasure u q B) = ∫⁻ y, ENNReal.ofReal (source u q B y)*F y :=
  lintegral_withDensity_eq_lintegral_mul volume (measurable_source hu q B).ennreal_ofReal hF

lemma IsSolution.sourceMeasure_potential_u_ae {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hq : 0 < q) :
    ∀ᵐ x, (∫⁻ y, ENNReal.ofReal (‖x-y‖^(2-(n:ℝ))) ∂sourceMeasure v p A) =
      ENNReal.ofReal (newtonDenom n*u x) := by
  filter_upwards [h.potential_u_ae hn hq] with x hx
  rw [lintegral_sourceMeasure h.continuous_v p A (by fun_prop),hx]
  have hi := ofReal_integral_eq_lintegral_ofReal (h.kernel_g_integrable hn x)
    (Eventually.of_forall fun y => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (source_nonneg (fun y => (h.positive_v y).le) p A y))
  calc
    _ = ∫⁻ y, ENNReal.ofReal (‖x-y‖^(2-(n:ℝ))*source v p A y) := by
      apply lintegral_congr
      intro y
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _),mul_comm]
    _ = _ := by simpa only [WeakPDE.rawPotential,finrank_euclideanSpace_fin] using hi.symm

noncomputable def kernelMass (n : ℕ) : ℝ :=
  ∫ x in Metric.ball (0:Space n) 12, ‖x‖^(2-(n:ℝ))

lemma kernelMass_nonneg (n : ℕ) : 0 ≤ kernelMass n :=
  integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg x) _)

lemma lintegral_kernelMass (n : ℕ) (hn : 1 ≤ n) :
    (∫⁻ x in Metric.ball (0:Space n) 12, ENNReal.ofReal (‖x‖^(2-(n:ℝ)))) = ENNReal.ofReal (kernelMass n) := by
  have hi := (WeakPDE.locallyIntegrable_newtonKernel (E := Space n) (by simpa using hn)).integrableOn_isCompact
    (isCompact_closedBall (0:Space n) 12)
  have hib : IntegrableOn (fun x : Space n => ‖x‖^(2-(n:ℝ))) (Metric.ball 0 12) := by
    simpa only [finrank_euclideanSpace_fin] using hi.mono_set Metric.ball_subset_closedBall
  exact (ofReal_integral_eq_lintegral_ofReal hib
    (Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg x) _)).symm

noncomputable def uniformTailConstant (n : ℕ) (p q A B : ℝ) : ℝ :=
  tailNumber (sourceConstant n p q A B) ((n:ℝ)-2) ((n:ℝ)-2-alpha p q A B)

noncomputable def uniformMassConstant (n : ℕ) (p q A B : ℝ) : ℝ :=
  (kernelMass n*(sourceConstant n p q A B*8^((n:ℝ)-2-alpha p q A B)) +
    uniformTailConstant n p q A B * (volume (Metric.ball (0:Space n) 4)).toReal) / newtonDenom n

lemma IsSolution.uniform_u_mass {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q) :
    (∫ x in Metric.ball (0:Space n) 4, u x) ≤ uniformMassConstant n p q A B := by
  have hn3 := h.dimension_ge_three hn
  have hn3' : (3:ℝ) ≤ n := by exact_mod_cast hn3
  have hA := h.first_weight_gt_neg_two hn
  have hB := h.swap.first_weight_gt_neg_two hn
  have ha := alpha_pos hp hA hB (h.product_gt_one hn hp hq)
  have hC : 0 ≤ sourceConstant n p q A B := (sourceConstant_pos hn3 hA hB).le
  have hT : 0 ≤ uniformTailConstant n p q A B := tailNumber_nonneg hC (by linarith)
  have hh := local_potential_bound (sourceMeasure v p A) hC
    (show 0 ≤ (n:ℝ)-2 by linarith)
    (show (n:ℝ)-2-alpha p q A B < (n:ℝ)-2 by linarith)
    (fun R hR => by rw [h.sourceMeasure_ball hn]; exact ENNReal.ofReal_le_ofReal (h.sourceMass_g_upper hn hp hq hR))
  simp only [neg_sub] at hh
  rw [lintegral_congr_ae (ae_restrict_of_ae (h.sourceMeasure_potential_u_ae hn hq)),
    lintegral_kernelMass n (by omega)] at hh
  have huf : IntegrableOn (fun x => newtonDenom n*u x) (Metric.ball (0:Space n) 4) :=
    ((continuous_const.mul h.continuous_u).continuousOn.integrableOn_compact (isCompact_closedBall _ 4)).mono_set
      Metric.ball_subset_closedBall
  rw [← ofReal_integral_eq_lintegral_ofReal huf (Eventually.of_forall fun x =>
    mul_nonneg (newtonDenom_pos hn3).le (h.positive_u x).le),integral_const_mul] at hh
  have hv : volume (Metric.ball (0:Space n) 4) =
      ENNReal.ofReal ((volume (Metric.ball (0:Space n) 4)).toReal) :=
    (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  change ENNReal.ofReal (newtonDenom n * _) ≤ _ + ENNReal.ofReal (uniformTailConstant n p q A B) * _ at hh
  rw [hv,← ENNReal.ofReal_mul (kernelMass_nonneg n),
    ← ENNReal.ofReal_mul hT,
    ← ENNReal.ofReal_add (mul_nonneg (kernelMass_nonneg n) (mul_nonneg hC (by positivity)))
      (mul_nonneg hT ENNReal.toReal_nonneg)] at hh
  apply (le_div_iff₀ (newtonDenom_pos hn3)).mpr
  rw [mul_comm]
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg
    (mul_nonneg (kernelMass_nonneg n) (mul_nonneg hC (by positivity)))
    (mul_nonneg hT ENNReal.toReal_nonneg))).mp hh

lemma IsSolution.uniform_g_truncated {n : ℕ} (hn : 2 ≤ n) {p q A B : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    {x : Space n} (hx : ‖x‖ ≤ 4) {l : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) :
    (∫⁻ y in {y | l ≤ ‖x-y‖}, ENNReal.ofReal (‖x-y‖^(2-(n:ℝ))) ∂sourceMeasure v p A) ≤
      ENNReal.ofReal ((sourceConstant n p q A B*8^((n:ℝ)-2-alpha p q A B)+uniformTailConstant n p q A B)*l^(2-(n:ℝ))) := by
  have hn3 := h.dimension_ge_three hn
  have hn3' : (3:ℝ) ≤ n := by exact_mod_cast hn3
  have hA := h.first_weight_gt_neg_two hn
  have hB := h.swap.first_weight_gt_neg_two hn
  have ha := alpha_pos hp hA hB (h.product_gt_one hn hp hq)
  simpa only [neg_sub,uniformTailConstant] using
    truncated_potential_bound (sourceMeasure v p A) (sourceConstant_pos hn3 hA hB).le
      (show 0 ≤ (n:ℝ)-2 by linarith)
      (show (n:ℝ)-2-alpha p q A B < (n:ℝ)-2 by linarith)
      (fun R hR => by rw [h.sourceMeasure_ball hn]; exact ENNReal.ofReal_le_ofReal (h.sourceMass_g_upper hn hp hq hR)) hx hl hl1

end HenonLaneEmden
end UniformBounds

end OAI
