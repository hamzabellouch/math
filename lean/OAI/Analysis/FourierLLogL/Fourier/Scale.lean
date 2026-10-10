import OAI.Analysis.FourierLLogL.Fourier.Translate
import OAI.Analysis.FourierLLogL.Fourier.Kernel
import OAI.Analysis.FourierLLogL.Fourier.Affine

open MeasureTheory Filter Set Function
open scoped ENNReal BigOperators Topology Real

namespace OAI

namespace FourierLLogL.Period
noncomputable section

def scales : Set ℝ := Ico (1/2) 1

def averageH (F : ℝ → ℂ) (x : ℝ) (J : ℕ) :=
  ∫ s in scales, (1/s^2) • ∫ a in origins, shift F a s J x

def convK (F : ℝ → ℂ) (x : ℝ) (J : ℕ) :=
  ∫ t in window, kernel (side J) t • F (x-t)

lemma seg_integral_slices (a b : ℝ) (h : ℝ → ℝ → ℂ) (A : Set ℝ)
    (hm : Measurable (uncurry h)) (B : ℝ)
    (hb : ∀ s ∈ Ico a b, ∀ y, ‖h s y‖ ≤ B) [IsFiniteMeasure (volume.restrict A)] :
    IntegrableOn (fun s => ∫ y in A, h s y) (Ico a b) := by
  refine seg_integrable _ hm.stronglyMeasurable.integral_prod_right.measurable
    (∫ _ in A, B) _ _ (fun s hs => ?_)
  apply (norm_integral_le_integral_norm _).trans
  have hm' : Measurable (h s) := hm.comp (measurable_const.prodMk measurable_id)
  exact integral_mono (Integrable.of_bound hm'.aestronglyMeasurable B
    (ae_of_all _ (hb _ hs))).norm (integrable_const _) (hb _ hs)

lemma measurable_layer {X : Type*} [MeasurableSpace X] {F : ℝ → ℂ} (hf : Measurable F)
    {A R O : X → ℝ} (hA : Measurable A) (hR : Measurable R) (hO : Measurable O) (n) :
    Measurable fun y => haarLayer F (A y) (R y) n (O y) :=
  Finset.measurable_sum _ fun _ _ =>
    measurable_jump_comp hf (hA.add (measurable_const.mul (hR.mul measurable_const)))
      (hR.mul measurable_const) hO

private lemma inv_sq_bound {s : ℝ} (hs : s ∈ scales) : ‖(1/s^2:ℝ)‖ ≤ 4 := by
  have hh := hs.1
  have h1 : 0 < s := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [div_le_iff₀ (by positivity)]
  nlinarith

private lemma weight_bound {c : ℝ} {v : ℂ} (hc : c ∈ scales) {B : ℝ}
    (h : ‖v‖ ≤ B) : ‖(1/c^2) • v‖ ≤ 4 * B := by
  rw [norm_smul]
  apply mul_le_mul (inv_sq_bound hc) h (norm_nonneg _)
  norm_num

private instance scales_fin : IsFiniteMeasure (volume.restrict scales) :=
  show IsFiniteMeasure (volume.restrict (Ico (1/2:ℝ) 1)) from inferInstance

private instance origins_fin : IsFiniteMeasure (volume.restrict origins) :=
  show IsFiniteMeasure (volume.restrict (Ico (-2:ℝ) 2)) from inferInstance

private instance window_fin : IsFiniteMeasure (volume.restrict window) :=
  show IsFiniteMeasure (volume.restrict (Ico (-1:ℝ) 1)) from inferInstance

private lemma average_succ (F : ℝ → ℂ) (hf : Measurable F) (B : ℝ) (hb : ∀ y, ‖F y‖ ≤ B)
    (x : ℝ) (J : ℕ) :
    averageH F x (J+1) = averageH F x J +
      ∫ s in scales, (1/s^2) • ∫ a in origins, haarLayer F a s J x := by
  let U (s a : ℝ) := shift F a s J x
  let V (s a : ℝ) := haarLayer F a s J x
  have hu : Measurable (uncurry U) :=
    measurable_shift_comp hf measurable_snd measurable_fst measurable_const J
  have hv : Measurable (uncurry V) :=
    measurable_layer hf measurable_snd measurable_fst measurable_const J
  have hUb (s a) := bounded_shift hf B hb a s J x
  let C := ∑ n ∈ Finset.range J, (2:ℝ)^n*B
  have HI (w : ℝ → ℝ → ℂ) (hw : Measurable (uncurry w)) (C : ℝ)
      (hW : ∀ s a, ‖w s a‖ ≤ C) :
      (∀ s, IntegrableOn (w s) origins) ∧
      IntegrableOn (fun s => (1/s^2) • ∫ a in origins, w s a) scales := by
    refine ⟨fun s => Integrable.of_bound (hw.of_uncurry_left.aestronglyMeasurable)
      C (ae_of_all _ (hW s)), ?_⟩
    simp_rw [← integral_smul]
    apply seg_integral_slices _ _ _ _ (_ : Measurable _) (4*C) (fun s hs a => weight_bound hs (hW s a))
    exact (measurable_const.div (measurable_fst.pow_const 2)).smul hw
  obtain ⟨hUI,hUI'⟩ := HI U hu C hUb
  obtain ⟨hVI,hVI'⟩ := HI V hv ((2:ℝ)^J * B) (fun s a => bounded_haarLayer hf B hb a s J x)
  have heq (s : ℝ) :
      (1/s^2) • (∫ a in origins, shift F a s (J+1) x) =
        ((1/s^2) • ∫ a in origins, U s a) + ((1/s^2) • ∫ a in origins, V s a) := by
    simp_rw [show ∀ a, shift F a s (J+1) x = U s a + V s a by
      intro a; exact Finset.sum_range_succ (fun n => haarLayer F a s n x) J]
    rw [integral_add (hUI s) (hVI s), smul_add]
  unfold averageH
  simp_rw [heq, integral_add hUI' hVI']
  rfl

def portion (a b t : ℝ) : ℝ := ∫ r in Ico a b, kappa (t/r) / r^2

private lemma scale_subst (n : ℕ) (t : ℝ) :
    (∫ s in scales, (1/s^2)*((2:ℝ)^n)*kappa (t/(s*side n))) =
      portion (side (n+1)) (side n) t := by
  let f (r : ℝ) := kappa (t/r)/r^2
  have hp := side_pos n
  have hh := seg_translate_scale f 0 (by norm_num : (1/2:ℝ) ≤ 1) hp
  simp only [zero_add, mul_one] at hh
  have H (s : ℝ) : (1/s^2)*((2:ℝ)^n)*kappa (t/(s*side n)) =
      side n • f (side n * s) := by
    rw [show (2:ℝ)^n = (side n)⁻¹ by
      field_simp
      exact pow_mul_side _]
    unfold f
    rw [mul_comm (side n) s, smul_eq_mul, mul_pow]
    simp only [div_eq_mul_inv, mul_inv_rev]
    field_simp

  unfold scales portion
  simp_rw [H]
  rw [integral_smul, hh, smul_smul, mul_inv_cancel₀ hp.ne', one_smul, side_succ]
  simp only [f, div_eq_mul_inv, one_mul]

private lemma kernel_split (J : ℕ) (t : ℝ) :
    kernel (side (J+1)) t = kernel (side J) t + portion (side (J+1)) (side J) t := by
  let f (r : ℝ) := kappa (t/r)/r^2
  have hJ := side_pos J
  have hlt : side (J+1) ≤ side J := by rw [side_succ]; linarith
  have hi {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : IntervalIntegrable f volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    have H (x : ℝ) (hx : x ∈ Icc a b) : x ≠ 0 := (ha.trans_le hx.1).ne'
    exact (kappa_cont.comp_continuousOn (continuousOn_const.div continuousOn_id H)).div
      (continuousOn_id.pow 2) (fun x hx => pow_ne_zero _ (H x hx))
  rw [kernel, kernel, portion, seg_eq_interval f (side_le (J+1)), seg_eq_interval f (side_le J),
    seg_eq_interval f hlt, add_comm (a:=(∫ x in side J..1, f x)), intervalIntegral.integral_add_adjacent_intervals
      (hi (side_pos _) hlt) (hi (side_pos _) (side_le J))]

lemma convolution_average (F : ℝ → ℂ) (hf : Measurable F) (B : ℝ) (hb : ∀ y, ‖F y‖ ≤ B)
    {x : ℝ} (hx : x ∈ unitInt) (J) :
    averageH F x J = convK F x J := by
  induction J with
  | zero =>
    simp [averageH, convK, shift, kernel, side]
  | succ n ih =>
    let q (t : ℝ) := F (x-t)
    have hq : Measurable q := hf.comp (by fun_prop)
    let r := side n
    let V (s t : ℝ) := (1/s^2*(2:ℝ)^n*kappa (t/(s*r))) • q t
    have heq : (∫ s in scales, (1/s^2) • ∫ a in origins, haarLayer F a s n x) =
        ∫ t in window, portion (side (n+1)) r t • q t := by
      have Hs (s : ℝ) (hs : s ∈ scales) :
          ((1/s^2) • ∫ a in origins, haarLayer F a s n x) = ∫ t in window, V s t := by
        have hs' : 0 < s := by linarith [hs.1]
        rw [haarLayer_average F hf B hb n hx hs' hs.2.le, smul_smul, ← integral_smul]
        unfold V q r
        simp_rw [smul_smul]
      have HVm : Measurable (uncurry V) :=
        (((measurable_const.div (measurable_fst.pow_const 2)).mul measurable_const).mul
          (kappa_cont.measurable.comp (measurable_snd.div (measurable_fst.mul measurable_const)))).smul
          (hq.comp measurable_snd)
      have Hi : Integrable (uncurry V) ((volume.restrict scales).prod (volume.restrict window)) := by
        apply Integrable.of_bound HVm.aestronglyMeasurable ((4*(2:ℝ)^n*2)*B)
        rw [Measure.prod_restrict]
        filter_upwards [ae_restrict_mem (measurableSet_Ico.prod measurableSet_Ico)]
          with ⟨s,t⟩ ⟨hs,_⟩
        dsimp only [uncurry_apply_pair, V, q]
        rw [norm_smul, norm_mul, norm_mul, Real.norm_eq_abs (kappa _)]
        have h := inv_sq_bound hs
        gcongr
        all_goals first | simp | exact kappa_bound _ | exact hb _
      calc
        _ = ∫ s in scales, ∫ t in window, V s t := setIntegral_congr_fun measurableSet_Ico Hs
        _ = ∫ t in window, ∫ s in scales, V s t := integral_integral_swap Hi
        _ = _ := by
          dsimp only [V, r]
          simp_rw [integral_smul_const, scale_subst]
    have Hk (n : ℕ) : IntegrableOn (fun t => kernel (side n) t • F (x-t)) window := by
      apply seg_integrable _ ((kernel_measurable _).smul hq)
        ((2/(side n)) * B)
      intro t _
      change ‖kernel (side n) t • F (x-t)‖ ≤ _
      rw [norm_smul]
      exact mul_le_mul (kernel_small (side_pos _) (side_le _) t) (hb _) (norm_nonneg _)
        (div_nonneg (by norm_num) (side_pos _).le)
    let V' (t : ℝ) := portion (side (n+1)) r t • F (x-t)
    have H (t : ℝ) : kernel (side (n+1)) t • F (x-t) =
        kernel (side n) t • F (x-t) + V' t := by rw [kernel_split, add_smul]
    have Hi : IntegrableOn V' window := by
      rw [show V' = (fun t => kernel (side (n+1)) t • F (x-t)) -
        (fun t => kernel (side n) t • F (x-t)) by ext t; simp [H]]
      exact (Hk _).sub (Hk _)
    rw [average_succ F hf B hb, ih, heq, convK, convK]
    simp_rw [H, integral_add (Hk n) Hi]
    rfl


def maxConvK (ρ : ℝ → ℝ) (J : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ u : ℤ, ENNReal.ofReal ‖convK (modρ ρ u) x J‖

lemma measurable_maxConvK {ρ : ℝ → ℝ} (hρ : Measurable ρ) (J : ℕ) :
    Measurable (maxConvK ρ J) := by
  refine Measurable.iSup fun n => Measurable.ennreal_ofReal
    (Measurable.norm (show Measurable (fun x => convK (modρ ρ n) x J) from ?_))
  unfold convK
  apply StronglyMeasurable.measurable
  exact StronglyMeasurable.integral_prod_right (Measurable.stronglyMeasurable
    (((kernel_measurable _).comp measurable_snd).smul
      ((measurable_mod hρ _).comp (measurable_fst.sub measurable_snd))))

lemma convolution_cost {ρ : ℝ → ℝ} (hρ : Measurable ρ) (h0 : ∀ x, 0 ≤ ρ x)
    (B : ℝ) (hb : ∀ y, ρ y ≤ B) (G : Set ℝ) (hG : MeasurableSet G)
    (hGu : G ⊆ unitInt) (Q : ℝ≥0∞) (J : ℕ)
    (H : ∀ s ∈ scales, ∀ a ∈ origins, (∫⁻ x in G, maxShift ρ a s J x) ≤ Q) :
    (∫⁻ x in G, maxConvK ρ J x) ≤ 16 * Q := by
  let Z (x s a : ℝ) := ENNReal.ofReal ‖(1/s^2:ℝ)‖ * maxShift ρ a s J x
  have Hi (x : ℝ) (hx : x ∈ G) :
      maxConvK ρ J x ≤ ∫⁻ s in scales, (∫⁻ a in origins, Z x s a) := by
    refine iSup_le fun n => ?_
    let f := modρ ρ (n:ℝ)
    have hm : Measurable f := measurable_mod hρ _
    have hb' (y : ℝ) : ‖f y‖ ≤ B := by rw [show f y = _ from rfl, norm_mod h0]; exact hb _
    rw [← convolution_average (modρ ρ n) hm B hb' (hGu hx) J]
    unfold averageH
    simp_rw [← integral_smul]
    rw [ofReal_norm]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    refine lintegral_mono fun s => (enorm_integral_le_lintegral_enorm _).trans ?_
    refine lintegral_mono fun a => ?_
    unfold Z maxShift
    rw [← ofReal_norm, norm_smul, ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul_right (le_iSup (fun u : ℤ =>
      ENNReal.ofReal ‖shift (modρ ρ u) a s J x‖) n) _
  have Hm {X : Type} [MeasurableSpace X] (x s a : X → ℝ)
      (hx : Measurable x) (hs : Measurable s) (ha : Measurable a) :
      Measurable fun y => Z (x y) (s y) (a y) :=
    ((measurable_const.div (hs.pow_const 2)).norm.ennreal_ofReal).mul
      (measurable_maxShift_comp hρ ha hs hx _)
  have Hm' : Measurable fun w : ℝ × ℝ => ∫⁻ a in origins, Z w.1 w.2 a := by
    refine Measurable.lintegral_prod_right ?_
    exact Hm _ _ _ (measurable_fst.comp measurable_fst) (measurable_snd.comp measurable_fst)
      measurable_snd
  have HI (s : ℝ) (hs : s ∈ scales) :
      (∫⁻ x in G, (∫⁻ a in origins, Z x s a)) ≤ 16 * Q := by
    have hZ : Measurable (fun p : ℝ × ℝ => Z p.1 s p.2) :=
      Hm _ _ _ measurable_fst measurable_const measurable_snd
    rw [lintegral_lintegral_swap hZ.aemeasurable]
    have hA (a : ℝ) (ha : a ∈ origins) :
        (∫⁻ x in G, Z x s a) ≤ 4 * Q := by
      unfold Z
      rw [lintegral_const_mul _ (show Measurable (maxShift ρ a s J) from
        measurable_maxShift_comp hρ measurable_const measurable_const measurable_id J)]
      exact mul_le_mul' (by simpa using ENNReal.ofReal_le_ofReal (inv_sq_bound hs)) (H s hs a ha)
    refine (lintegral_mono_ae ((ae_restrict_mem measurableSet_Ico).mono hA)).trans ?_
    have HV : volume origins = 4 := by norm_num [origins]
    simp only [setLIntegral_const]
    change 4*Q*volume origins ≤ _
    rw [HV]

    exact le_of_eq (by ring)
  refine (lintegral_mono_ae ((ae_restrict_mem hG).mono Hi)).trans ?_
  rw [lintegral_lintegral_swap Hm'.aemeasurable]
  refine (lintegral_mono_ae ((ae_restrict_mem measurableSet_Ico).mono HI)).trans ?_
  simp only [setLIntegral_const]
  exact mul_le_of_le_one_right zero_le (by norm_num [scales])

end
end FourierLLogL.Period

end OAI
