import OAI.Analysis.LiebThirring.LowestEigenvalue

namespace OAI

universe u189


noncomputable section
namespace SharpLiebThirring.OperatorProof
open MeasureTheory Set Filter
open scoped Topology

lemma integral_norm_Icc_le_sqrt_length {E : Type u189} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : MemLp f 2 volume) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in Icc a b, ‖f x‖) ≤ ‖hf.toLp f‖ * Real.sqrt (b-a) := by
  let q : Lp ℝ 2 (volume : Measure ℝ) :=
    indicatorConstLp (s := Icc a b) 2 measurableSet_Icc (measure_Icc_lt_top.ne) (1 : ℝ)
  have hq : ‖q‖ = Real.sqrt (b-a) := by
    rw [show q = indicatorConstLp (s := Icc a b) 2 measurableSet_Icc (measure_Icc_lt_top.ne) (1 : ℝ) from rfl,
      norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp only [norm_one,one_mul,ENNReal.toReal_ofNat,Real.volume_real_Icc,
      max_eq_left (sub_nonneg.mpr hab),Real.sqrt_eq_rpow]
  have hi : inner ℝ (hf.norm.toLp (fun x ↦ ‖f x‖)) q = ∫ x in Icc a b, ‖f x‖ := by
    rw [L2.inner_def,← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [hf.norm.coeFn_toLp,indicatorConstLp_coeFn (p := 2)
      (s := Icc a b) (hs := measurableSet_Icc) (hμs := measure_Icc_lt_top.ne) (c := (1:ℝ))] with x hx hy
    change q x * (hf.norm.toLp (fun x ↦ ‖f x‖)) x = (Icc a b).indicator (fun x ↦ ‖f x‖) x
    rw [hx,show q x = (Icc a b).indicator (fun _ ↦ (1:ℝ)) x from hy]
    by_cases h : x ∈ Icc a b <;> simp [h]
  rw [← hi]
  calc
    _ ≤ ‖hf.norm.toLp (fun x ↦ ‖f x‖)‖ * ‖q‖ := real_inner_le_norm _ _
    _ = _ := by simp only [hq,Lp.norm_toLp,eLpNorm_norm f hf.aestronglyMeasurable]

lemma primitive_holder {g : ℝ → ℝ} (hg : MemLp g 2 volume) (c x y : ℝ) :
    |(c + ∫ t in (0:ℝ)..x, g t) - (c + ∫ t in (0:ℝ)..y, g t)| ≤
      ‖hg.toLp g‖ * Real.sqrt |x-y| := by
  have hgI := SobolevProof.locallyIntegrable_intervalIntegrable (hg.locallyIntegrable (by norm_num))
  have h (a b : ℝ) (hab : a ≤ b) :
      |(c + ∫ t in (0:ℝ)..b, g t) - (c + ∫ t in (0:ℝ)..a, g t)| ≤
        ‖hg.toLp g‖ * Real.sqrt (b-a) := by
    have hd : (c + ∫ t in (0:ℝ)..b, g t) - (c + ∫ t in (0:ℝ)..a, g t) =
        ∫ t in a..b, g t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hgI 0 a) (hgI a b)]
      ring
    rw [hd]
    calc
      _ ≤ ∫ t in a..b, ‖g t‖ := intervalIntegral.norm_integral_le_integral_norm hab
      _ = ∫ t in Icc a b, ‖g t‖ := by
        rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
      _ ≤ _ := integral_norm_Icc_le_sqrt_length hg hab
  rcases le_total y x with hyx | hxy
  · simpa [abs_of_nonneg (sub_nonneg.mpr hyx)] using h y x hyx
  · rw [abs_sub_comm, abs_sub_comm x y, abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact h x y hxy

lemma h1_exists_continuous_rep (u : H1) : ∃ F : ℝ → ℂ, Continuous F ∧
    u.val =ᵐ[volume] F ∧
    (∀ x, ‖F x‖ ≤ 2*(‖u.val_memLp.toLp u.val‖ + ‖u.grad_memLp.toLp u.grad‖)) ∧
    (∀ x y, ‖F x-F y‖ ≤ 2*‖u.grad_memLp.toLp u.grad‖*Real.sqrt |x-y|) := by
  obtain ⟨cr,hr⟩ := SobolevProof.weak_derivative_representation
    ((Complex.reCLM.comp_memLp' u.val_memLp).locallyIntegrable (by norm_num))
    ((Complex.reCLM.comp_memLp' u.grad_memLp).locallyIntegrable (by norm_num))
    (SobolevProof.h1_project_weak u Complex.reCLM)
  obtain ⟨ci,hi⟩ := SobolevProof.weak_derivative_representation
    ((Complex.imCLM.comp_memLp' u.val_memLp).locallyIntegrable (by norm_num))
    ((Complex.imCLM.comp_memLp' u.grad_memLp).locallyIntegrable (by norm_num))
    (SobolevProof.h1_project_weak u Complex.imCLM)
  let Fr := fun x ↦ cr+∫ t in (0:ℝ)..x, (u.grad t).re
  let Fi := fun x ↦ ci+∫ t in (0:ℝ)..x, (u.grad t).im
  have hcr : Continuous Fr := continuous_const.add (intervalIntegral.continuous_primitive
    (SobolevProof.locallyIntegrable_intervalIntegrable
      ((Complex.reCLM.comp_memLp' u.grad_memLp).locallyIntegrable (by norm_num))) 0)
  have hci : Continuous Fi := continuous_const.add (intervalIntegral.continuous_primitive
    (SobolevProof.locallyIntegrable_intervalIntegrable
      ((Complex.imCLM.comp_memLp' u.grad_memLp).locallyIntegrable (by norm_num))) 0)
  let F := fun x ↦ (Fr x : ℂ) + (Fi x : ℂ)*Complex.I
  have hFc : Continuous F := (Complex.continuous_ofReal.comp hcr).add
    ((Complex.continuous_ofReal.comp hci).mul continuous_const)
  have hrep : u.val =ᵐ[volume] F := by
    filter_upwards [hr,hi] with x hx hy
    apply Complex.ext
    · simpa [F,Fr,Fi] using hx
    · simpa [F,Fr,Fi] using hy
  have hrv := project_L2_norm_le Complex.reCLM (fun z ↦ Complex.abs_re_le_norm z) u.val_memLp
  have hrg := project_L2_norm_le Complex.reCLM (fun z ↦ Complex.abs_re_le_norm z) u.grad_memLp
  have hiv := project_L2_norm_le Complex.imCLM (fun z ↦ Complex.abs_im_le_norm z) u.val_memLp
  have hig := project_L2_norm_le Complex.imCLM (fun z ↦ Complex.abs_im_le_norm z) u.grad_memLp
  refine ⟨F,hFc,hrep,?_,?_⟩
  · intro x
    have hxr := primitive_pointwise_bound (Complex.reCLM.comp_memLp' u.val_memLp)
      (Complex.reCLM.comp_memLp' u.grad_memLp) cr hr x
    have hxi := primitive_pointwise_bound (Complex.imCLM.comp_memLp' u.val_memLp)
      (Complex.imCLM.comp_memLp' u.grad_memLp) ci hi x
    have he : ‖F x‖ ≤ |Fr x|+|Fi x| := by simpa [F] using Complex.norm_le_abs_re_add_abs_im (F x)
    change |Fr x| ≤ _ at hxr
    change |Fi x| ≤ _ at hxi
    dsimp only [Function.comp_def] at hxr hxi
    linarith
  · intro x y
    have hrh := primitive_holder (Complex.reCLM.comp_memLp' u.grad_memLp) cr x y
    have hih := primitive_holder (Complex.imCLM.comp_memLp' u.grad_memLp) ci x y
    have he : ‖F x-F y‖ ≤ |Fr x-Fr y|+|Fi x-Fi y| := by
      simpa [F] using Complex.norm_le_abs_re_add_abs_im (F x-F y)
    have hs := Real.sqrt_nonneg |x-y|
    change |Fr x-Fr y| ≤ _ at hrh
    change |Fi x-Fi y| ≤ _ at hih
    dsimp only [Function.comp_def] at hrh hih
    nlinarith [mul_le_mul_of_nonneg_right hrg hs, mul_le_mul_of_nonneg_right hig hs]

end SharpLiebThirring.OperatorProof

end

end OAI
