import OAI.Analysis.LiebThirring.OperatorGraph

namespace OAI

universe u181


noncomputable section
namespace SharpLiebThirring.OperatorProof
open MeasureTheory Set Filter
open scoped Topology

lemma integral_norm_Icc_le_L2 {E : Type u181} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : MemLp f 2 volume) {a b : ℝ} (hab : a ≤ b) (hlen : b-a ≤ 1) :
    (∫ x in Icc a b, ‖f x‖) ≤ ‖hf.toLp f‖ := by
  let q : Lp ℝ 2 (volume : Measure ℝ) :=
    indicatorConstLp (s := Icc a b) 2 measurableSet_Icc (measure_Icc_lt_top.ne) (1 : ℝ)
  have hq : ‖q‖ ≤ 1 := by
    rw [show q = indicatorConstLp (s := Icc a b) 2 measurableSet_Icc (measure_Icc_lt_top.ne) (1 : ℝ) from rfl,
      norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp only [norm_one,one_mul,ENNReal.toReal_ofNat,Real.volume_real_Icc,max_eq_left (sub_nonneg.mpr hab)]
    calc
      (b-a)^(1/(2:ℝ)) ≤ 1^(1/(2:ℝ)) := Real.rpow_le_rpow (sub_nonneg.mpr hab) hlen (by norm_num)
      _ = 1 := by simp
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
    _ ≤ ‖hf.norm.toLp (fun x ↦ ‖f x‖)‖*‖q‖ := real_inner_le_norm _ _
    _ ≤ ‖hf.norm.toLp (fun x ↦ ‖f x‖)‖*1 := mul_le_mul_of_nonneg_left hq (norm_nonneg _)
    _ = ‖hf.toLp f‖ := by
      simp only [mul_one,Lp.norm_toLp,eLpNorm_norm f hf.aestronglyMeasurable]

lemma primitive_pointwise_bound {f g : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (c : ℝ)
    (hrep : f =ᵐ[volume] (fun x ↦ c+∫ t in (0:ℝ)..x, g t)) (x : ℝ) :
    |c+∫ t in (0:ℝ)..x, g t| ≤ ‖hf.toLp f‖+‖hg.toLp g‖ := by
  let F : ℝ → ℝ := fun x ↦ c+∫ t in (0:ℝ)..x, g t
  have hgI := SobolevProof.locallyIntegrable_intervalIntegrable (hg.locallyIntegrable (by norm_num))
  have hFc : Continuous F := continuous_const.add (intervalIntegral.continuous_primitive hgI 0)
  have hFL : MemLp F 2 volume := hf.ae_eq hrep
  have hnorm : ‖hFL.toLp F‖ = ‖hf.toLp f‖ := by
    congr 1
    exact (MemLp.toLp_eq_toLp_iff hFL hf).mpr hrep.symm
  have hvol : volume (Icc x (x+1)) = 1 := by simp [Real.volume_Icc]
  obtain ⟨y,hy,hmean⟩ := exists_le_setAverage (μ := volume) (s := Icc x (x+1)) (by simp [hvol])
    (by simp [hvol]) (hFc.norm.integrableOn_Icc)
  have hFy : |F y| ≤ ‖hf.toLp f‖ := by
    have hInt := integral_norm_Icc_le_L2 hFL (a := x) (b := x+1) (by linarith) (by linarith)
    rw [setAverage_eq,Measure.real,hvol] at hmean
    simp only [ENNReal.toReal_one,inv_one,one_smul] at hmean
    exact hmean.trans (hnorm ▸ hInt)
  have hdiff : F y-F x = ∫ t in x..y, g t := by
    dsimp [F]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hgI 0 x) (hgI x y)]
    ring
  have hdif : |F y-F x| ≤ ‖hg.toLp g‖ := by
    rw [hdiff]
    calc
      _ ≤ ∫ t in x..y, ‖g t‖ := intervalIntegral.norm_integral_le_integral_norm hy.1
      _ = ∫ t in Icc x y, ‖g t‖ := by
        rw [intervalIntegral.integral_of_le hy.1,integral_Icc_eq_integral_Ioc]
      _ ≤ ‖hg.toLp g‖ := integral_norm_Icc_le_L2 hg hy.1 (by linarith [hy.2])
  have hFx : |F x| ≤ |F y|+|F y-F x| := by
    calc
      _ = |F y + (F x-F y)| := by congr 1; ring
      _ ≤ |F y|+|F x-F y| := abs_add_le _ _
      _ = _ := by rw [abs_sub_comm (F x) (F y)]
  exact hFx.trans (add_le_add hFy hdif)


lemma project_L2_norm_le (L : ℂ →L[ℝ] ℝ) (hL : ∀ z, ‖L z‖ ≤ ‖z‖)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    ‖(L.comp_memLp' hf).toLp (fun x ↦ L (f x))‖ ≤ ‖hf.toLp f‖ := by
  simp only [Lp.norm_toLp]
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top
    (eLpNorm_mono_ae (L.comp_memLp' hf).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x ↦ hL (f x))))

lemma h1_ae_bound (u : H1) : ∀ᵐ x : ℝ,
    ‖u.val x‖ ≤ 2*(‖u.val_memLp.toLp u.val‖+‖u.grad_memLp.toLp u.grad‖) := by
  obtain ⟨cr,hr⟩ := SobolevProof.weak_derivative_representation
    ((Complex.reCLM.comp_memLp' u.val_memLp).locallyIntegrable (by norm_num))
    ((Complex.reCLM.comp_memLp' u.grad_memLp).locallyIntegrable (by norm_num))
    (SobolevProof.h1_project_weak u Complex.reCLM)
  obtain ⟨ci,hi⟩ := SobolevProof.weak_derivative_representation
    ((Complex.imCLM.comp_memLp' u.val_memLp).locallyIntegrable (by norm_num))
    ((Complex.imCLM.comp_memLp' u.grad_memLp).locallyIntegrable (by norm_num))
    (SobolevProof.h1_project_weak u Complex.imCLM)
  have hrv := project_L2_norm_le Complex.reCLM (fun z ↦ Complex.abs_re_le_norm z) u.val_memLp
  have hrg := project_L2_norm_le Complex.reCLM (fun z ↦ Complex.abs_re_le_norm z) u.grad_memLp
  have hiv := project_L2_norm_le Complex.imCLM (fun z ↦ Complex.abs_im_le_norm z) u.val_memLp
  have hig := project_L2_norm_le Complex.imCLM (fun z ↦ Complex.abs_im_le_norm z) u.grad_memLp
  filter_upwards [hr,hi] with x hx hy
  have hxr := primitive_pointwise_bound (Complex.reCLM.comp_memLp' u.val_memLp)
    (Complex.reCLM.comp_memLp' u.grad_memLp) cr hr x
  have hxi := primitive_pointwise_bound (Complex.imCLM.comp_memLp' u.val_memLp)
    (Complex.imCLM.comp_memLp' u.grad_memLp) ci hi x
  change (u.val x).re = _ at hx
  change (u.val x).im = _ at hy
  rw [← hx] at hxr
  rw [← hy] at hxi
  calc
    ‖u.val x‖ ≤ |(u.val x).re|+|(u.val x).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ _ := add_le_add hxr hxi
    _ ≤ (‖u.val_memLp.toLp u.val‖+‖u.grad_memLp.toLp u.grad‖)+
        (‖u.val_memLp.toLp u.val‖+‖u.grad_memLp.toLp u.grad‖) :=
      add_le_add (add_le_add hrv hrg) (add_le_add hiv hig)
    _ = _ := by ring

lemma h1_ae_sq_bound (u : H1) : ∀ᵐ x : ℝ,
    ‖u.val x‖^2 ≤ 8*(‖u.val_memLp.toLp u.val‖^2+‖u.grad_memLp.toLp u.grad‖^2) := by
  filter_upwards [h1_ae_bound u] with x hx
  have hpos : 0 ≤ 2*(‖u.val_memLp.toLp u.val‖+‖u.grad_memLp.toLp u.grad‖) := by positivity
  have hsq := sq_le_sq₀ (norm_nonneg (u.val x)) hpos |>.mpr hx
  nlinarith [sq_nonneg (‖u.val_memLp.toLp u.val‖-‖u.grad_memLp.toLp u.grad‖)]

lemma L2_norm_sq_eq_integral (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖f‖^2 = ∫ x, ‖f x‖^2 := by
  rw [@norm_sq_eq_re_inner ℂ,L2.inner_def]
  change Complex.reCLM (∫ x, inner ℂ (f x) (f x)) = _
  rw [← Complex.reCLM.integral_comp_comm (L2.integrable_inner f f)]
  congr 1
  ext x
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (f x)).symm

end SharpLiebThirring.OperatorProof

end

end OAI
