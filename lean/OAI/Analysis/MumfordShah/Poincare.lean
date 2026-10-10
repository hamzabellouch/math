import Mathlib
import OAI.Analysis.MumfordShah.Model

namespace OAI

/-! MumfordShah poincare. -/

noncomputable section
open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap
namespace MumfordShah
open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff

open Set MeasureTheory Metric Topology Filter InnerProductSpace
open scoped ENNReal NNReal ContDiff Convolution symmDiff
open Laplacian ContinuousLinearMap

open Set MeasureTheory Metric Topology
open scoped ENNReal NNReal ContDiff symmDiff

lemma sq_integral_le_mass_mul_integral_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ μ.real univ * (∫ x, (f x) ^ 2 ∂μ) := by
  let F : Lp ℝ 2 μ := hf.toLp f
  let U : Lp ℝ 2 μ := (memLp_const (1 : ℝ)).toLp (fun _ : α => (1 : ℝ))
  have h := real_inner_mul_inner_self_le U F
  have hUF : inner ℝ U F = ∫ x, f x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, (memLp_const (1 : ℝ) (μ := μ) (p := 2)).coeFn_toLp]
      with x hx hux
    change F x = f x at hx
    change U x = 1 at hux
    rw [hx, hux]
    simp
  have hUU : inner ℝ U U = μ.real univ := by
    rw [L2.inner_def]
    calc
      (∫ x, inner ℝ (U x) (U x) ∂μ) = ∫ _ : α, (1 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [(memLp_const (1 : ℝ) (μ := μ) (p := 2)).coeFn_toLp] with x hx
        change U x = 1 at hx
        rw [hx]
        simp
      _ = μ.real univ := by simp
  have hFF : inner ℝ F F = ∫ x, (f x) ^ 2 ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    change F x = f x at hx
    rw [hx]
    simp [pow_two]
  rw [hUF, hUU, hFF] at h
  simpa only [pow_two] using h

lemma sq_sub_le_length_mul_integral_deriv_sq
    {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) {a b x y : ℝ}
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    (u x - u y) ^ 2 ≤ (b - a) * (∫ t in Icc a b, (deriv u t) ^ 2) := by
  have hdu : Continuous (deriv u) := hu.continuous_deriv (by norm_num)
  have hdiff : Differentiable ℝ u := hu.differentiable (by norm_num)
  wlog hxy : y ≤ x generalizing x y
  · have hyx := this hy hx (le_of_not_ge hxy)
    nlinarith
  have hFTC : ∫ t in y..x, deriv u t = u x - u y :=
    intervalIntegral.integral_deriv_eq_sub (fun t _ => hdiff t)
      (hdu.intervalIntegrable _ _)
  have hLp : MemLp (deriv u) 2 (volume.restrict (Icc y x)) :=
    (memLp_two_iff_integrable_sq hdu.aestronglyMeasurable).mpr
      ((hdu.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
  have hCS := sq_integral_le_mass_mul_integral_sq hLp
  have hCS' : (∫ t in Icc y x, deriv u t) ^ 2 ≤
      (x - y) * (∫ t in Icc y x, (deriv u t) ^ 2) := by
    simpa only [Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hxy)]
      using hCS
  have hFTC' : ∫ t in Icc y x, deriv u t = u x - u y := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hxy]
    exact hFTC
  rw [hFTC'] at hCS'
  have hmono : (∫ t in Icc y x, (deriv u t) ^ 2) ≤
      ∫ t in Icc a b, (deriv u t) ^ 2 := by
    apply setIntegral_mono_set
      ((hdu.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
      (Filter.Eventually.of_forall fun t => sq_nonneg _)
    exact Filter.Eventually.of_forall (fun t ht => ⟨hy.1.trans ht.1, ht.2.trans hx.2⟩)
  have hnonneg : 0 ≤ ∫ t in Icc y x, (deriv u t) ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  calc
    (u x - u y) ^ 2 ≤ (x - y) * (∫ t in Icc y x, (deriv u t) ^ 2) := hCS'
    _ ≤ (b - a) * (∫ t in Icc a b, (deriv u t) ^ 2) :=
      mul_le_mul (by linarith [hx.2, hy.1]) hmono hnonneg (by linarith [hx.2, hx.1])

lemma sq_sub_mean_le_mean_sq_sub
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : MemLp f 2 μ) (hm : 0 < μ.real univ) (c : ℝ) :
    (c - (∫ x, f x ∂μ) / μ.real univ) ^ 2 ≤
      (∫ x, (c - f x) ^ 2 ∂μ) / μ.real univ := by
  have h := sq_integral_le_mass_mul_integral_sq ((memLp_const c).sub hf)
  have hfi : Integrable f μ := hf.integrable (by norm_num)
  have hint : (∫ x, c - f x ∂μ) = μ.real univ * c - ∫ x, f x ∂μ := by
    rw [integral_sub (integrable_const c) hfi, integral_const, smul_eq_mul]
  change (∫ x, c - f x ∂μ) ^ 2 ≤ μ.real univ * ∫ x, (c - f x) ^ 2 ∂μ at h
  rw [hint] at h
  apply (le_div_iff₀ hm).2
  have heq : μ.real univ * ((∫ x, f x ∂μ) / μ.real univ) = ∫ x, f x ∂μ :=
    mul_div_cancel₀ _ hm.ne'
  have hdiv : (μ.real univ * (c - (∫ x, f x ∂μ) / μ.real univ)) ^ 2 ≤
      μ.real univ * (∫ x, (c - f x) ^ 2 ∂μ) := by
    rwa [mul_sub, heq]
  apply (mul_le_mul_iff_right₀ hm).mp
  nlinarith only [hdiv]

lemma square_path_estimate
    {u : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 1 u) {R : ℝ} (hR : 0 ≤ R)
    {x y : ℝ × ℝ} (hx : x ∈ Icc (-R) R ×ˢ Icc (-R) R)
    (hy : y ∈ Icc (-R) R ×ˢ Icc (-R) R) :
    (u x - u y) ^ 2 ≤ 4 * R *
      ((∫ s in Icc (-R) R, ‖fderiv ℝ u (s, x.2)‖ ^ 2) +
       (∫ t in Icc (-R) R, ‖fderiv ℝ u (y.1, t)‖ ^ 2)) := by
  have hrow : ContDiff ℝ 1 (fun s : ℝ => u (s, x.2)) :=
    hu.comp (contDiff_id.prodMk contDiff_const)
  have hcol : ContDiff ℝ 1 (fun t : ℝ => u (y.1, t)) :=
    hu.comp (contDiff_const.prodMk contDiff_id)
  have hrow' := sq_sub_le_length_mul_integral_deriv_sq hrow hx.1 hy.1
  have hcol' := sq_sub_le_length_mul_integral_deriv_sq hcol hx.2 hy.2
  have hdu : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have hrowbound : (∫ s in Icc (-R) R, (deriv (fun s => u (s, x.2)) s) ^ 2) ≤
      ∫ s in Icc (-R) R, ‖fderiv ℝ u (s, x.2)‖ ^ 2 := by
    apply setIntegral_mono_on
      ((hrow.continuous_deriv (by norm_num)).pow 2).continuousOn.integrableOn_Icc
      ((hdu.comp (continuous_id.prodMk continuous_const)).norm.pow 2).continuousOn.integrableOn_Icc
      measurableSet_Icc
    intro s hs
    have hd : deriv (fun s : ℝ => u (s, x.2)) s = fderiv ℝ u (s, x.2) (1, 0) := by
      exact ((hu.differentiable (by norm_num) (s, x.2)).hasFDerivAt.comp_hasDerivAt s
        ((hasDerivAt_id s).prodMk (hasDerivAt_const s x.2))).deriv
    change (deriv _ s) ^ 2 ≤ ‖fderiv ℝ u (s, x.2)‖ ^ 2
    rw [hd, ← sq_abs]
    have hnorm := (fderiv ℝ u (s, x.2)).le_opNorm (1, 0)
    simp only [Prod.norm_def, norm_one, norm_zero, max_eq_left zero_le_one, mul_one] at hnorm
    exact pow_le_pow_left₀ (abs_nonneg _) hnorm 2
  have hcolbound : (∫ t in Icc (-R) R, (deriv (fun t => u (y.1, t)) t) ^ 2) ≤
      ∫ t in Icc (-R) R, ‖fderiv ℝ u (y.1, t)‖ ^ 2 := by
    apply setIntegral_mono_on
      ((hcol.continuous_deriv (by norm_num)).pow 2).continuousOn.integrableOn_Icc
      ((hdu.comp (continuous_const.prodMk continuous_id)).norm.pow 2).continuousOn.integrableOn_Icc
      measurableSet_Icc
    intro t ht
    have hd : deriv (fun t : ℝ => u (y.1, t)) t = fderiv ℝ u (y.1, t) (0, 1) := by
      exact ((hu.differentiable (by norm_num) (y.1, t)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t y.1).prodMk (hasDerivAt_id t))).deriv
    change (deriv _ t) ^ 2 ≤ ‖fderiv ℝ u (y.1, t)‖ ^ 2
    rw [hd, ← sq_abs]
    have hnorm := (fderiv ℝ u (y.1, t)).le_opNorm (0, 1)
    simp only [Prod.norm_def, norm_one, norm_zero, max_eq_right zero_le_one, mul_one] at hnorm
    exact pow_le_pow_left₀ (abs_nonneg _) hnorm 2
  have hrowfinal := hrow'.trans (mul_le_mul_of_nonneg_left hrowbound (by linarith))
  have hcolfinal := hcol'.trans (mul_le_mul_of_nonneg_left hcolbound (by linarith))
  norm_num only [sub_neg_eq_add] at hrowfinal hcolfinal
  have hsq := sq_nonneg ((u x - u (y.1, x.2)) - (u (y.1, x.2) - u y))
  simp only [Prod.mk.eta] at hrowfinal hcolfinal
  nlinarith

def coordSquare (R : ℝ) : Set (ℝ × ℝ) := Icc (-R) R ×ˢ Icc (-R) R

lemma isCompact_coordSquare (R : ℝ) : IsCompact (coordSquare R) :=
  isCompact_Icc.prod isCompact_Icc

instance coordSquare_finiteMeasure (R : ℝ) :
    IsFiniteMeasure (volume.restrict (coordSquare R)) :=
  isFiniteMeasure_restrict.mpr (isCompact_coordSquare R).measure_ne_top

lemma mass_coordSquare {R : ℝ} (hR : 0 ≤ R) :
    (volume.restrict (coordSquare R)).real univ = (2 * R) ^ 2 := by
  simp only [Measure.real, Measure.restrict_apply_univ, coordSquare,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ R - -R)]
  ring

lemma integral_square_fst (f : ℝ → ℝ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ z in coordSquare R, f z.1) = (2 * R) * ∫ x in Icc (-R) R, f x := by
  rw [coordSquare, Measure.volume_eq_prod, ← Measure.prod_restrict, integral_fun_fst]
  simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ R - -R), smul_eq_mul]
  ring

lemma integral_square_snd (f : ℝ → ℝ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ z in coordSquare R, f z.2) = (2 * R) * ∫ x in Icc (-R) R, f x := by
  rw [coordSquare, Measure.volume_eq_prod, ← Measure.prod_restrict, integral_fun_snd]
  simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ R - -R), smul_eq_mul]
  ring

lemma integral_square_rows {d : ℝ × ℝ → ℝ} (hd : Continuous d) (R : ℝ) :
    (∫ t in Icc (-R) R, ∫ s in Icc (-R) R, d (s, t)) =
      ∫ z in coordSquare R, d z := by
  symm
  rw [coordSquare, Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact integral_prod_symm d (by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hd.continuousOn.integrableOn_compact (isCompact_coordSquare R))

lemma integral_square_cols {d : ℝ × ℝ → ℝ} (hd : Continuous d) (R : ℝ) :
    (∫ s in Icc (-R) R, ∫ t in Icc (-R) R, d (s, t)) =
      ∫ z in coordSquare R, d z := by
  symm
  rw [coordSquare, Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact integral_prod d (by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hd.continuousOn.integrableOn_compact (isCompact_coordSquare R))

lemma pointwise_sub_unitmean_sq_bound
    {u : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 1 u) {R : ℝ} (hR : 1 ≤ R)
    {x : ℝ × ℝ} (hx : x ∈ coordSquare R) :
    (u x - (∫ y in coordSquare 1, u y) / 4) ^ 2 ≤
      4 * R * (∫ s in Icc (-R) R, ‖fderiv ℝ u (s, x.2)‖ ^ 2) +
      2 * R * (∫ z in coordSquare R, ‖fderiv ℝ u z‖ ^ 2) := by
  let d : ℝ × ℝ → ℝ := fun z => ‖fderiv ℝ u z‖ ^ 2
  let row : ℝ → ℝ := fun t => ∫ s in Icc (-R) R, d (s, t)
  let col : ℝ → ℝ := fun s => ∫ t in Icc (-R) R, d (s, t)
  let E : ℝ := ∫ z in coordSquare R, d z
  have hd : Continuous d := (hu.continuous_fderiv (by norm_num)).norm.pow 2
  have hrow : Continuous row :=
    continuous_parametric_integral_of_continuous (f := fun t s => d (s, t))
      (hd.comp continuous_swap) isCompact_Icc
  have hcol : Continuous col :=
    continuous_parametric_integral_of_continuous (f := fun s t => d (s, t)) hd isCompact_Icc
  have hcolint : (∫ s in Icc (-R) R, col s) = E := integral_square_cols hd R
  have hcolnonneg : ∀ s, 0 ≤ col s := fun _ => integral_nonneg (fun _ => sq_nonneg _)
  have hmono : (∫ s in Icc (-1 : ℝ) 1, col s) ≤ E := by
    rw [← hcolint]
    apply setIntegral_mono_set hcol.continuousOn.integrableOn_Icc
      (Filter.Eventually.of_forall hcolnonneg)
    exact Filter.Eventually.of_forall (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  have hnorm : MemLp u 2 (volume.restrict (coordSquare 1)) :=
    (memLp_two_iff_integrable_sq hu.continuous.aestronglyMeasurable).mpr
      ((hu.continuous.pow 2).continuousOn.integrableOn_compact (isCompact_coordSquare 1))
  have hmass : (volume.restrict (coordSquare 1)).real univ = 4 := by
    norm_num [mass_coordSquare (show (0 : ℝ) ≤ 1 by norm_num)]
  have hJ := sq_sub_mean_le_mean_sq_sub hnorm (by rw [hmass]; norm_num) (u x)
  rw [hmass] at hJ
  have hbound : (∫ y in coordSquare 1, (u x - u y) ^ 2) ≤
      4 * R * (4 * row x.2 + 2 * E) := by
    have hi : (∫ y in coordSquare 1, (u x - u y) ^ 2) ≤
        ∫ y in coordSquare 1, 4 * R * (row x.2 + col y.1) := by
      apply setIntegral_mono_on
        (((continuous_const.sub hu.continuous).pow 2).continuousOn.integrableOn_compact
          (isCompact_coordSquare 1))
        (((continuous_const.add (hcol.comp continuous_fst)).const_mul _).continuousOn.integrableOn_compact
          (isCompact_coordSquare 1))
        (isCompact_coordSquare 1).measurableSet
      intro y hy
      apply square_path_estimate hu (by linarith) hx
      exact ⟨⟨by linarith [hy.1.1], by linarith [hy.1.2]⟩,
        ⟨by linarith [hy.2.1], by linarith [hy.2.2]⟩⟩
    have heval : (∫ y in coordSquare 1, 4 * R * (row x.2 + col y.1)) =
        4 * R * (4 * row x.2 + 2 * ∫ s in Icc (-1 : ℝ) 1, col s) := by
      have hc : Integrable (fun y : ℝ × ℝ => col y.1)
          (volume.restrict (coordSquare 1)) :=
        (hcol.comp continuous_fst).continuousOn.integrableOn_compact (isCompact_coordSquare 1)
      rw [integral_const_mul, integral_add (integrable_const (row x.2)) hc, integral_const,
        smul_eq_mul, hmass, integral_square_fst col (show (0 : ℝ) ≤ 1 by norm_num)]
      norm_num
    rw [heval] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  change (u x - (∫ y in coordSquare 1, u y) / 4) ^ 2 ≤ 4 * R * row x.2 + 2 * R * E
  linarith

lemma unitmean_poincare_square
    {u : ℝ × ℝ → ℝ} (hu : ContDiff ℝ 1 u) {R : ℝ} (hR : 1 ≤ R) :
    (∫ x in coordSquare R, (u x - (∫ y in coordSquare 1, u y) / 4) ^ 2) ≤
      (8 * R ^ 2 + 8 * R ^ 3) * (∫ z in coordSquare R, ‖fderiv ℝ u z‖ ^ 2) := by
  let d : ℝ × ℝ → ℝ := fun z => ‖fderiv ℝ u z‖ ^ 2
  let row : ℝ → ℝ := fun t => ∫ s in Icc (-R) R, d (s, t)
  let E : ℝ := ∫ z in coordSquare R, d z
  have hd : Continuous d := (hu.continuous_fderiv (by norm_num)).norm.pow 2
  have hrow : Continuous row :=
    continuous_parametric_integral_of_continuous (f := fun t s => d (s, t))
      (hd.comp continuous_swap) isCompact_Icc
  have hrowint : (∫ t in Icc (-R) R, row t) = E := integral_square_rows hd R
  have hR0 : 0 ≤ R := by linarith
  have hi : (∫ x in coordSquare R, (u x - (∫ y in coordSquare 1, u y) / 4) ^ 2) ≤
      ∫ x in coordSquare R, 4 * R * row x.2 + 2 * R * E := by
    apply setIntegral_mono_on
      (((hu.continuous.sub continuous_const).pow 2).continuousOn.integrableOn_compact
        (isCompact_coordSquare R))
      ((((hrow.comp continuous_snd).const_mul (4 * R)).add continuous_const).continuousOn.integrableOn_compact (isCompact_coordSquare R))
      (isCompact_coordSquare R).measurableSet
    exact fun x hx => pointwise_sub_unitmean_sq_bound hu hR hx
  have heval : (∫ x in coordSquare R, 4 * R * row x.2 + 2 * R * E) =
      (8 * R ^ 2 + 8 * R ^ 3) * E := by
    have hr : Integrable (fun x : ℝ × ℝ => 4 * R * row x.2)
        (volume.restrict (coordSquare R)) :=
      ((hrow.comp continuous_snd).const_mul (4 * R)).continuousOn.integrableOn_compact
        (isCompact_coordSquare R)
    rw [integral_add hr (integrable_const (2 * R * E)),
      integral_const_mul, integral_square_snd row hR0, hrowint,
      integral_const, smul_eq_mul, mass_coordSquare hR0]
    ring
  exact hi.trans_eq heval

def complexSquare (R : ℝ) : Set ℂ := Complex.equivRealProdCLM ⁻¹' coordSquare R

lemma isCompact_complexSquare (R : ℝ) : IsCompact (complexSquare R) :=
  Complex.equivRealProdCLM.toHomeomorph.isCompact_preimage.mpr (isCompact_coordSquare R)

instance complexSquare_finiteMeasure (R : ℝ) :
    IsFiniteMeasure (volume.restrict (complexSquare R)) :=
  isFiniteMeasure_restrict.mpr (isCompact_complexSquare R).measure_ne_top

lemma integral_complexSquare (f : ℂ → ℝ) (R : ℝ) :
    (∫ z in complexSquare R, f z) =
      ∫ w in coordSquare R, f (Complex.equivRealProdCLM.symm w) := by
  have h := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun w => f (Complex.equivRealProdCLM.symm w)) (coordSquare R)
  change (∫ x in complexSquare R, f (Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM x))) = _ at h
  simpa only [Complex.equivRealProdCLM.symm_apply_apply] using h

lemma norm_complexCoordInverse_le :
    ‖(Complex.equivRealProdCLM.symm : (ℝ × ℝ) →L[ℝ] ℂ)‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro w
  change ‖Complex.equivRealProdCLM.symm w‖ ≤ 2 * ‖w‖
  rw [Complex.equivRealProdCLM_symm_apply]
  calc
    ‖(w.1 : ℂ) + w.2 * Complex.I‖ ≤ ‖(w.1 : ℂ)‖ + ‖(w.2 : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = ‖w.1‖ + ‖w.2‖ := by simp
    _ ≤ 2 * ‖w‖ := by
      have h₁ : ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
      have h₂ : ‖w.2‖ ≤ ‖w‖ := norm_snd_le w
      linarith

lemma coord_derivative_norm_le {u : ℂ → ℝ} (hu : Differentiable ℝ u) (w : ℝ × ℝ) :
    ‖fderiv ℝ (fun y => u (Complex.equivRealProdCLM.symm y)) w‖ ≤
      2 * ‖gradient u (Complex.equivRealProdCLM.symm w)‖ := by
  change ‖fderiv ℝ (u ∘ ⇑Complex.equivRealProdCLM.symm) w‖ ≤ _
  rw [fderiv_comp w (hu _) Complex.equivRealProdCLM.symm.differentiableAt,
    ContinuousLinearEquiv.fderiv]
  calc
    ‖(fderiv ℝ u (Complex.equivRealProdCLM.symm w)).comp
        (Complex.equivRealProdCLM.symm : (ℝ × ℝ) →L[ℝ] ℂ)‖ ≤
        ‖fderiv ℝ u (Complex.equivRealProdCLM.symm w)‖ *
          ‖(Complex.equivRealProdCLM.symm : (ℝ × ℝ) →L[ℝ] ℂ)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ u (Complex.equivRealProdCLM.symm w)‖ * 2 :=
      mul_le_mul_of_nonneg_left norm_complexCoordInverse_le (norm_nonneg _)
    _ = 2 * ‖gradient u (Complex.equivRealProdCLM.symm w)‖ := by
      simp [gradient, mul_comm]

lemma unitmean_poincare_complexSquare
    {u : ℂ → ℝ} (hu : ContDiff ℝ 1 u) {R : ℝ} (hR : 1 ≤ R) :
    (∫ x in complexSquare R, (u x - (∫ y in complexSquare 1, u y) / 4) ^ 2) ≤
      (32 * R ^ 2 + 32 * R ^ 3) * (∫ z in complexSquare R, ‖gradient u z‖ ^ 2) := by
  let v : ℝ × ℝ → ℝ := fun w => u (Complex.equivRealProdCLM.symm w)
  have hv : ContDiff ℝ 1 v := hu.comp Complex.equivRealProdCLM.symm.contDiff
  have h := unitmean_poincare_square hv hR
  have hgrad : Continuous (gradient u) := (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp
    (hu.continuous_fderiv (by norm_num))
  have hbound : (∫ z in coordSquare R, ‖fderiv ℝ v z‖ ^ 2) ≤
      4 * ∫ z in coordSquare R, ‖gradient u (Complex.equivRealProdCLM.symm z)‖ ^ 2 := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on
      (((hv.continuous_fderiv (by norm_num)).norm.pow 2).continuousOn.integrableOn_compact
        (isCompact_coordSquare R))
      ((((hgrad.comp Complex.equivRealProdCLM.symm.continuous).norm.pow 2).const_mul 4).continuousOn.integrableOn_compact (isCompact_coordSquare R))
      (isCompact_coordSquare R).measurableSet
    intro z hz
    have hn := coord_derivative_norm_le (hu.differentiable (by norm_num)) z
    change ‖fderiv ℝ v z‖ ^ 2 ≤ 4 * ‖gradient u (Complex.equivRealProdCLM.symm z)‖ ^ 2
    change ‖fderiv ℝ v z‖ ≤ 2 * ‖gradient u (Complex.equivRealProdCLM.symm z)‖ at hn
    nlinarith [norm_nonneg (fderiv ℝ v z), norm_nonneg (gradient u (Complex.equivRealProdCLM.symm z))]
  rw [integral_complexSquare u 1, integral_complexSquare _ R, integral_complexSquare _ R]
  change (∫ x in coordSquare R, (v x - (∫ y in coordSquare 1, v y) / 4) ^ 2) ≤ _
  have hc : 0 ≤ 8 * R ^ 2 + 8 * R ^ 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hbound hc]

end MumfordShah
end

end OAI
