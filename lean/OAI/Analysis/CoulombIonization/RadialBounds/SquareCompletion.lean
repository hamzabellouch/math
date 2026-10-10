import Mathlib
import OAI.Analysis.CoulombIonization.Model

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution

namespace CoulombAtom

section SquareCompletion
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma derivative_norm_sq {f : E → ℂ} {point : E}
    (hf : DifferentiableAt ℝ f point) (v : E) :
    fderiv ℝ (fun y => ‖f y‖ ^ 2) point v = 2 * ⟪f point, fderiv ℝ f point v⟫_ℝ := by
  rw [hf.hasFDerivAt.norm_sq.fderiv]
  simp
  ring

lemma square_completion_pointwise {f : E → ℂ} {point : E}
    (hf : DifferentiableAt ℝ f point)
    (v : E) (b : ℝ) :
    ‖fderiv ℝ f point v + b • f point‖ ^ 2 =
      ‖fderiv ℝ f point v‖ ^ 2 + b ^ 2 * ‖f point‖ ^ 2 +
        b * fderiv ℝ (fun y => ‖f y‖ ^ 2) point v := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, derivative_norm_sq hf, real_inner_comm (fderiv ℝ f point v) (f point)]
  ring

variable [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]

lemma square_completion_integral {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) {b : E → ℝ} (hb : ContDiff ℝ ∞ b) (v : E) :
    (∫ x, ‖fderiv ℝ f x v + b x • f x‖ ^ 2) =
      (∫ x, ‖fderiv ℝ f x v‖ ^ 2) + (∫ x, (b x) ^ 2 * ‖f x‖ ^ 2) -
        (∫ x, fderiv ℝ b x v * ‖f x‖ ^ 2) := by
  let q : E → ℝ := fun x => ‖f x‖ ^ 2
  have hq : ContDiff ℝ ∞ q := hf.norm_sq ℝ
  have hcq : HasCompactSupport q := hcf.comp_left (g := fun z : ℂ => ‖z‖ ^ (2 : ℕ)) (by simp)
  have hdf : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcdf : HasCompactSupport (fun x => fderiv ℝ f x v) :=
    (hcf.fderiv ℝ).comp_left (g := fun A : E →L[ℝ] ℂ => A v) (by simp)
  have hdb : Continuous (fun x => fderiv ℝ b x v) :=
    (hb.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdq : Continuous (fun x => fderiv ℝ q x v) :=
    (hq.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcdq : HasCompactSupport (fun x => fderiv ℝ q x v) :=
    (hcq.fderiv ℝ).comp_left (g := fun A : E →L[ℝ] ℝ => A v) (by simp)
  have ik : Integrable (fun x => ‖fderiv ℝ f x v‖ ^ 2) :=
    (hdf.norm.pow 2).integrable_of_hasCompactSupport (hcdf.comp_left (g := fun z : ℂ => ‖z‖ ^ (2 : ℕ)) (by simp))
  have ibq : Integrable (fun x => (b x) ^ 2 * q x) :=
    ((hb.continuous.pow 2).mul hq.continuous).integrable_of_hasCompactSupport hcq.mul_left
  have idbq : Integrable (fun x => fderiv ℝ b x v * q x) :=
    (hdb.mul hq.continuous).integrable_of_hasCompactSupport hcq.mul_left
  have ibdq : Integrable (fun x => b x * fderiv ℝ q x v) :=
    (hb.continuous.mul hdq).integrable_of_hasCompactSupport hcdq.mul_left
  have ibq' : Integrable (fun x => b x * q x) :=
    (hb.continuous.mul hq.continuous).integrable_of_hasCompactSupport hcq.mul_left
  have hip : (∫ x, b x * fderiv ℝ q x v) = -(∫ x, fderiv ℝ b x v * q x) :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable idbq ibdq ibq'
      (fun x _ => hb.differentiable (by simp) x)
      (fun x _ => hq.differentiable (by simp) x)
  calc
    _ = ∫ x, (‖fderiv ℝ f x v‖ ^ 2 + (b x) ^ 2 * q x) +
        b x * fderiv ℝ q x v :=
      integral_congr_ae (Filter.Eventually.of_forall fun x =>
        square_completion_pointwise (hf.differentiable (by simp) x) v (b x))
    _ = _ := by
      have hsum := integral_add (ik.add ibq) ibdq
      simp only [Pi.add_apply] at hsum
      rw [hsum, integral_add ik ibq, hip]
      rfl

lemma square_completion_bound {ι : Type*} [Fintype ι]
    {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
    {b : ι → E → ℝ} (hb : ∀ i, ContDiff ℝ ∞ (b i)) (v : ι → E)
    {V : E → ℝ} (hV : Continuous V) {C : ℝ}
    (hbnd : ∀ x, ∑ i, (b i x) ^ 2 ≤ C)
    (hdiv : ∀ x, V x ≤ ∑ i, fderiv ℝ (b i) x (v i)) :
    (∫ x, V x * ‖f x‖ ^ 2) ≤
      (∑ i, ∫ x, ‖fderiv ℝ f x (v i)‖ ^ 2) + C * (∫ x, ‖f x‖ ^ 2) := by
  have hcq : HasCompactSupport (fun x => ‖f x‖ ^ 2) :=
    hcf.comp_left (g := fun z : ℂ => ‖z‖ ^ (2 : ℕ)) (by simp)
  have hq : Continuous (fun x => ‖f x‖ ^ 2) := hf.continuous.norm.pow 2
  have iq : Integrable (fun x => ‖f x‖ ^ 2) := hq.integrable_of_hasCompactSupport hcq
  have ib (i : ι) : Integrable (fun x => (b i x) ^ 2 * ‖f x‖ ^ 2) :=
    ((hb i).continuous.pow 2 |>.mul hq).integrable_of_hasCompactSupport hcq.mul_left
  have idb (i : ι) : Integrable (fun x => fderiv ℝ (b i) x (v i) * ‖f x‖ ^ 2) :=
    (((hb i).continuous_fderiv (by simp)).clm_apply continuous_const |>.mul hq
      ).integrable_of_hasCompactSupport hcq.mul_left
  have hbound (i : ι) : (∫ x, fderiv ℝ (b i) x (v i) * ‖f x‖ ^ 2) ≤
      (∫ x, ‖fderiv ℝ f x (v i)‖ ^ 2) + (∫ x, (b i x) ^ 2 * ‖f x‖ ^ 2) := by
    have hn : 0 ≤ (∫ x : E, ‖fderiv ℝ f x (v i) + b i x • f x‖ ^ 2) :=
      integral_nonneg (fun x : E => sq_nonneg _)
    rw [square_completion_integral hf hcf (hb i)] at hn
    linarith
  calc
    _ ≤ ∫ x, ∑ i, fderiv ℝ (b i) x (v i) * ‖f x‖ ^ 2 := by
      apply integral_mono
        ((hV.mul hq).integrable_of_hasCompactSupport hcq.mul_left)
        (integrable_finsetSum _ fun i _ => idb i)
      intro x
      simpa only [Finset.sum_mul, Pi.mul_apply] using
        mul_le_mul_of_nonneg_right (hdiv x) (sq_nonneg ‖f x‖)
    _ = ∑ i, ∫ x, fderiv ℝ (b i) x (v i) * ‖f x‖ ^ 2 :=
      integral_finsetSum _ fun i _ => idb i
    _ ≤ ∑ i, ((∫ x, ‖fderiv ℝ f x (v i)‖ ^ 2) +
        (∫ x, (b i x) ^ 2 * ‖f x‖ ^ 2)) := Finset.sum_le_sum fun i _ => hbound i
    _ = (∑ i, ∫ x, ‖fderiv ℝ f x (v i)‖ ^ 2) +
        ∫ x, ∑ i, (b i x) ^ 2 * ‖f x‖ ^ 2 := by
      rw [Finset.sum_add_distrib, integral_finsetSum _ fun i _ => ib i]
    _ ≤ _ := by
      apply add_le_add (le_refl _)
      rw [← integral_const_mul]
      apply integral_mono (integrable_finsetSum _ fun i _ => ib i) (iq.const_mul C)
      intro x
      simpa only [Finset.sum_mul, Pi.mul_apply] using
        mul_le_mul_of_nonneg_right (hbnd x) (sq_nonneg ‖f x‖)

omit [FiniteDimensional ℝ E] [(volume : Measure E).IsAddHaarMeasure] in
lemma integrable_norm_sq_derivative {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (hf2 : MemLp f 2) (v : E) (hdf2 : MemLp (fun x => fderiv ℝ f x v) 2) :
    Integrable (fun x => fderiv ℝ (fun y => ‖f y‖ ^ 2) x v) := by
  have hi := (hf2.norm.integrable_mul hdf2.norm).const_mul 2
  apply hi.mono'
    (((hf.norm_sq ℝ).continuous_fderiv (by simp)).clm_apply continuous_const
      ).aestronglyMeasurable
  filter_upwards [] with x
  rw [derivative_norm_sq (hf.differentiable (by simp) x), norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (by norm_num)

lemma square_completion_integral_of_memLp {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (hf2 : MemLp f 2) {b : E → ℝ} (hb : ContDiff ℝ ∞ b) (v : E)
    (hdf2 : MemLp (fun x => fderiv ℝ f x v) 2)
    {B D : ℝ} (hbnd : ∀ x, ‖b x‖ ≤ B)
    (hdbnd : ∀ x, ‖fderiv ℝ b x v‖ ≤ D) :
    (∫ x, ‖fderiv ℝ f x v + b x • f x‖ ^ 2) =
      (∫ x, ‖fderiv ℝ f x v‖ ^ 2) + (∫ x, (b x) ^ 2 * ‖f x‖ ^ 2) -
        (∫ x, fderiv ℝ b x v * ‖f x‖ ^ 2) := by
  let q : E → ℝ := fun x => ‖f x‖ ^ 2
  have hq : ContDiff ℝ ∞ q := hf.norm_sq ℝ
  have iq : Integrable q := hf2.norm.integrable_sq
  have ik := hdf2.norm.integrable_sq
  have ibq : Integrable (fun x => (b x) ^ 2 * q x) :=
    iq.bdd_mul (hb.continuous.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbnd x) _)
  have idbq : Integrable (fun x => fderiv ℝ b x v * q x) :=
    iq.bdd_mul (((hb.continuous_fderiv (by simp)).clm_apply continuous_const
      ).aestronglyMeasurable) (Eventually.of_forall hdbnd)
  have ibdq : Integrable (fun x => b x * fderiv ℝ q x v) :=
    (integrable_norm_sq_derivative hf hf2 v hdf2).bdd_mul hb.continuous.aestronglyMeasurable
      (Eventually.of_forall hbnd)
  have ibq' : Integrable (fun x => b x * q x) :=
    iq.bdd_mul hb.continuous.aestronglyMeasurable (Eventually.of_forall hbnd)
  have hip : (∫ x, b x * fderiv ℝ q x v) = -(∫ x, fderiv ℝ b x v * q x) :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable idbq ibdq ibq'
      (fun x _ => hb.differentiable (by simp) x)
      (fun x _ => hq.differentiable (by simp) x)
  calc
    _ = ∫ x, (‖fderiv ℝ f x v‖ ^ 2 + (b x) ^ 2 * q x) +
        b x * fderiv ℝ q x v :=
      integral_congr_ae (Eventually.of_forall fun x =>
        square_completion_pointwise (hf.differentiable (by simp) x) v (b x))
    _ = _ := by
      have hsum := integral_add (ik.add ibq) ibdq
      simp only [Pi.add_apply] at hsum
      rw [hsum, integral_add ik ibq, hip]
      rfl

lemma square_completion_bound_of_memLp {ι : Type*} [Fintype ι]
    {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (hf2 : MemLp f 2)
    {b : ι → E → ℝ} (hb : ∀ i, ContDiff ℝ ∞ (b i)) (v : ι → E)
    (hdf2 : ∀ i, MemLp (fun x => fderiv ℝ f x (v i)) 2)
    {B D : ι → ℝ} (hbb : ∀ i x, ‖b i x‖ ≤ B i)
    (hdb : ∀ i x, ‖fderiv ℝ (b i) x (v i)‖ ≤ D i)
    {V : E → ℝ} (hVq : Integrable (fun x => V x * ‖f x‖ ^ 2)) {C : ℝ}
    (hbnd : ∀ x, ∑ i, (b i x) ^ 2 ≤ C)
    (hdiv : ∀ x, V x ≤ ∑ i, fderiv ℝ (b i) x (v i)) :
    (∫ x, V x * ‖f x‖ ^ 2) ≤
      (∑ i, ∫ x, ‖fderiv ℝ f x (v i)‖ ^ 2) + C * (∫ x, ‖f x‖ ^ 2) := by
  have iq : Integrable (fun x => ‖f x‖ ^ 2) := hf2.norm.integrable_sq
  have ib (i : ι) : Integrable (fun x => (b i x) ^ 2 * ‖f x‖ ^ 2) :=
    iq.bdd_mul ((hb i).continuous.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbb i x) _)
  have idb (i : ι) : Integrable (fun x => fderiv ℝ (b i) x (v i) * ‖f x‖ ^ 2) :=
    iq.bdd_mul (((hb i).continuous_fderiv (by simp)).clm_apply continuous_const
      ).aestronglyMeasurable (Eventually.of_forall (hdb i))
  have hbound (i : ι) : (∫ x, fderiv ℝ (b i) x (v i) * ‖f x‖ ^ 2) ≤
      (∫ x, ‖fderiv ℝ f x (v i)‖ ^ 2) + (∫ x, (b i x) ^ 2 * ‖f x‖ ^ 2) := by
    have hn : 0 ≤ (∫ x : E, ‖fderiv ℝ f x (v i) + b i x • f x‖ ^ 2) :=
      integral_nonneg (fun x : E => sq_nonneg _)
    rw [square_completion_integral_of_memLp hf hf2 (hb i) (v i) (hdf2 i)
      (hbb i) (hdb i)] at hn
    linarith
  calc
    _ ≤ ∫ x, ∑ i, fderiv ℝ (b i) x (v i) * ‖f x‖ ^ 2 := by
      apply integral_mono hVq (integrable_finsetSum _ fun i _ => idb i)
      intro x
      simpa only [Finset.sum_mul, Pi.mul_apply] using
        mul_le_mul_of_nonneg_right (hdiv x) (sq_nonneg ‖f x‖)
    _ = ∑ i, ∫ x, fderiv ℝ (b i) x (v i) * ‖f x‖ ^ 2 :=
      integral_finsetSum _ fun i _ => idb i
    _ ≤ ∑ i, ((∫ x, ‖fderiv ℝ f x (v i)‖ ^ 2) +
        (∫ x, (b i x) ^ 2 * ‖f x‖ ^ 2)) := Finset.sum_le_sum fun i _ => hbound i
    _ = (∑ i, ∫ x, ‖fderiv ℝ f x (v i)‖ ^ 2) +
        ∫ x, ∑ i, (b i x) ^ 2 * ‖f x‖ ^ 2 := by
      rw [Finset.sum_add_distrib, integral_finsetSum _ fun i _ => ib i]
    _ ≤ _ := by
      apply add_le_add (le_refl _)
      rw [← integral_const_mul]
      apply integral_mono (integrable_finsetSum _ fun i _ => ib i) (iq.const_mul C)
      intro x
      simpa only [Finset.sum_mul, Pi.mul_apply] using
        mul_le_mul_of_nonneg_right (hbnd x) (sq_nonneg ‖f x‖)

end SquareCompletion

def regularizedRadius (ε : ℝ) (x : Space) : ℝ := Real.sqrt (‖x‖ ^ 2 + ε ^ 2)

def radialField (ε : ℝ) (a : Fin 3) (x : Space) : ℝ := x a / regularizedRadius ε x

lemma regularizedRadius_pos {ε : ℝ} (hε : 0 < ε) (x : Space) :
    0 < regularizedRadius ε x := by
  apply Real.sqrt_pos.2
  positivity

lemma regularizedRadius_sq (ε : ℝ) (x : Space) :
    regularizedRadius ε x ^ 2 = ‖x‖ ^ 2 + ε ^ 2 := Real.sq_sqrt (by positivity)

lemma regularizedRadius_smooth {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (regularizedRadius ε) := by
  apply (contDiff_id.norm_sq ℝ |>.add contDiff_const).sqrt
  intro x
  positivity

lemma radialField_smooth {ε : ℝ} (hε : 0 < ε) (a : Fin 3) :
    ContDiff ℝ ∞ (radialField ε a) :=
  (EuclideanSpace.proj a).contDiff.div (regularizedRadius_smooth hε)
    (fun x => (regularizedRadius_pos hε x).ne')

lemma radialField_fderiv {ε : ℝ} (hε : 0 < ε) (a : Fin 3) (x : Space) :
    fderiv ℝ (radialField ε a) x (EuclideanSpace.single a 1) =
      (regularizedRadius ε x)⁻¹ - (x a) ^ 2 / (regularizedRadius ε x) ^ 3 := by
  have ht := ((hasFDerivAt_id (𝕜 := ℝ) x).norm_sq).add_const (ε ^ 2)
  have hs := (Real.hasDerivAt_sqrt (by positivity : ‖x‖ ^ 2 + ε ^ 2 ≠ 0)
    ).comp_hasFDerivAt x ht
  have hi := (hasDerivAt_inv (regularizedRadius_pos hε x).ne').comp_hasFDerivAt x hs
  have hp := ((EuclideanSpace.proj a).hasFDerivAt (x := x)).mul hi
  change (fderiv ℝ ((EuclideanSpace.proj a : Space → ℝ) *
      ((fun y : ℝ => y⁻¹) ∘ regularizedRadius ε)) x) _ = _
  rw [hp.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, innerSL_apply_apply, EuclideanSpace.inner_single_right,
    conj_trivial, one_mul]
  simp [EuclideanSpace.proj, regularizedRadius]
  field_simp
  ring

lemma sum_coordinate_sq (x : Space) : ∑ a : Fin 3, (x a) ^ 2 = ‖x‖ ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_sq_eq x).symm

lemma coordinate_sq_le (x : Space) (a : Fin 3) : (x a) ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [← sum_coordinate_sq]
  exact Finset.single_le_sum (fun b _ => sq_nonneg (x b)) (Finset.mem_univ a)

lemma norm_le_regularizedRadius (ε : ℝ) (x : Space) : ‖x‖ ≤ regularizedRadius ε x := by
  calc
    ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg ε))

lemma le_regularizedRadius {ε : ℝ} (hε : 0 ≤ ε) (x : Space) :
    ε ≤ regularizedRadius ε x := by
  calc
    ε = Real.sqrt (ε ^ 2) := (Real.sqrt_sq hε).symm
    _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg ‖x‖))

lemma radialField_norm_le {ε : ℝ} (hε : 0 < ε) (a : Fin 3) (x : Space) :
    ‖radialField ε a x‖ ≤ 1 := by
  have hr := regularizedRadius_pos hε x
  have hcoord : |x a| ≤ ‖x‖ := by
    have hh := coordinate_sq_le x a
    nlinarith [abs_nonneg (x a), sq_abs (x a), norm_nonneg x]
  change ‖x a / regularizedRadius ε x‖ ≤ 1
  rw [norm_div, Real.norm_eq_abs, Real.norm_of_nonneg hr.le, div_le_one hr]
  exact hcoord.trans (norm_le_regularizedRadius ε x)

lemma sum_radialField_sq_le {ε : ℝ} (hε : 0 < ε) (x : Space) :
    ∑ a : Fin 3, (radialField ε a x) ^ 2 ≤ 1 := by
  simp only [radialField, div_pow, ← Finset.sum_div, sum_coordinate_sq]
  apply (div_le_one (sq_pos_of_pos (regularizedRadius_pos hε x))).2
  rw [regularizedRadius_sq]
  exact le_add_of_nonneg_right (sq_nonneg ε)

lemma radialField_derivative_bounds {ε : ℝ} (hε : 0 < ε) (a : Fin 3) (x : Space) :
    0 ≤ fderiv ℝ (radialField ε a) x (EuclideanSpace.single a 1) ∧
      fderiv ℝ (radialField ε a) x (EuclideanSpace.single a 1) ≤ ε⁻¹ := by
  let r := regularizedRadius ε x
  have hr : 0 < r := regularizedRadius_pos hε x
  have hxr : (x a) ^ 2 ≤ r ^ 2 := by
    calc
      _ ≤ ‖x‖ ^ 2 := coordinate_sq_le x a
      _ ≤ _ := by rw [regularizedRadius_sq]; exact le_add_of_nonneg_right (sq_nonneg ε)
  have heq : r ^ 2 / r ^ 3 = r⁻¹ := by field_simp
  have hle : (x a) ^ 2 / r ^ 3 ≤ r⁻¹ := by
    rw [← heq]
    exact div_le_div_of_nonneg_right hxr (pow_nonneg hr.le _)
  rw [radialField_fderiv hε]
  constructor
  · exact sub_nonneg.mpr hle
  · calc
      r⁻¹ - (x a) ^ 2 / r ^ 3 ≤ r⁻¹ := sub_le_self _ (by positivity)
      _ ≤ ε⁻¹ := inv_anti₀ hε (le_regularizedRadius hε.le x)

lemma radialField_divergence {ε : ℝ} (hε : 0 < ε) (x : Space) :
    2 * ‖x‖ / (regularizedRadius ε x) ^ 2 ≤
      ∑ a : Fin 3, fderiv ℝ (radialField ε a) x (EuclideanSpace.single a 1) := by
  let r := regularizedRadius ε x
  have hr : 0 < r := regularizedRadius_pos hε x
  have hnr : ‖x‖ ^ 2 ≤ r ^ 2 := by rw [regularizedRadius_sq]; exact le_add_of_nonneg_right (sq_nonneg ε)
  have heq : r ^ 2 / r ^ 3 = r⁻¹ := by field_simp
  have hle : ‖x‖ ^ 2 / r ^ 3 ≤ r⁻¹ := by
    rw [← heq]
    exact div_le_div_of_nonneg_right hnr (pow_nonneg hr.le _)
  have hnorm : ‖x‖ / r ^ 2 ≤ r⁻¹ := by
    calc
      _ ≤ r / r ^ 2 := div_le_div_of_nonneg_right (norm_le_regularizedRadius ε x)
        (sq_nonneg _)
      _ = _ := by field_simp
  simp only [radialField_fderiv hε, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div, sum_coordinate_sq]
  change 2 * ‖x‖ / r ^ 2 ≤ 3 * r⁻¹ - ‖x‖ ^ 2 / r ^ 3
  have heq2 : 2 * ‖x‖ / r ^ 2 = 2 * (‖x‖ / r ^ 2) := by ring
  rw [heq2]
  linarith

def regularizedCoulomb (ε : ℝ) (x : Space) : ℝ :=
  ‖x‖ / (regularizedRadius ε x) ^ 2

lemma regularizedCoulomb_nonneg (ε : ℝ) (x : Space) : 0 ≤ regularizedCoulomb ε x := by
  unfold regularizedCoulomb
  positivity

lemma regularizedCoulomb_le {ε : ℝ} (hε : 0 < ε) (x : Space) :
    regularizedCoulomb ε x ≤ ε⁻¹ := by
  let r := regularizedRadius ε x
  have hr : 0 < r := regularizedRadius_pos hε x
  calc
    _ ≤ r / r ^ 2 := div_le_div_of_nonneg_right (norm_le_regularizedRadius ε x) (sq_nonneg _)
    _ = r⁻¹ := by field_simp
    _ ≤ ε⁻¹ := inv_anti₀ hε (le_regularizedRadius hε.le x)

lemma regularizedCoulomb_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (regularizedCoulomb ε) :=
  continuous_norm.div ((regularizedRadius_smooth hε).continuous.pow 2)
    (fun x => pow_ne_zero _ (regularizedRadius_pos hε x).ne')

lemma coordinate_radialField_fderiv {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (i : Fin N) (a : Fin 3) (x : Configuration N) :
    fderiv ℝ (fun y : Configuration N => radialField ε a (y i)) x (direction i a) =
      fderiv ℝ (radialField ε a) (x i) (EuclideanSpace.single a 1) := by
  have hh := ((radialField_smooth hε a).differentiable (by simp) (x i)).hasFDerivAt.comp x
    ((ContinuousLinearMap.proj i : Configuration N →L[ℝ] Space).hasFDerivAt (x := x))
  change (fderiv ℝ ((radialField ε a) ∘
    (ContinuousLinearMap.proj i : Configuration N →L[ℝ] Space)) x) _ = _
  rw [hh.fderiv]
  simp [direction]

end CoulombAtom

end

end OAI
