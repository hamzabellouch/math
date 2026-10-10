import Mathlib
import OAI.Probability.GaussianInformation.Dyadic.BoxKernels

namespace OAI
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
open MeasureTheory Metric Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
open InnerProductSpace Matrix MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
namespace RepeatedLocalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma gram_linearCombination {ι : Type*} [Fintype ι] (g : ι → E)
    (T : Matrix ι ι ℝ) :
    Matrix.gram ℝ (fun j => ∑ i, T i j • g i) = Tᵀ * Matrix.gram ℝ g * T := by
  ext i j
  simp only [Matrix.gram_apply, sum_inner, inner_sum, real_inner_smul_left,
    real_inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

noncomputable def gramTriangular {q : ℕ} (f : Fin q → E) : Matrix (Fin q) (Fin q) ℝ :=
  fun i j => (if i = j then 1 else 0) +
    (if i < j then ⟪gramSchmidt ℝ f i, f j⟫ / ‖gramSchmidt ℝ f i‖ ^ 2 else 0)

lemma gramTriangular_expansion {q : ℕ} (f : Fin q → E) (j : Fin q) :
    f j = ∑ i, gramTriangular f i j • gramSchmidt ℝ f i := by
  rw [gramSchmidt_def'' ℝ f j]
  have hfin : (Finset.univ.filter fun i : Fin q => i < j) = Finset.Iio j := by
    ext i
    simp
  simp only [gramTriangular, add_smul, Finset.sum_add_distrib, ite_smul, one_smul,
    zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_filter, hfin]
  simp only [RCLike.ofReal_real_eq_id, id_eq]

lemma gramTriangular_det {q : ℕ} (f : Fin q → E) : (gramTriangular f).det = 1 := by
  have htri : (gramTriangular f).IsUpperTriangular := by
    intro i j hij
    change j < i at hij
    simp only [gramTriangular, ite_eq_right (ne_of_gt hij), ite_eq_right (not_lt.mpr (le_of_lt hij)),
      zero_add]
  rw [Matrix.det_of_isUpperTriangular htri]
  simp [gramTriangular]

lemma gram_gramSchmidt {q : ℕ} (f : Fin q → E) :
    Matrix.gram ℝ (gramSchmidt ℝ f) =
      Matrix.diagonal (fun i => ‖gramSchmidt ℝ f i‖ ^ 2) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp
  · simp [h, gramSchmidt_orthogonal ℝ f h]

lemma gram_det_eq_prod_gramSchmidt {q : ℕ} (f : Fin q → E) :
    (Matrix.gram ℝ f).det = (∏ i, ‖gramSchmidt ℝ f i‖)^2 := by
  have he : f = (fun j => ∑ i, gramTriangular f i j • gramSchmidt ℝ f i) :=
    funext (gramTriangular_expansion f)
  calc
    (Matrix.gram ℝ f).det =
        ((gramTriangular f)ᵀ * Matrix.gram ℝ (gramSchmidt ℝ f) * gramTriangular f).det := by
      conv_lhs => rw [he]
      rw [gram_linearCombination]
    _ = (∏ i, ‖gramSchmidt ℝ f i‖)^2 := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
        gramTriangular_det, one_mul, mul_one, gram_gramSchmidt, Matrix.det_diagonal,
        Finset.prod_pow]

lemma sqrt_gram_det_eq_prod_gramSchmidt {q : ℕ} (f : Fin q → E) :
    Real.sqrt (Matrix.gram ℝ f).det = ∏ i, ‖gramSchmidt ℝ f i‖ := by
  rw [gram_det_eq_prod_gramSchmidt, Real.sqrt_sq (Finset.prod_nonneg fun _ _ => norm_nonneg _)]

lemma gramSchmidt_real_def {q : ℕ} (f : Fin q → E) (j : Fin q) :
    gramSchmidt ℝ f j = f j - ∑ i ∈ Finset.Iio j,
      (⟪gramSchmidt ℝ f i, f j⟫ / ‖gramSchmidt ℝ f i‖ ^ 2) • gramSchmidt ℝ f i := by
  apply eq_sub_iff_add_eq.mpr
  simpa only [RCLike.ofReal_real_eq_id, id_eq] using (gramSchmidt_def'' ℝ f j).symm

lemma measurable_gramSchmidt {q : ℕ} [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (j : Fin q) :
    Measurable (fun f : Fin q → E => gramSchmidt ℝ f j) := by
  induction j using (wellFounded_lt (α := Fin q)).induction with
  | h j ih =>
    simp_rw [gramSchmidt_real_def (j := j)]
    refine (measurable_pi_apply j).sub (Finset.measurable_sum _ fun i hi => ?_)
    have hmi := ih i (Finset.mem_Iio.mp hi)
    exact ((hmi.inner (measurable_pi_apply j)).div (hmi.norm.pow_const 2)).smul hmi

lemma gramSchmidt_prefix_congr {q : ℕ} {f g : Fin q → E} (j : Fin q)
    (h : ∀ i ≤ j, f i = g i) : gramSchmidt ℝ f j = gramSchmidt ℝ g j := by
  induction j using (wellFounded_lt (α := Fin q)).induction with
  | h j ih =>
    rw [gramSchmidt_real_def, gramSchmidt_real_def, h j le_rfl]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hgi := ih i (Finset.mem_Iio.mp hi) (fun a ha => h a (ha.trans (Finset.mem_Iio.mp hi).le))
    rw [hgi]

lemma gramSchmidt_residual_mem_span {q : ℕ} (f : Fin q → E) (j : Fin q) :
    f j - gramSchmidt ℝ f j ∈ Submodule.span ℝ (f '' Set.Iio j) := by
  rw [gramSchmidt_real_def, sub_sub_cancel]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  rw [← span_gramSchmidt_Iio ℝ f j]
  exact Submodule.subset_span (mem_image_of_mem _ (Finset.mem_Iio.mp hi))

lemma infDist_span_le_gramSchmidt {q : ℕ} (f : Fin q → E) (j : Fin q) :
    Metric.infDist (f j) (Submodule.span ℝ (f '' Set.Iio j) : Set E) ≤
      ‖gramSchmidt ℝ f j‖ := by
  simpa [dist_eq_norm] using
    (Metric.infDist_le_dist_of_mem (x := f j) (gramSchmidt_residual_mem_span f j))

end RepeatedLocalization

end OAI
