import OAI.Probability.SpanningForest.TransferCurrent
import OAI.Probability.SpanningForest.FiniteGradientResponse

namespace OAI

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Operator

namespace Problem336.TransferCurrent

variable {n : Type*} [Fintype n] [DecidableEq n]

local instance : TopologicalSpace (Matrix n n ℝ) :=
  (Matrix.linftyOpNormedAddCommGroup : NormedAddCommGroup (Matrix n n ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

lemma hasDerivAt_inverse_curve (M : ℝ → Matrix n n ℝ) (D : Matrix n n ℝ) (t : ℝ)
    (hM : HasDerivAt M D t) (hU : IsUnit (M t)) :
    HasDerivAt (fun s => (M s)⁻¹) (-((M t)⁻¹ * D * (M t)⁻¹)) t := by
  rcases hU with ⟨u, hu⟩
  have h := (hasFDerivAt_ringInverse (𝕜 := ℝ) u).comp_hasDerivAt_of_eq t hM hu
  simpa only [Function.comp_def, ← Matrix.nonsing_inv_eq_ringInverse,
    neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    Matrix.coe_units_inv, hu] using h

lemma hasDerivAt_bilinear_inverse_curve (M : ℝ → Matrix n n ℝ) (D : Matrix n n ℝ)
    (t : ℝ) (hM : HasDerivAt M D t) (hU : IsUnit (M t)) (a b : n → ℝ) :
    HasDerivAt (fun s => bilinear (M s)⁻¹ a b)
      (-bilinear ((M t)⁻¹ * D * (M t)⁻¹) a b) t := by
  have h := (bilinearCLM a b).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_inverse_curve M D t hM hU)
  simpa only [Function.comp_def, bilinearCLM_apply, bilinear_neg] using h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open FiniteGradientResponse

omit [Fintype ι] [DecidableEq ι] in
lemma hasDerivAt_segmentField_apply (h k : ι → ℝ) (i : ι) (t : ℝ) :
    HasDerivAt (fun s => segmentField h k s i) (k i - h i) t := by
  simpa only [segmentField, Function.id_def, one_mul] using
    ((hasDerivAt_id t).mul_const (k i - h i)).const_add (h i)

omit [DecidableEq ι] in
lemma hasDerivAt_laplacian_segment (a : ι → n → ℝ) (h k : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => laplacian a (segmentField h k s))
      (∑ f, (Real.exp (segmentField h k t f) * (k f - h f)) •
        Matrix.vecMulVec (a f) (a f)) t := by
  have hf (f : ι) : HasDerivAt
      (fun s => Real.exp (segmentField h k s f) • Matrix.vecMulVec (a f) (a f))
      ((Real.exp (segmentField h k t f) * (k f - h f)) • Matrix.vecMulVec (a f) (a f)) t :=
    (hasDerivAt_segmentField_apply h k f t).exp.smul_const _
  simpa only [laplacian, Finset.sum_apply] using
    HasDerivAt.fun_sum (u := Finset.univ) (fun f _ => hf f)

omit [DecidableEq ι] in
lemma bilinear_laplacian_direction (a : ι → n → ℝ) (h d : ι → ℝ) (e : ι) :
    Real.exp (h e) * bilinear
      ((laplacian a h)⁻¹ *
        (∑ f, (Real.exp (h f) * d f) • Matrix.vecMulVec (a f) (a f)) *
          (laplacian a h)⁻¹) (a e) (a e) =
      ∑ f, responseSquare a h e f * d f := by
  rw [Matrix.mul_sum, Matrix.sum_mul]
  change Real.exp (h e) * bilinearCLM (a e) (a e) (∑ f,
    (laplacian a h)⁻¹ * ((Real.exp (h f) * d f) • Matrix.vecMulVec (a f) (a f)) *
      (laplacian a h)⁻¹) = _
  rw [map_sum, Finset.mul_sum]
  simp only [bilinearCLM_apply]
  apply Finset.sum_congr rfl
  intro f hf
  rw [Matrix.mul_smul, Matrix.smul_mul, bilinear_smul, bilinear_rankOne,
    bilinear_symmetric (inverse_symmetric (laplacian_symmetric a h)) (a f) (a e)]
  unfold responseSquare
  ring

lemma hasDerivAt_marginal_segment (a : ι → n → ℝ) (h k : ι → ℝ) (e : ι) (t : ℝ)
    (hL : IsUnit (laplacian a (segmentField h k t))) :
    HasDerivAt (fun s => marginal a (segmentField h k s) e)
      (∑ f, response a (segmentField h k t) e f * (k f - h f)) t := by
  let H := segmentField h k t
  let D := ∑ f, (Real.exp (H f) * (k f - h f)) • Matrix.vecMulVec (a f) (a f)
  have hB := hasDerivAt_bilinear_inverse_curve
    (fun s => laplacian a (segmentField h k s)) D t
    (hasDerivAt_laplacian_segment a h k t) hL (a e) (a e)
  have hprod := (hasDerivAt_segmentField_apply h k e t).exp.mul hB
  have hv : (Real.exp (H e) * (k e - h e)) * bilinear (laplacian a H)⁻¹ (a e) (a e) +
      Real.exp (H e) * -bilinear ((laplacian a H)⁻¹ * D * (laplacian a H)⁻¹) (a e) (a e) =
      ∑ f, response a H e f * (k f - h f) := by
    rw [mul_neg]
    change (Real.exp (H e) * (k e - h e)) * bilinear (laplacian a H)⁻¹ (a e) (a e) +
      -(Real.exp (H e) * bilinear ((laplacian a H)⁻¹ *
        (∑ f, (Real.exp (H f) * (k f - h f)) • Matrix.vecMulVec (a f) (a f)) *
          (laplacian a H)⁻¹) (a e) (a e)) = _
    rw [bilinear_laplacian_direction]
    simp only [response, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    unfold marginal
    ring
  change HasDerivAt (fun s => marginal a (segmentField h k s) e)
    (∑ f, response a H e f * (k f - h f)) t
  rw [← hv]
  exact hprod

lemma marginal_sub_le_half (a : ι → n → ℝ) (h k : ι → ℝ) (e : ι)
    (D : ℝ) (hD : 0 ≤ D) (hdir : ∀ f, |k f - h f| ≤ D)
    (hL : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (laplacian a (segmentField h k t))) :
    |marginal a k e - marginal a h e| ≤ (1 : ℝ) / 2 * D := by
  apply response_le_of_line_derivative Finset.univ (fun H => marginal a H e)
    (fun H f => response a H e f) h k (1 / 2) D hD
  · intro f hf
    exact hdir f
  · intro t ht
    exact hasDerivAt_marginal_segment a h k e t (hL t ht)
  · intro t ht
    rw [sum_abs_response a _ (hL t ⟨ht.1, ht.2.le⟩) e]
    nlinarith [sq_nonneg (marginal a (segmentField h k t) e - 1 / 2)]

end Problem336.TransferCurrent

end

end OAI
