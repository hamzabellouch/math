import Mathlib

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Filter Set Matrix Unitary
open scoped Topology ContDiff
namespace YauCounterexamples

lemma second_deriv_nonpos_of_localMax {f : ℝ → ℝ} {x : ℝ}
    (hf : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra h
  have hp : 0 < deriv (deriv f) x := lt_of_not_ge h
  have hmin := isLocalMin_of_deriv_deriv_pos hp hf.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [hf, hmin] with y hy hy'
    exact le_antisymm hy hy'
  have hz : deriv (deriv f) x = 0 := by
    simpa only [deriv_const', deriv_const] using he.deriv.deriv_eq
  linarith

lemma matrix_contraction_nonpos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (H : Matrix ι ι ℝ)
    (hH : ∀ v : ι → ℝ, ∑ i, ∑ j, H i j * v i * v j ≤ 0) :
    ∑ i, ∑ j, A i j * H i j ≤ 0 := by
  let U : Matrix ι ι ℝ := hA.isHermitian.eigenvectorUnitary
  have hspec (i j : ι) : A i j =
      ∑ k, hA.isHermitian.eigenvalues k * U i k * U j k := by
    conv_lhs => rw [hA.isHermitian.spectral_theorem]
    rw [conjStarAlgAut_apply, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.star_apply, star_trivial]
    change (∑ k, U i k * hA.isHermitian.eigenvalues k * U j k) = _
    apply Finset.sum_congr rfl
    intro k _
    dsimp [U]
    ring
  simp_rw [hspec, Finset.sum_mul]
  calc
    _ = ∑ i, ∑ k, ∑ j, hA.isHermitian.eigenvalues k * U i k * U j k * H i j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, hA.isHermitian.eigenvalues k * U i k * U j k * H i j :=
      Finset.sum_comm
    _ = ∑ k, hA.isHermitian.eigenvalues k *
        (∑ i, ∑ j, H i j * U i k * U j k) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ 0 := Finset.sum_nonpos fun k _ =>
      mul_nonpos_of_nonneg_of_nonpos (hA.eigenvalues_nonneg k) (hH (fun i => U i k))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma second_fderiv_diag_nonpos {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hm : IsLocalMax f x) (v : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x v ≤ 0 := by
  let line : ℝ → E := fun t => x + t • v
  have hl (t : ℝ) : HasDerivAt line v t := by
    simpa [line] using (hasDerivAt_id t).smul_const v |>.const_add x
  have h0 : line 0 = x := by simp [line]
  have hf' : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have he : (fun t => deriv (f ∘ line) t) =ᶠ[𝓝 0]
      fun t => fderiv ℝ f (line t) v := by
    have hfd := hf.eventually (by norm_num)
    have hline : Tendsto line (𝓝 0) (𝓝 x) := by
      have hc := (hl 0).continuousAt
      rwa [ContinuousAt, h0] at hc
    filter_upwards [hline.eventually hfd] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hl t)).deriv
  have h2 : deriv (deriv (f ∘ line)) 0 =
      fderiv ℝ (fun y => fderiv ℝ f y v) x v := by
    rw [he.deriv_eq]
    have hd : HasFDerivAt (fun y => fderiv ℝ f y v)
        (fderiv ℝ (fun y => fderiv ℝ f y v) x) (line 0) := by
      rw [h0]
      exact (hf'.clm_apply (differentiableAt_const v)).hasFDerivAt
    exact (hd.comp_hasDerivAt 0 (hl 0)).deriv
  rw [← h2]
  apply second_deriv_nonpos_of_localMax
  · have hm' : IsLocalMax f (line 0) := by simpa [line] using hm
    exact hm'.comp_continuous (hl 0).continuousAt
  · have hc : ContinuousAt f (line 0) := by rw [h0]; exact hf.continuousAt
    exact hc.comp (hl 0).continuousAt

lemma localMax_hessian_contraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hm : IsLocalMax f x)
    (b : ι → E) {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    ∑ i, ∑ j, A i j * fderiv ℝ (fun y => fderiv ℝ f y (b j)) x (b i) ≤ 0 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  apply matrix_contraction_nonpos hA
  intro v
  have hq := second_fderiv_diag_nonpos hf hm (∑ i, v i • b i)
  simp only [fderiv_clm_apply hd (differentiableAt_const _), fderiv_const_apply,
    ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply] at hq ⊢
  convert hq using 1
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end YauCounterexamples

end

end OAI
