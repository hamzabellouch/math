import Mathlib
import OAI.Analysis.AffineBernstein.TensorFlux

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [CompleteSpace E] [DecidableEq ι] in
lemma orthonormal_bilinear_trace (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E)
    (A : E →L[ℝ] E →L[ℝ] ℝ) : (∑ i, A (b i) (b i)) = ∑ j, A (c j) (c j) := by
  have hi (i : ι) : A (b i) (b i) = ∑ j, ∑ k,
      inner ℝ (c j) (b i) * inner ℝ (c k) (b i) * A (c j) (c k) := by
    conv_lhs => rw [← c.sum_repr' (b i)]
    simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    ext j
    congr 1
    ext k
    ring
  simp_rw [hi]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  have hinner (k : κ) : (∑ i, inner ℝ (c j) (b i) * inner ℝ (c k) (b i)) =
      if j = k then 1 else 0 := by
    simpa only [real_inner_comm (c k),c.inner_eq_ite,eq_comm] using b.sum_inner_mul_inner (c j) (c k)
  simp_rw [← Finset.sum_mul,hinner]
  simp

omit [DecidableEq ι] in
lemma roundHessianContraction_basis (b : OrthonormalBasis ι ℝ E)
    (c : OrthonormalBasis κ ℝ E) (T : E → E →L[ℝ] E →L[ℝ] ℝ) (g : E → ℝ) (e : E) :
    roundHessianContraction b T g e = roundHessianContraction c T g e := by
  let P := tangentProjectionCLM e
  let L := (P.comp (fderiv ℝ (gradient g) e)).comp P - inner ℝ e (gradient g e) • P
  exact orthonormal_bilinear_trace b c ((T e).bilinearComp P L)

omit [CompleteSpace E] in
lemma tangentProjection_adapted (c : OrthonormalBasis (ι ⊕ Unit) ℝ E) (i : ι) :
    tangentProjection (c (Sum.inr ())) (c (Sum.inl i)) = c (Sum.inl i) := by
  apply tangentProjection_eq
  simp [c.inner_eq_ite]

lemma tangentProjection_gradient_component (c : OrthonormalBasis (ι ⊕ Unit) ℝ E)
    (f : E → ℝ) (i : ι) :
    inner ℝ (c (Sum.inl i)) (tangentProjection (c (Sum.inr ())) (gradient f (c (Sum.inr ())))) =
      fderiv ℝ f (c (Sum.inr ())) (c (Sum.inl i)) := by
  simp [tangentProjection,inner_sub_right,real_inner_smul_right,c.inner_eq_ite]

omit [CompleteSpace E] [DecidableEq ι] in
lemma tangent_vector_expansion (c : OrthonormalBasis (ι ⊕ Unit) ℝ E) {v : E}
    (hv : inner ℝ (c (Sum.inr ())) v = 0) :
    v = ∑ i, inner ℝ (c (Sum.inl i)) v • c (Sum.inl i) := by
  have hh := c.sum_repr' v
  simpa [Fintype.sum_sum_type,hv] using hh.symm

lemma roundTensorPair_adapted (c : OrthonormalBasis (ι ⊕ Unit) ℝ E)
    (T : E →L[ℝ] E →L[ℝ] ℝ) (f g : E → ℝ) :
    T (tangentProjection (c (Sum.inr ())) (gradient f (c (Sum.inr ()))))
      (tangentProjection (c (Sum.inr ())) (gradient g (c (Sum.inr ())))) =
      ∑ j, ∑ i, T (c (Sum.inl j)) (c (Sum.inl i)) *
        fderiv ℝ f (c (Sum.inr ())) (c (Sum.inl j)) *
        fderiv ℝ g (c (Sum.inr ())) (c (Sum.inl i)) := by
  have hu : inner ℝ (c (Sum.inr ())) (c (Sum.inr ())) = 1 := by simp
  have hex (f : E → ℝ) : tangentProjection (c (Sum.inr ())) (gradient f (c (Sum.inr ()))) =
      ∑ i, fderiv ℝ f (c (Sum.inr ())) (c (Sum.inl i)) • c (Sum.inl i) := by
    simpa only [tangentProjection_gradient_component] using
      tangent_vector_expansion c (inner_tangentProjection_unit hu (gradient f (c (Sum.inr ()))))
  rw [hex f,hex g]
  simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma roundHessianContraction_adapted (c : OrthonormalBasis (ι ⊕ Unit) ℝ E)
    (T : E → E →L[ℝ] E →L[ℝ] ℝ) {g : E → ℝ}
    (hg : ContDiffAt ℝ ∞ g (c (Sum.inr ()))) :
    roundHessianContraction c T g (c (Sum.inr ())) =
      ∑ j, ∑ i, T (c (Sum.inr ())) (c (Sum.inl j)) (c (Sum.inl i)) *
        (fderiv ℝ (fderiv ℝ g) (c (Sum.inr ())) (c (Sum.inl j)) (c (Sum.inl i)) -
          fderiv ℝ g (c (Sum.inr ())) (c (Sum.inr ())) * (if i = j then 1 else 0)) := by
  have hu : inner ℝ (c (Sum.inr ())) (c (Sum.inr ())) = 1 := by simp
  simp only [roundHessianContraction,Fintype.sum_sum_type,Finset.univ_unique,
    Finset.sum_singleton,tangentProjection_adapted,tangentProjection_self_unit hu,
    map_zero,smul_zero,sub_zero,zero_apply,add_zero]
  apply Finset.sum_congr rfl
  intro j _
  let w := tangentProjection (c (Sum.inr ()))
      (fderiv ℝ (gradient g) (c (Sum.inr ())) (c (Sum.inl j))) -
        inner ℝ (c (Sum.inr ())) (gradient g (c (Sum.inr ()))) • c (Sum.inl j)
  have hw : inner ℝ (c (Sum.inr ())) w = 0 := by
    simp [w,inner_sub_right,real_inner_smul_right,inner_tangentProjection_unit hu,c.inner_eq_ite]
  change T _ _ w = _
  rw [tangent_vector_expansion c hw]
  simp only [map_sum,map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hi : inner ℝ (c (Sum.inl i)) w =
      fderiv ℝ (fderiv ℝ g) (c (Sum.inr ())) (c (Sum.inl j)) (c (Sum.inl i)) -
        fderiv ℝ g (c (Sum.inr ())) (c (Sum.inr ())) * (if i = j then 1 else 0) := by
    simp only [w,tangentProjection,inner_sub_right,real_inner_smul_right,c.inner_eq_ite,
      Sum.inl_ne_inr,ite_false,mul_zero,sub_zero,
      Sum.inl.injEq,inner_gradient_right]
    rw [real_inner_comm (fderiv ℝ (gradient g) (c (Sum.inr ())) (c (Sum.inl j))),
      inner_fderiv_gradient hg]
    simp
  rw [hi]
  ring

end AffineBernstein
end

end OAI
