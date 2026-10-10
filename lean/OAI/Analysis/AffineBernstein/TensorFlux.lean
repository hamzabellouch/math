import Mathlib
import OAI.Analysis.AffineBernstein.SphereAlgebra
import OAI.Analysis.AffineBernstein.SphereTensorCalculus

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι]

def tangentProjectionCLM (e : E) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (InnerProductSpace.toDual ℝ E e).smulRight e

lemma tangentProjectionCLM_apply (e v : E) : tangentProjectionCLM e v = tangentProjection e v := rfl

omit [CompleteSpace E] in
lemma inner_tangentProjection_unit {e : E} (he : inner ℝ e e = 1) (v : E) :
    inner ℝ e (tangentProjection e v) = 0 := by
  simp only [tangentProjection, inner_sub_right, real_inner_smul_right, he, mul_one, sub_self]

omit [CompleteSpace E] in
lemma tangentProjection_self_unit {e : E} (he : inner ℝ e e = 1) :
    tangentProjection e e = 0 := by simp only [tangentProjection, he, one_smul, sub_self]

omit [CompleteSpace E] in
lemma contDiffAt_projected_field {G : E → E} {e : E} (hG : ContDiffAt ℝ ∞ G e) :
    ContDiffAt ℝ ∞ (fun q => tangentProjection q (G q)) e :=
  hG.sub ((contDiffAt_id.inner ℝ hG).smul contDiffAt_id)

omit [CompleteSpace E] in
lemma fderiv_projected_field {G : E → E} {e : E} (hG : DifferentiableAt ℝ G e) (u : E) :
    fderiv ℝ (fun q => tangentProjection q (G q)) e u =
      tangentProjection e (fderiv ℝ G e u) - inner ℝ u (G e) • e - inner ℝ e (G e) • u := by
  have hd := (hG.hasFDerivAt.sub (((hasFDerivAt_id e).inner ℝ hG.hasFDerivAt).smul
    (hasFDerivAt_id e))).fderiv
  simp only [Pi.sub_def, Pi.smul_def', id_eq] at hd
  change fderiv ℝ (fun q => G q - inner ℝ q (G q) • q) e u = _
  rw [hd]
  simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
    tangentProjection, fderivInnerCLM_apply,
    ContinuousLinearMap.prod_apply, add_smul]
  abel

/- The flux of the angular tensor acting on the projected vector field.
Written in a fixed ambient basis, so no unspecified moving-frame derivatives appear. -/
def tensorFlux (b : OrthonormalBasis ι ℝ E)
    (T : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E) (q : E) : E :=
  ∑ i, T q (tangentProjection q (b i)) (tangentProjection q (G q)) • b i

omit [CompleteSpace E] in
lemma contDiffAt_tensorFlux (b : OrthonormalBasis ι ℝ E)
    {T : E → E →L[ℝ] E →L[ℝ] ℝ} {G : E → E} {e : E}
    (hT : ContDiffAt ℝ ∞ T e) (hG : ContDiffAt ℝ ∞ G e) :
    ContDiffAt ℝ ∞ (tensorFlux b T G) e := by
  apply ContDiffAt.sum
  intro i _
  exact ((hT.clm_apply (contDiffAt_projected_field contDiffAt_const)).clm_apply
    (contDiffAt_projected_field hG)).smul contDiffAt_const

lemma tensorFlux_tangent (b : OrthonormalBasis ι ℝ E)
    (T : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E) {e : E} (he : inner ℝ e e = 1) :
    inner ℝ e (tensorFlux b T G e) = 0 := by
  simp only [tensorFlux, inner_sum, real_inner_smul_right]
  have hb : (∑ i, inner ℝ e (b i) • tangentProjection e (b i)) = 0 := by
    have hh := congrArg (tangentProjectionCLM e) (b.sum_repr' e)
    simp only [map_sum, map_smul, tangentProjectionCLM_apply, tangentProjection_self_unit he] at hh
    simpa only [real_inner_comm e] using hh
  have hh := congrArg (fun v => T e v (tangentProjection e (G e))) hb
  simpa only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, map_zero, zero_apply,
    mul_comm] using hh

lemma fderiv_tensorFlux_scalar (b : OrthonormalBasis ι ℝ E)
    (T : E → E →L[ℝ] E →L[ℝ] ℝ) (g f : E → ℝ) (e : E) :
    fderiv ℝ f e (tensorFlux b T (gradient g) e) =
      T e (tangentProjection e (gradient f e)) (tangentProjection e (gradient g e)) := by
  simp only [tensorFlux, map_sum, map_smul, smul_eq_mul]
  have hh := congrArg (fun v => T e (tangentProjectionCLM e v)
    (tangentProjection e (gradient g e))) (b.sum_repr' (gradient f e))
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul,
    tangentProjectionCLM_apply] at hh
  simpa only [real_inner_comm (gradient f e), inner_gradient_left, mul_comm] using hh

omit [CompleteSpace E] in
lemma fderiv_basis_combination (b : OrthonormalBasis ι ℝ E) {F : ι → E → ℝ}
    {e : E} (hF : ∀ i, DifferentiableAt ℝ (F i) e) (v : E) :
    fderiv ℝ (fun q => ∑ i, F i q • b i) e v = ∑ i, fderiv ℝ (F i) e v • b i := by
  have hd : HasFDerivAt (fun q => ∑ i, F i q • b i)
      (∑ i, (fderiv ℝ (F i) e).smulRight (b i)) e := by
    apply HasFDerivAt.fun_sum
    intro i _
    exact (hF i).hasFDerivAt.smul_const (b i)
  rw [hd.fderiv]
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply]

variable [DecidableEq ι]

omit [CompleteSpace E] in
lemma roundDivergence_basis_combination (b : OrthonormalBasis ι ℝ E) {F : ι → E → ℝ}
    {e : E} (hF : ∀ i, DifferentiableAt ℝ (F i) e) :
    roundDivergence b (fun q => ∑ i, F i q • b i) e =
      ∑ i, fderiv ℝ (F i) e (tangentProjection e (b i)) := by
  simp only [roundDivergence, tangentProjection, fderiv_basis_combination b hF,
    inner_sum, real_inner_smul_right, orthonormal_iff_ite.mp b.orthonormal,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/- Intrinsic round Hessian contraction, formed from ambient derivatives and
orthogonal projection. It is independent of the extension off the sphere. -/
def roundHessianContraction (b : OrthonormalBasis ι ℝ E)
    (T : E → E →L[ℝ] E →L[ℝ] ℝ) (g : E → ℝ) (e : E) : ℝ :=
  ∑ i, T e (tangentProjection e (b i))
    (tangentProjection e (fderiv ℝ (gradient g) e (tangentProjection e (b i))) -
      inner ℝ e (gradient g e) • tangentProjection e (b i))

lemma roundDivergence_tensorFlux (b : OrthonormalBasis ι ℝ E)
    {T : E → E →L[ℝ] E →L[ℝ] ℝ} {G : E → E} {e : E}
    (hT : DifferentiableAt ℝ T e) (hG : DifferentiableAt ℝ G e)
    (he : inner ℝ e e = 1)
    (hr : ∀ v, inner ℝ e v = 0 → T e e v = 0 ∧ T e v e = 0)
    (hdiv : ∀ v, inner ℝ e v = 0 → (∑ i,
      roundTensorDerivative T e (tangentProjection e (b i)) (tangentProjection e (b i)) v) = 0) :
    roundDivergence b (tensorFlux b T G) e =
      ∑ i, T e (tangentProjection e (b i))
        (tangentProjection e (fderiv ℝ G e (tangentProjection e (b i))) -
          inner ℝ e (G e) • tangentProjection e (b i)) := by
  let p : ι → E := fun i => tangentProjection e (b i)
  let v : E := tangentProjection e (G e)
  have hp (i : ι) : inner ℝ e (p i) = 0 := inner_tangentProjection_unit he _
  have hv : inner ℝ e v = 0 := inner_tangentProjection_unit he _
  have hP : DifferentiableAt ℝ (fun q => tangentProjection q (G q)) e :=
    hG.sub ((differentiableAt_id.inner ℝ hG).smul differentiableAt_id)
  unfold tensorFlux
  rw [roundDivergence_basis_combination b (fun i =>
    (hT.clm_apply (hasFDerivAt_tangentProjection e (b i)).differentiableAt).clm_apply hP)]
  have hi (i : ι) :
      fderiv ℝ (fun q => T q (tangentProjection q (b i)) (tangentProjection q (G q))) e (p i) =
        roundTensorDerivative T e (p i) (p i) v - inner ℝ e (b i) * T e (p i) v +
          T e (p i) (tangentProjection e (fderiv ℝ G e (p i)) - inner ℝ e (G e) • p i) := by
    rw [fderiv_bilinear_field hT (hasFDerivAt_tangentProjection e (b i)).differentiableAt hP,
      (hasFDerivAt_tangentProjection e (b i)).fderiv, fderiv_projected_field hG,
      roundTensorDerivative_eq_of_radial hT _ _ _ (hp i) hv (hr _ (hp i)).2 (hr _ hv).1]
    simp only [neg_apply, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply, InnerProductSpace.toDual_apply_apply,
      map_neg, map_add, map_sub, map_smul, smul_eq_mul]
    dsimp only [p, v] at *
    simp only [(hr _ hv).1, (hr _ (hp i)).2, mul_zero, sub_zero, add_zero]
    ring
  change (∑ i, fderiv ℝ (fun q => T q (tangentProjection q (b i))
    (tangentProjection q (G q))) e (p i)) = _
  simp_rw [hi, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hdiv v hv]
  have hz : (∑ i, inner ℝ e (b i) * T e (p i) v) = 0 := by
    have hb := congrArg (tangentProjectionCLM e) (b.sum_repr' e)
    simp only [map_sum, map_smul, tangentProjectionCLM_apply, tangentProjection_self_unit he] at hb
    have hb' : (∑ i, inner ℝ e (b i) • p i) = 0 := by
      simpa only [real_inner_comm e] using hb
    have hh := congrArg (fun z => T e z v) hb'
    simpa only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, map_zero, zero_apply] using hh
  rw [hz, sub_self, zero_add]

end AffineBernstein
end

end OAI
