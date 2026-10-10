import Mathlib
import OAI.Analysis.AffineBernstein.AngularCalculus

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma fderiv_bilinear_field {T : E → E →L[ℝ] E →L[ℝ] ℝ} {u v : E → E} {x : E}
    (hT : DifferentiableAt ℝ T x) (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) (z : E) :
    fderiv ℝ (fun q => T q (u q) (v q)) x z =
      fderiv ℝ T x z (u x) (v x) + T x (fderiv ℝ u x z) (v x) +
        T x (u x) (fderiv ℝ v x z) := by
  rw [((hT.hasFDerivAt.clm_apply hu.hasFDerivAt).clm_apply hv.hasFDerivAt).fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  ring

/- Derivatives of the radial eigenspace remain radial in the radial direction.
The polynomial identity avoids differentiating an arbitrarily chosen eigenvalue. -/
lemma radial_tensor_derivative {T : E → E →L[ℝ] E →L[ℝ] ℝ} {e v : E}
    (hT : DifferentiableAt ℝ T e) (he : inner ℝ e e = 1) (hv : inner ℝ e v = 0)
    (hr : ∀ᶠ q in 𝓝 e, T q q v * inner ℝ q q = T q q q * inner ℝ q v) :
    fderiv ℝ T e e e v = 0 := by
  have hv0 : T e e v = 0 := by
    have hh := hr.self_of_nhds
    simpa only [he, hv, mul_one, mul_zero] using hh
  have h1 : DifferentiableAt ℝ (fun q => T q q v) e :=
    (hT.clm_apply differentiableAt_id).clm_apply (differentiableAt_const v)
  have h2 : DifferentiableAt ℝ (fun q => T q q q) e :=
    (hT.clm_apply differentiableAt_id).clm_apply differentiableAt_id
  have hn : DifferentiableAt ℝ (fun q : E => inner ℝ q q) e :=
    differentiableAt_id.inner ℝ differentiableAt_id
  have hvd : DifferentiableAt ℝ (fun q : E => inner ℝ q v) e :=
    differentiableAt_id.inner ℝ (differentiableAt_const v)
  have heq : (fun q => T q q v * inner ℝ q q) =ᶠ[𝓝 e]
      (fun q => T q q q * inner ℝ q v) := hr
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L e) heq.fderiv_eq
  have hd1 := (h1.hasFDerivAt.mul hn.hasFDerivAt).fderiv
  have hd2 := (h2.hasFDerivAt.mul hvd.hasFDerivAt).fderiv
  simp only [Pi.mul_def] at hd1 hd2
  rw [hd1, hd2] at hh
  simp only [add_apply, smul_apply, smul_eq_mul, he, hv, hv0, zero_mul,
    add_zero, zero_add] at hh
  have hvd' : fderiv ℝ (fun q : E => inner ℝ q v) e e = 0 := by
    have hG : (fun q : E => inner ℝ q v) = InnerProductSpace.toDual ℝ E v := by
      ext q; simp [real_inner_comm]
    rw [hG, (InnerProductSpace.toDual ℝ E v).fderiv]
    simpa only [InnerProductSpace.toDual_apply_apply, real_inner_comm] using hv
  rw [hvd', mul_zero] at hh
  have hdf := fderiv_bilinear_field hT differentiableAt_id (differentiableAt_const v) e
  simp only [id_eq, fderiv_id, ContinuousLinearMap.id_apply, fderiv_const_apply, zero_apply,
    hv0, map_zero, add_zero] at hdf
  rw [hdf] at hh
  simpa only [one_mul] using hh

lemma roundTensorDerivative_eq_of_radial {T : E → E →L[ℝ] E →L[ℝ] ℝ} {e : E}
    (hT : DifferentiableAt ℝ T e) (u v w : E)
    (hv : inner ℝ e v = 0) (hw : inner ℝ e w = 0)
    (hrv : T e v e = 0) (hrw : T e e w = 0) :
    roundTensorDerivative T e u v w = fderiv ℝ T e u v w := by
  unfold roundTensorDerivative
  rw [fderiv_bilinear_field hT (hasFDerivAt_tangentProjection e v).differentiableAt
    (hasFDerivAt_tangentProjection e w).differentiableAt,
    (hasFDerivAt_tangentProjection e v).fderiv,
    (hasFDerivAt_tangentProjection e w).fderiv]
  simp only [tangentProjection_eq hv, tangentProjection_eq hw,
    neg_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    InnerProductSpace.toDual_apply_apply,
    hv, hw, zero_smul, zero_add, map_neg, map_smul, smul_eq_mul,
    hrv, hrw, mul_zero, neg_zero, add_zero]

variable {ι : Type*} [Fintype ι]

omit [CompleteSpace E] in
lemma trace_projected_bilinear (b : OrthonormalBasis ι ℝ E)
    (A : E →L[ℝ] E →L[ℝ] ℝ) (e : E) (he : inner ℝ e e = 1) :
    (∑ i, A (tangentProjection e (b i)) (tangentProjection e (b i))) =
      (∑ i, A (b i) (b i)) - A e e := by
  simp only [tangentProjection, map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul,
    Finset.sum_sub_distrib, mul_sub]
  have hone : (∑ i, inner ℝ e (b i) • b i) = e := by
    simpa only [real_inner_comm e] using b.sum_repr' e
  have h1 : (∑ i, inner ℝ e (b i) * A (b i) e) = A e e := by
    have hh := congrArg (fun z => A z e) hone
    simpa only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul] using hh
  have h2 : (∑ i, inner ℝ e (b i) * A e (b i)) = A e e := by
    have hh := congrArg (A e) hone
    simpa only [map_sum, map_smul, smul_eq_mul] using hh
  have h3 : (∑ i, inner ℝ e (b i) * (inner ℝ e (b i) * A e e)) = A e e := by
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    have hh : (∑ i, inner ℝ e (b i) * inner ℝ e (b i)) = 1 := by
      simpa only [real_inner_comm e] using (b.sum_inner_mul_inner e e).trans he
    rw [hh, one_mul]
  rw [h1, h2, h3]
  ring

/- Tangential divergence of the restricted Newton tensor. Both normal
corrections vanish by genuine radial invariance, not as an IBP assumption. -/
theorem projected_tensor_divergence (b : OrthonormalBasis ι ℝ E)
    {T : E → E →L[ℝ] E →L[ℝ] ℝ} {e v : E}
    (hT : DifferentiableAt ℝ T e) (he : inner ℝ e e = 1) (hv : inner ℝ e v = 0)
    (hs : ∀ u w, T e u w = T e w u)
    (hr : ∀ᶠ q in 𝓝 e, ∀ w, T q q w * inner ℝ q q = T q q q * inner ℝ q w)
    (hdiv : ∀ w, (∑ i, fderiv ℝ T e (b i) (b i) w) = 0) :
    (∑ i, roundTensorDerivative T e (tangentProjection e (b i))
      (tangentProjection e (b i)) v) = 0 := by
  have hrv : T e e v = 0 := by
    have hh := hr.self_of_nhds v
    simpa only [he, hv, mul_one, mul_zero] using hh
  have hp (i : ι) : inner ℝ e (tangentProjection e (b i)) = 0 := by
    simp only [tangentProjection, inner_sub_right, real_inner_smul_right, he, mul_one, sub_self]
  have hrp (i : ι) : T e (tangentProjection e (b i)) e = 0 := by
    rw [hs]
    have hh := hr.self_of_nhds (tangentProjection e (b i))
    simpa only [he, hp, mul_one, mul_zero] using hh
  simp_rw [roundTensorDerivative_eq_of_radial hT _ _ _ (hp _) hv (hrp _) hrv]
  let A : E →L[ℝ] E →L[ℝ] ℝ := (ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) ℝ
    (ContinuousLinearMap.apply ℝ ℝ v)).comp (fderiv ℝ T e)
  have htrace : (∑ i, fderiv ℝ T e (tangentProjection e (b i))
      (tangentProjection e (b i)) v) =
      (∑ i, fderiv ℝ T e (b i) (b i) v) - fderiv ℝ T e e e v := by
    exact trace_projected_bilinear b A e he
  rw [htrace, hdiv, radial_tensor_derivative hT he hv (hr.mono fun q hq => hq v), sub_zero]

end AffineBernstein
end

end OAI
