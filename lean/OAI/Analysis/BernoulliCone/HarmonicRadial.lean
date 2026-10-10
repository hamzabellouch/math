import OAI.Analysis.BernoulliCone.StationarityIntegrability

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff BigOperators
namespace Bernoulli
open scoped _root_.Bernoulli
namespace HarmonicKernel
variable {d : ℕ}

lemma radial_hasFDerivAt {f : ℝ → ℝ} (hf : Differentiable ℝ f) (x : Space d) :
    HasFDerivAt (fun y : Space d => f (‖y‖^2))
      (deriv f (‖x‖^2) • (2 • innerSL ℝ x)) x := by
  exact (hf (‖x‖^2)).hasDerivAt.comp_hasFDerivAt x
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt

lemma radial_directional {f : ℝ → ℝ} (hf : Differentiable ℝ f) (x e : Space d) :
    fderiv ℝ (fun y : Space d => f (‖y‖^2)) x e =
      2 * deriv f (‖x‖^2) * inner ℝ x e := by
  rw [(radial_hasFDerivAt hf x).fderiv]
  simp only [smul_apply,smul_eq_mul,innerSL_apply_apply]
  ring

lemma radial_second_directional {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (x e : Space d) :
    fderiv ℝ (fun y : Space d =>
      fderiv ℝ (fun z : Space d => f (‖z‖^2)) y e) x e =
      4 * deriv (deriv f) (‖x‖^2) * (inner ℝ x e)^2 +
        2 * deriv f (‖x‖^2) * ‖e‖^2 := by
  have hd := hf.differentiable (by simp)
  have hd' := (contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp)
  simp_rw [radial_directional hd]
  have hi : HasFDerivAt (fun y : Space d => inner ℝ y e) (innerSL ℝ e) x := by
    convert (innerSL ℝ e).hasFDerivAt (x := x) using 1
    ext y
    simp only [innerSL_apply_apply,real_inner_comm]
  have ht := ((radial_hasFDerivAt hd' x).const_mul 2).mul hi
  change HasFDerivAt (fun y => 2 * deriv f (‖y‖^2) * inner ℝ y e) _ x at ht
  rw [ht.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,innerSL_apply_apply,
    real_inner_self_eq_norm_sq]
  ring

/-- The full Euclidean radial Laplacian; no polar-coordinate convention is
hidden in this formula. It is used to build compact harmonic averaging kernels. -/
lemma radial_laplacian {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (x : Space d) :
    Laplacian.laplacian (fun y : Space d => f (‖y‖^2)) x =
      4 * deriv (deriv f) (‖x‖^2) * ‖x‖^2 + 2 * d * deriv f (‖x‖^2) := by
  let b := stdOrthonormalBasis ℝ (Space d)
  have hq : ContDiff ℝ ∞ (fun y : Space d => f (‖y‖^2)) :=
    hf.comp (contDiff_id.norm_sq ℝ)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  have he (e : Space d) :
      iteratedFDeriv ℝ 2 (fun y : Space d => f (‖y‖^2)) x ![e,e] =
        4 * deriv (deriv f) (‖x‖^2) * (inner ℝ x e)^2 +
          2 * deriv f (‖x‖^2) * ‖e‖^2 := by
    rw [iteratedFDeriv_two_apply]
    have hd := (hq.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
    have hh := fderiv_clm_apply hd (differentiableAt_const e)
    have ht := radial_second_directional hf x e
    rw [hh] at ht
    simpa using ht
  simp_rw [he,b.norm_eq_one,one_pow,mul_one]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  have hs : ∑ i, (inner ℝ x (b i))^2 = ‖x‖^2 := by
    have hs' := b.sum_inner_mul_inner x x
    simpa only [real_inner_comm x,sq,real_inner_self_eq_norm_sq] using hs'
  rw [hs]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    finrank_euclideanSpace, nsmul_eq_mul]
  ring
end HarmonicKernel
end Bernoulli

end
end

end OAI
