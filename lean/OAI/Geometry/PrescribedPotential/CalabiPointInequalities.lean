import Mathlib
import OAI.Geometry.PrescribedPotential.CalabiBochner
import OAI.Geometry.PrescribedPotential.CalabiResidualBound

namespace OAI

/-! Calabi Point Inequalities. -/

section

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus.LocalKaehlerField
variable {n : ℕ} (K : LocalKaehlerField n)

def calabiGood (z : V n) : ℝ :=
  (∑ k, tensorSquare (fun i => K.covHol K.connection k i z)) +
    ∑ k, tensorSquare (fun i => K.curvature k i z)

lemma calabiGood_nonneg (z : V n) : 0 ≤ K.calabiGood z :=
  add_nonneg (Finset.sum_nonneg (fun _ _ => tensorSquare_nonneg _))
    (Finset.sum_nonneg (fun _ _ => tensorSquare_nonneg _))

lemma calabiNorm_at_one {z : V n} (hM : K.matrix z = 1) :
    K.calabiNorm z = tensorSquare (fun i => K.connection i z) := by
  simp only [calabiNorm,tensorPair,hM,inv_one,tensorSquare]

lemma calabi_bochner_real_at_one {z : V n} (hz : z ∈ K.domain) (hM : K.matrix z = 1) :
    (PotentialKaehler.potentialMatrix K.calabiNorm z).trace.re = K.calabiGood z +
      calabiResidual (K.ricciHessian z) (fun i => mderiv (-Complex.I) (e i) K.ricciHessian z)
        (fun i => K.connection i z) := by
  rw [K.calabi_bochner_at_one hz hM]
  have he : (fun i => mderiv (-Complex.I) (e i) K.ricciHessian z -
      K.connection i z*K.ricciHessian z - ∑ q, K.ricciHessian z q i • K.connection q z) =
      (fun i => mderiv (-Complex.I) (e i) K.ricciHessian z) -
        ricciRight (K.ricciHessian z) (fun i => K.connection i z) := by
    funext i
    exact (sub_add_eq_sub_sub _ _ _).symm
  rw [he]
  simp only [Complex.add_re,Complex.re_sum,calabiGood,tensorSquare,calabiResidual,Complex.add_re]
  exact add_assoc _ _ _

lemma calabi_gradient_at_one {z : V n} (hz : z ∈ K.domain) (hM : K.matrix z = 1) (k : Fin n) :
    ‖dz (e k) (fun y => (K.calabiNorm y : ℂ)) z‖^2 ≤ 2*K.calabiNorm z *
      (tensorSquare (fun i => K.covHol K.connection k i z)+tensorSquare (fun i => K.curvature k i z)) := by
  have he : (fun y => (K.calabiNorm y : ℂ)) =ᶠ[𝓝 z] K.tensorPair K.connection K.connection := by
    filter_upwards [K.isOpen.mem_nhds hz] with y hy using K.calabiNorm_complex hy
  have hd : dz (e k) (fun y => (K.calabiNorm y : ℂ)) z =
      tensorPairAt 1 1 (fun i => K.covHol K.connection k i z) (fun i => K.connection i z) +
      tensorPairAt 1 1 (fun i => K.connection i z) (fun i => K.curvature k i z) := by
    change wderiv (-Complex.I) (e k) _ z = _
    rw [wderiv_congr he]
    change dz (e k) (K.tensorPair K.connection K.connection) z = _
    rw [K.tensorPair_hol (T := K.connection) (U := K.connection) K.connection_smooth K.connection_smooth hz]
    simp only [tensorPair,hM,inv_one]
    rfl
  rw [hd,K.calabiNorm_at_one hM]
  have h1 := tensorPairAt_cauchy (fun i => K.covHol K.connection k i z) (fun i => K.connection i z)
  have h2 := tensorPairAt_cauchy (fun i => K.connection i z) (fun i => K.curvature k i z)
  have hh := norm_add_le
    (tensorPairAt 1 1 (fun i => K.covHol K.connection k i z) (fun i => K.connection i z))
    (tensorPairAt 1 1 (fun i => K.connection i z) (fun i => K.curvature k i z))
  have hs := sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr hh
  nlinarith [sq_nonneg (‖tensorPairAt 1 1 (fun i => K.covHol K.connection k i z) (fun i => K.connection i z)‖-
    ‖tensorPairAt 1 1 (fun i => K.connection i z) (fun i => K.curvature k i z)‖)]

lemma calabi_gradient_sum_at_one {z : V n} (hz : z ∈ K.domain) (hM : K.matrix z = 1) :
    (∑ k, ‖dz (e k) (fun y => (K.calabiNorm y : ℂ)) z‖^2) ≤ 2*K.calabiNorm z*K.calabiGood z := by
  calc
    _ ≤ ∑ k, 2*K.calabiNorm z*(tensorSquare (fun i => K.covHol K.connection k i z)+
      tensorSquare (fun i => K.curvature k i z)) := Finset.sum_le_sum (fun k _ => K.calabi_gradient_at_one hz hM k)
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_add_distrib]; rfl
end KaehlerCalculus.LocalKaehlerField

end
end

end OAI
