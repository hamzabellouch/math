import Mathlib
import OAI.Geometry.PrescribedPotential.ChernLuLocalInequality
import OAI.Geometry.PrescribedPotential.LinearFrameCalculus

namespace OAI

/-! Frame Second Calculus. -/

section

 
noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

lemma mderiv_pullMetric_second {U : Set (V n)} (hU : IsOpen U)
    (B : V n →L[ℂ] V n) {M : V n → Matrix (Fin n) (Fin n) ℂ}
    (hM : ContDiffOn ℝ ∞ M U) {z : V n} (hz : B z ∈ U)
    (a b : ℂ) (u v : V n) :
    mderiv a u (mderiv b v (pullMetric B M)) z =
      (frameMatrix B)ᴴ*mderiv a (B u) (mderiv b (B v) M) (B z)*frameMatrix B := by
  have he : mderiv b v (pullMetric B M) =ᶠ[𝓝 z] pullMetric B (mderiv b (B v) M) := by
    filter_upwards [B.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hz)] with y hy
    exact mderiv_pullMetric B (hM.contDiffAt (hU.mem_nhds hy)) b v
  rw [mderiv_congr he,mderiv_pullMetric B (mderiv_smooth (hM.contDiffAt (hU.mem_nhds hz)) b (B v))]

lemma congruence_inverse_cancel (B G Y : Matrix (Fin n) (Fin n) ℂ)
    (hB : IsUnit B) :
    (Bᴴ*Y*B)ᴴ*(Bᴴ*G*B)⁻¹*(Bᴴ*Y*B) = Bᴴ*(Yᴴ*G⁻¹*Y)*B := by
  have hb := (Matrix.isUnit_iff_isUnit_det B).mp hB
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
    Matrix.mul_inv_rev,← Matrix.conjTranspose_nonsing_inv]
  have hc : B*B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hb
  have hd : (B⁻¹)ᴴ*Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul,hc,Matrix.conjTranspose_one]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc B B⁻¹,hc,Matrix.one_mul]
  rw [← Matrix.mul_assoc (B⁻¹)ᴴ Bᴴ,hd,Matrix.one_mul]

lemma curvatureDiagonal_pullMetric {U : Set (V n)} (hU : IsOpen U)
    (B : V n →L[ℂ] V n) (hB : IsUnit (frameMatrix B))
    {M : V n → Matrix (Fin n) (Fin n) ℂ}
    (hM : ContDiffOn ℝ ∞ M U) {z : V n} (hz : B z ∈ U) (v : V n) :
    curvatureDiagonal (pullMetric B M) z v =
      (frameMatrix B)ᴴ*curvatureDiagonal M (B z) (B v)*frameMatrix B := by
  unfold curvatureDiagonal
  rw [mderiv_pullMetric_second hU B hM hz,
    mderiv_pullMetric B (hM.contDiffAt (hU.mem_nhds hz))]
  unfold pullMetric
  rw [congruence_inverse_cancel _ _ _ hB]
  simp only [mul_sub,sub_mul]
end KaehlerCalculus

end
end

end OAI
