import Mathlib
import OAI.Geometry.PrescribedPotential.MatrixWirtinger

namespace OAI

/-! Inverse Trace Calculus. -/

section

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

lemma second_mderiv_inverse_at_one {U : Set (V n)} (hU : IsOpen U)
    {M : V n → Matrix (Fin n) (Fin n) ℂ} (hM : ContDiffOn ℝ ∞ M U)
    (hn : ∀ y ∈ U, (M y).det ≠ 0) {z : V n} (hz : z ∈ U) (hMz : M z = 1)
    (a b : ℂ) (u v : V n) :
    mderiv b u (mderiv a v (fun y => (M y)⁻¹)) z =
      mderiv b u M z*mderiv a v M z + mderiv a v M z*mderiv b u M z -
        mderiv b u (mderiv a v M) z := by
  have hs := hM.contDiffAt (hU.mem_nhds hz)
  have hi := (MatrixSmoothGeneral.inverse hM hn).contDiffAt (hU.mem_nhds hz)
  have hd := mderiv_smooth hs a v
  have he : mderiv a v (fun y => (M y)⁻¹) =ᶠ[𝓝 z]
      (fun y => -(M y)⁻¹*mderiv a v M y*(M y)⁻¹) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    exact mderiv_inverse hU hM hn hy a v
  rw [mderiv_congr he,mderiv_mul (matrix_smooth_mul hi.neg hd) hi,
    mderiv_mul hi.neg hd,mderiv_neg hi,mderiv_inverse hU hM hn hz,hMz]
  simp only [inv_one,neg_mul,one_mul,mul_one,neg_neg]
  noncomm_ring

lemma second_mderiv_mul {M N : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : ContDiffAt ℝ ∞ M z) (hN : ContDiffAt ℝ ∞ N z)
    (a b : ℂ) (u v : V n) :
    mderiv b u (mderiv a v (fun y => M y*N y)) z =
    mderiv b u (mderiv a v M) z*N z + mderiv a v M z*mderiv b u N z +
      mderiv b u M z*mderiv a v N z + M z*mderiv b u (mderiv a v N) z := by
  have he : mderiv a v (fun y => M y*N y) =ᶠ[𝓝 z]
      (fun y => mderiv a v M y*N y+M y*mderiv a v N y) := by
    filter_upwards [(hM.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by decide),
      (hN.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by decide)] with y hyM hyN
    exact mderiv_mul_differentiable (hyM.differentiableAt (by simp))
      (hyN.differentiableAt (by simp)) a v
  rw [mderiv_congr he,mderiv_add (matrix_smooth_mul (mderiv_smooth hM a v) hN)
    (matrix_smooth_mul hM (mderiv_smooth hN a v)),
    mderiv_mul (mderiv_smooth hM a v) hN,mderiv_mul hM (mderiv_smooth hN a v)]
  abel

lemma second_wderiv_trace {M : V n → Matrix (Fin n) (Fin n) ℂ} {z : V n}
    (hM : ContDiffAt ℝ ∞ M z) (a b : ℂ) (u v : V n) :
    wderiv b u (wderiv a v (fun y => (M y).trace)) z =
      (mderiv b u (mderiv a v M) z).trace := by
  have he : wderiv a v (fun y => (M y).trace) =ᶠ[𝓝 z]
      (fun y => (mderiv a v M y).trace) := by
    filter_upwards [(hM.of_le (show (1 : WithTop ℕ∞) ≤ ∞ by simp)).eventually (by decide)] with y hy
    exact mderiv_trace_differentiable (hy.differentiableAt (by simp)) a v
  rw [wderiv_congr he,mderiv_trace (mderiv_smooth hM a v)]

lemma second_wderiv_inverse_trace_at_one {U : Set (V n)} (hU : IsOpen U)
    {M G : V n → Matrix (Fin n) (Fin n) ℂ} (hM : ContDiffOn ℝ ∞ M U)
    (hn : ∀ y ∈ U, (M y).det ≠ 0) {z : V n} (hz : z ∈ U) (hMz : M z = 1)
    (hG : ContDiffAt ℝ ∞ G z) (a b : ℂ) (u v : V n) :
    wderiv b u (wderiv a v (fun y => ((M y)⁻¹*G y).trace)) z =
      ((mderiv b u M z*mderiv a v M z + mderiv a v M z*mderiv b u M z -
        mderiv b u (mderiv a v M) z)*G z -
        mderiv a v M z*mderiv b u G z - mderiv b u M z*mderiv a v G z +
        mderiv b u (mderiv a v G) z).trace := by
  have hi := (MatrixSmoothGeneral.inverse hM hn).contDiffAt (hU.mem_nhds hz)
  rw [second_wderiv_trace (matrix_smooth_mul hi hG),second_mderiv_mul hi hG,
    second_mderiv_inverse_at_one hU hM hn hz hMz,
    mderiv_inverse hU hM hn hz,mderiv_inverse hU hM hn hz,hMz]
  congr 1
  simp only [inv_one,neg_mul,one_mul,mul_one]
  noncomm_ring
end KaehlerCalculus

end
end

end OAI
