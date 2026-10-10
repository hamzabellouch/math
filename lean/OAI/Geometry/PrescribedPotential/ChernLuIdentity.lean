import Mathlib
import OAI.Geometry.PrescribedPotential.InverseTraceCalculus
import OAI.Geometry.PrescribedPotential.KaehlerSecondDerivatives

namespace OAI

/-! Chern Lu Identity. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

lemma sum_ricci_cancellation (A B C Y Z W : Fin n → Matrix (Fin n) (Fin n) ℂ)
    (G H : Matrix (Fin n) (Fin n) ℂ)
    (hc : ∑ k, C k = H + ∑ k, B k*A k) :
    ∑ k, ((B k*A k+A k*B k-C k)*G-A k*Z k-B k*Y k+W k) =
      -(H*G) + ∑ k, (A k*B k*G-A k*Z k-B k*Y k+W k) := by
  simp only [add_mul,sub_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Matrix.sum_mul]
  rw [hc]
  noncomm_ring

lemma inverse_trace_ricci_identity_at_one {U : Set (V n)} (hU : IsOpen U)
    {M G : V n → Matrix (Fin n) (Fin n) ℂ}
    (hM : ContDiffOn ℝ ∞ M U) (hp : ∀ y ∈ U, (M y).PosDef)
    (hclosed : ∀ y ∈ U, ∀ u v w : V n,
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) v w) y u +
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) w u) y v +
      fderiv ℝ (fun q => Anticanonical.ComplexAtlas.fundamentalForm (M q) u v) y w = 0)
    (hG : ContDiffOn ℝ ∞ G U) (hGh : ∀ y ∈ U, (G y).IsHermitian)
    {z : V n} (hz : z ∈ U) (hMz : M z = 1) :
    ∑ k, dzbar (e k) (dz (e k) (fun y => ((M y)⁻¹*G y).trace)) z =
      -(PotentialKaehler.potentialMatrix (fun y => Real.log (M y).det.re) z*G z).trace +
      ∑ k, (mderiv (-Complex.I) (e k) M z*(mderiv (-Complex.I) (e k) M z)ᴴ*G z -
        mderiv (-Complex.I) (e k) M z*(mderiv (-Complex.I) (e k) G z)ᴴ -
        (mderiv (-Complex.I) (e k) M z)ᴴ*mderiv (-Complex.I) (e k) G z +
        mderiv Complex.I (e k) (mderiv (-Complex.I) (e k) G) z).trace := by
  let A := fun k => mderiv (-Complex.I) (e k) M z
  let B := fun k => mderiv Complex.I (e k) M z
  let C := fun k => mderiv Complex.I (e k) (mderiv (-Complex.I) (e k) M) z
  let Y := fun k => mderiv (-Complex.I) (e k) G z
  let Z := fun k => mderiv Complex.I (e k) G z
  let W := fun k => mderiv Complex.I (e k) (mderiv (-Complex.I) (e k) G) z
  let H := PotentialKaehler.potentialMatrix (fun y => Real.log (M y).det.re) z
  have hc : ∑ k, C k = H + ∑ k, B k*A k :=
    ricci_cancellation_at_one hU hM hp hclosed hz hMz
  have hn : ∀ y ∈ U, (M y).det ≠ 0 := fun y hy => ne_of_gt (hp y hy).det_pos
  have hsG := hG.contDiffAt (hU.mem_nhds hz)
  have hfirst : (∑ k, dzbar (e k) (dz (e k) (fun y => ((M y)⁻¹*G y).trace)) z) =
      ∑ k, ((B k*A k+A k*B k-C k)*G z-A k*Z k-B k*Y k+W k).trace := by
    apply Finset.sum_congr rfl
    intro k _
    exact second_wderiv_inverse_trace_at_one hU hM hn hz hMz hsG
      (-Complex.I) Complex.I (e k) (e k)
  have hsecond := congrArg Matrix.trace (sum_ricci_cancellation A B C Y Z W (G z) H hc)
  rw [Matrix.trace_add,Matrix.trace_neg,Matrix.trace_sum,Matrix.trace_sum] at hsecond
  have hlast : (∑ k, (A k*B k*G z-A k*Z k-B k*Y k+W k).trace) =
      ∑ k, (A k*(A k)ᴴ*G z-A k*(Y k)ᴴ-(A k)ᴴ*Y k+W k).trace := by
    apply Finset.sum_congr rfl
    intro k _
    have hb : B k = (A k)ᴴ := mderiv_bar_eq_conjTranspose hU hM
      (fun y hy => (hp y hy).isHermitian) hz (e k)
    have hz' : Z k = (Y k)ᴴ := mderiv_bar_eq_conjTranspose hU hG hGh hz (e k)
    rw [hb,hz']
  exact hfirst.trans (hsecond.trans (congrArg (fun q => -(H*G z).trace+q) hlast))
end KaehlerCalculus

end
end

end OAI
