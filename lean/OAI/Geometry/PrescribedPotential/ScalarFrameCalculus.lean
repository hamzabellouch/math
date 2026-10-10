import Mathlib
import OAI.Geometry.PrescribedPotential.InverseTraceFunction
import OAI.Geometry.PrescribedPotential.LinearFrameCalculus

namespace OAI

/-! Scalar Frame Calculus. -/

section

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

lemma potentialMatrix_const_add (c : ℝ) (f : V n → ℝ) (z : V n) :
    PotentialKaehler.potentialMatrix (fun y => c+f y) z = PotentialKaehler.potentialMatrix f z := by
  unfold PotentialKaehler.potentialMatrix
  have he : fderiv ℝ (fun y => c+f y) = fderiv ℝ f := funext (fun _ => fderiv_const_add c)
  rw [he]

lemma potentialMatrix_linear (B : V n →L[ℂ] V n) {f : V n → ℝ} {z : V n}
    (hf : ContDiffAt ℝ ∞ f (B z)) :
    PotentialKaehler.potentialMatrix (fun y => f (B y)) z =
      (frameMatrix B)ᴴ*PotentialKaehler.potentialMatrix f (B z)*frameMatrix B := by
  have he := PotentialKaehler.potentialMatrix_comp B.contDiff.contDiffAt hf
  have hb : fderiv ℂ (fun y => B y) z = B := B.fderiv
  simpa only [Function.comp_def,hb,frameMatrix] using he

lemma det_congruence_re (G B : Matrix (Fin n) (Fin n) ℂ) :
    (Bᴴ*G*B).det.re = ‖B.det‖^2*G.det.re := by
  rw [Matrix.det_mul,Matrix.det_mul,Matrix.det_conjTranspose]
  have he : (starRingEnd ℂ) B.det*G.det*B.det =
      ((‖B.det‖^2 : ℝ):ℂ)*G.det := by
    rw [show (starRingEnd ℂ) B.det*G.det*B.det =
      (B.det*(starRingEnd ℂ) B.det)*G.det by ring,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  change ((starRingEnd ℂ) B.det*G.det*B.det).re = _
  rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

lemma logdet_congruence (G B : Matrix (Fin n) (Fin n) ℂ)
    (hG : G.PosDef) (hB : IsUnit B) :
    Real.log (Bᴴ*G*B).det.re = Real.log (‖B.det‖^2) + Real.log G.det.re := by
  have hb : B.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  rw [det_congruence_re]
  exact Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.mpr hb))
    (ne_of_gt (Complex.pos_iff.mp hG.det_pos).1)

lemma matrix_logdet_smooth {U : Set (V n)}
    {M : V n → Matrix (Fin n) (Fin n) ℂ} (hM : ContDiffOn ℝ ∞ M U)
    (hp : ∀ y ∈ U, (M y).PosDef) :
    ContDiffOn ℝ ∞ (fun y => Real.log (M y).det.re) U := by
  exact (Complex.reCLM.contDiff.comp_contDiffOn
    (determinant_smooth.comp_contDiffOn hM)).log
    (fun y hy => ne_of_gt (Complex.pos_iff.mp (hp y hy).det_pos).1)

lemma potentialMatrix_logdet_pullMetric {U : Set (V n)} (hU : IsOpen U)
    (B : V n →L[ℂ] V n) (hB : IsUnit (frameMatrix B))
    {M : V n → Matrix (Fin n) (Fin n) ℂ} (hM : ContDiffOn ℝ ∞ M U)
    (hp : ∀ y ∈ U, (M y).PosDef) {z : V n} (hz : B z ∈ U) :
    PotentialKaehler.potentialMatrix (fun y => Real.log (pullMetric B M y).det.re) z =
      (frameMatrix B)ᴴ * PotentialKaehler.potentialMatrix (fun y => Real.log (M y).det.re) (B z) * frameMatrix B := by
  have he : (fun y => Real.log (pullMetric B M y).det.re) =ᶠ[𝓝 z]
      (fun y => Real.log (‖(frameMatrix B).det‖^2) + Real.log (M (B y)).det.re) := by
    filter_upwards [B.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hz)] with y hy
    exact logdet_congruence (M (B y)) (frameMatrix B) (hp (B y) hy) hB
  rw [PotentialKaehler.potentialMatrix_congr he]
  rw [potentialMatrix_const_add]
  exact potentialMatrix_linear B (f := fun y => Real.log (M y).det.re)
    (z := z) ((matrix_logdet_smooth hM hp).contDiffAt (hU.mem_nhds hz))

lemma inverseTrace_pullMetric (B : V n →L[ℂ] V n) (hB : IsUnit (frameMatrix B))
    (M G : V n → Matrix (Fin n) (Fin n) ℂ) (z : V n) :
    inverseTrace (pullMetric B M) (pullMetric B G) z = inverseTrace M G (B z) := by
  let C := frameMatrix B
  have hc : C*C⁻¹ = 1 := Matrix.mul_nonsing_inv C ((Matrix.isUnit_iff_isUnit_det C).mp hB)
  have hd : Cᴴ⁻¹*Cᴴ = 1 := by
    rw [← Matrix.conjTranspose_nonsing_inv,← Matrix.conjTranspose_mul,hc,Matrix.conjTranspose_one]
  unfold inverseTrace pullMetric
  change ((Cᴴ*M (B z)*C)⁻¹*(Cᴴ*G (B z)*C)).trace.re = _
  simp only [Matrix.mul_inv_rev,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Cᴴ⁻¹ Cᴴ,hd,Matrix.one_mul]
  have he : (C⁻¹*((M (B z))⁻¹*(G (B z)*C))).trace = ((M (B z))⁻¹*G (B z)).trace := by
    rw [← Matrix.mul_assoc (M (B z))⁻¹,← Matrix.mul_assoc C⁻¹,
      Matrix.trace_mul_cycle, hc,Matrix.one_mul]
  rw [he]
end KaehlerCalculus

end
end

end OAI
