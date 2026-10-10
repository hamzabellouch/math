import Mathlib
import OAI.Analysis.AffineBernstein.FlatFEquation
import OAI.Analysis.AffineBernstein.BaseExponentialIBP

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma flatCofactorTrace_eq_det_mul {f : E → ℝ} (v : ι → E) (g : E → ℝ) (x : E)
    (hd : (flatBlockHessian f v x).det ≠ 0) :
    flatCofactorTrace f v g x = (flatBlockHessian f v x).det *
      flatInverseTrace (flatBlockHessian f v x) v g x := by
  simp only [flatCofactorTrace,flatInverseTrace,matrix_adjugate_entry hd,Finset.mul_sum,mul_assoc]

lemma flatCofactorPair_eq_det_mul {f : E → ℝ} (v : ι → E) (g h : E → ℝ) (x : E)
    (hd : (flatBlockHessian f v x).det ≠ 0) :
    flatCofactorPair f v g h x = (flatBlockHessian f v x).det *
      flatInversePair (flatBlockHessian f v x) v g h x := by
  simp only [flatCofactorPair,flatInversePair,matrix_adjugate_entry hd,Finset.mul_sum,mul_assoc]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma flatCofactorTrace_log {D : Set E} (hD : IsOpen D) {H : E → ℝ}
    (hH : ContDiffOn ℝ ∞ H D) (hpos : ∀ x ∈ D, 0 < H x)
    {x : E} (hx : x ∈ D) (v : ι → E) (hd : (-flatBlockHessian H v x).det ≠ 0) :
    flatCofactorTrace (fun y => -H y) v (fun y => Real.log (H y)) x =
      -((-flatBlockHessian H v x).det/H x*(Fintype.card ι : ℝ)) -
      flatCofactorPair (fun y => -H y) v (fun y => Real.log (H y)) (fun y => Real.log (H y)) x := by
  have hd' : (flatBlockHessian (fun y => -H y) v x).det ≠ 0 := by rwa [flatBlockHessian_neg]
  rw [flatCofactorTrace_eq_det_mul v _ _ hd',flatCofactorPair_eq_det_mul v _ _ _ hd',flatBlockHessian_neg]
  have hh := flat_log_hessian_trace hD hH hpos hx (-flatBlockHessian H v x) v
  rw [flatInverseTrace_neg_hessian _ _ _ hd] at hh
  have hHx := (hpos x hx).ne'
  apply (mul_left_cancel₀ hHx)
  have hm := congrArg (fun t : ℝ => (-flatBlockHessian H v x).det*t) hh
  field_simp
  nlinarith [hm]

variable {μ : Measure E} [μ.IsAddHaarMeasure]

/- Pointwise logarithmic Hessian identity plus genuine base integration by
parts gives the source p-identity. Its density is exactly `W detB/H`. -/
theorem integral_base_log_identity {D : Set E} (hD : IsOpen D) {H F σ : E → ℝ}
    (hH : ContDiffOn ℝ ∞ H D) (hF : ContDiffOn ℝ ∞ F D)
    (hpos : ∀ x ∈ D, 0 < H x) (v : ι → E)
    (hd : ∀ x ∈ D, (-flatBlockHessian H v x).det ≠ 0)
    (hσ : ContDiff ℝ ∞ σ) (hc : HasCompactSupport σ) (hσD : tsupport σ ⊆ D)
    (n c : ℝ) :
    let K := fun x => -H x
    let P := fun x => Real.log (H x)
    let W := fun x => Real.exp (-n*P x-c*F x)
    (∫ x, W x*σ x^2 *
      (((-flatBlockHessian H v x).det/H x)*(Fintype.card ι : ℝ)+
        (n+1)*flatCofactorPair K v P P x+c*flatCofactorPair K v F P x) ∂μ) =
      2*(∫ x, W x*σ x*flatCofactorPair K v σ P x ∂μ) := by
  dsimp only
  let P := fun x => Real.log (H x)
  have hP : ContDiffOn ℝ ∞ P D := hH.log (fun x hx => (hpos x hx).ne')
  have hh := integral_flatCofactor_exp_square (μ := μ) v hσ hc
    (fun x hx => (hH.contDiffAt (hD.mem_nhds (hσD hx))).neg)
    (fun x hx => hP.contDiffAt (hD.mem_nhds (hσD hx)))
    (fun x hx => hF.contDiffAt (hD.mem_nhds (hσD hx)))
    (fun x hx => hP.contDiffAt (hD.mem_nhds (hσD hx))) (-n) (-c)
  simp only [neg_mul,← sub_eq_add_neg] at hh
  have heq : (∫ x, Real.exp (-n*P x-c*F x)*σ x^2 *
      (((-flatBlockHessian H v x).det/H x)*(Fintype.card ι : ℝ)+
        (n+1)*flatCofactorPair (fun y => -H y) v P P x+
        c*flatCofactorPair (fun y => -H y) v F P x) ∂μ) =
    -(∫ x, Real.exp (-n*P x-c*F x)*σ x^2 *
      (flatCofactorTrace (fun y => -H y) v P x-n*flatCofactorPair (fun y => -H y) v P P x-
        c*flatCofactorPair (fun y => -H y) v F P x) ∂μ) := by
    rw [← integral_neg]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    dsimp only
    by_cases hx : x ∈ tsupport σ
    · rw [flatCofactorTrace_log hD hH hpos (hσD hx) v (hd x (hσD hx))]
      ring
    · simp only [image_eq_zero_of_notMem_tsupport hx,zero_pow two_ne_zero,mul_zero,zero_mul,neg_zero]
  rw [heq]
  simp only [neg_mul]
  rw [hh]
  ring

end AffineBernstein
end

end OAI
