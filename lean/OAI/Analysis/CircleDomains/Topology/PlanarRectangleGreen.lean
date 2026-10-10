import OAI.Analysis.CircleDomains.Topology.PlanarFormPullback
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

namespace OAI

/-! Green's formula for the pullback of an actual smooth planar form on a
parameter rectangle. The only input is the existing rectangular divergence theorem. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma integral_pulledPlanarForm_curl_rectangle
    {P Q : ℂ → ℝ} {F : (ℝ × ℝ) → ℂ}
    (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q) (hF : ContDiff ℝ ∞ F)
    (a b : ℝ × ℝ) (hab : a ≤ b) :
    (∫ x in Icc a b,
      ((((fderiv ℝ F x) (1,0)).re * ((fderiv ℝ F x) (0,1)).im -
        ((fderiv ℝ F x) (1,0)).im * ((fderiv ℝ F x) (0,1)).re) *
        ((fderiv ℝ Q (F x)) 1 - (fderiv ℝ P (F x)) Complex.I))) =
      ((∫ s in a.1..b.1, pulledPlanarForm P Q F (1,0) (s,a.2)) +
        ∫ t in a.2..b.2, pulledPlanarForm P Q F (0,1) (b.1,t)) -
      (∫ s in a.1..b.1, pulledPlanarForm P Q F (1,0) (s,b.2)) -
        ∫ t in a.2..b.2, pulledPlanarForm P Q F (0,1) (a.1,t) := by
  let A := pulledPlanarForm P Q F (1,0)
  let B := pulledPlanarForm P Q F (0,1)
  have hA : ContDiff ℝ ∞ A := pulledPlanarForm_contDiff hP hQ hF _
  have hB : ContDiff ℝ ∞ B := pulledPlanarForm_contDiff hP hQ hF _
  have hder : Continuous (fun x => (fderiv ℝ B x) (1,0) + (fderiv ℝ (-A) x) (0,1)) :=
    ((hB.continuous_fderiv (by simp)).clm_apply continuous_const).add
      (((hA.neg).continuous_fderiv (by simp)).clm_apply continuous_const)
  have hi : IntegrableOn (fun x => (fderiv ℝ B x) (1,0) +
      (fderiv ℝ (-A) x) (0,1)) (Icc a b) volume :=
    hder.continuousOn.integrableOn_compact isCompact_Icc
  have he := integral_divergence_prod_Icc_of_hasFDerivAt_of_le B (-A)
    (fderiv ℝ B) (fderiv ℝ (-A)) a b hab hB.continuous.continuousOn
    hA.neg.continuous.continuousOn
    (fun x _ => (hB.differentiable (by simp) x).hasFDerivAt)
    (fun x _ => (hA.neg.differentiable (by simp) x).hasFDerivAt) hi
  have hcurl (x : ℝ × ℝ) :
      (fderiv ℝ B x) (1,0) + (fderiv ℝ (-A) x) (0,1) =
      ((((fderiv ℝ F x) (1,0)).re * ((fderiv ℝ F x) (0,1)).im -
        ((fderiv ℝ F x) (1,0)).im * ((fderiv ℝ F x) (0,1)).re) *
        ((fderiv ℝ Q (F x)) 1 - (fderiv ℝ P (F x)) Complex.I)) := by
    rw [fderiv_neg]
    change (fderiv ℝ B x) (1,0) - (fderiv ℝ A x) (0,1) = _
    exact pulledPlanarForm_curl hP hQ hF x
  simp_rw [hcurl] at he
  simp only [Pi.neg_apply,intervalIntegral.integral_neg] at he
  change _ = _ at he
  rw [he]
  ring

end CircleDomainRigidity

end

end OAI
