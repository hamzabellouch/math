import Mathlib
import OAI.Geometry.PrescribedPotential.ComplexOperator
import OAI.Geometry.PrescribedPotential.KaehlerClosedDerivatives
import OAI.Geometry.PrescribedPotential.SymmetricPrincipalFrame
import OAI.Geometry.PrescribedPotential.TracePositivity

namespace OAI

/-! Scalar Principal Wirtinger. -/

section

 

noncomputable section
open Set Filter Topology Matrix Finset
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
open EllipticKernel FrozenPoisson HigherJet
variable {n : ℕ}
local instance realECIP : InnerProductSpace ℝ (EC n) := InnerProductSpace.rclikeToReal ℂ (EC n)

lemma scalar_principal_real {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ (EC n))
    (M : Matrix (Fin n) (Fin n) ℂ) {f : EC n → ℝ} {x : EC n} (hf : ContDiffAt ℝ ∞ f x) :
    principalApply e (traceBilin M) (fderiv ℝ (fderiv ℝ f) x) =
      (M⁻¹*PotentialKaehler.potentialMatrix (f ∘ (coordinateEquiv n).symm) (coordinateEquiv n x)).trace.re := by
  rw [principalApply_symmetric e _ _ (hf.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top))]
  have he : traceBilin M (fderiv ℝ (fderiv ℝ f) x) =
      ∑ i, ∑ j, traceBilin M (rankTwo (e i) (e j))*fderiv ℝ (fderiv ℝ f) x (e i) (e j) := by
    conv_lhs => rw [bilin_expansion e (fderiv ℝ (fderiv ℝ f) x)]
    simp only [map_sum,map_smul,smul_eq_mul]
    exact sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => mul_comm _ _))
  simp only [smul_eq_mul]
  rw [← he,traceBilin_apply,pullBilin_hessian hf]
  rfl

lemma wirtinger_re_im {f : V n → ℂ} {z : V n} (hf : ContDiffAt ℝ ∞ f z) (u v : V n) :
    dzbar u (dz v f) z =
      dzbar u (dz v (fun y => ((f y).re:ℂ))) z +
      Complex.I*dzbar u (dz v (fun y => ((f y).im:ℂ))) z := by
  have hr : ContDiffAt ℝ ∞ (fun y => (f y).re) z := Complex.reCLM.contDiff.contDiffAt.comp z hf
  have hi : ContDiffAt ℝ ∞ (fun y => (f y).im) z := Complex.imCLM.contDiff.contDiffAt.comp z hf
  rw [dzbar_dz_real hr,dzbar_dz_real hi]
  simp only [dzbar,dz,wderiv,fderiv_wderiv hf]
  have hre (a b : V n) : fderiv ℝ (fderiv ℝ (fun y => (f y).re)) z a b =
      (fderiv ℝ (fderiv ℝ f) z a b).re := GlobalElliptic.second_postcomp hf Complex.reCLM a b
  have him (a b : V n) : fderiv ℝ (fderiv ℝ (fun y => (f y).im)) z a b =
      (fderiv ℝ (fderiv ℝ f) z a b).im := GlobalElliptic.second_postcomp hf Complex.imCLM a b
  simp only [PotentialKaehler.hermitianPart,hre,him]
  apply Complex.ext <;> simp <;> ring

lemma inverse_wirtinger_real (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.PosDef)
    {f : V n → ℝ} {z : V n} (hf : ContDiffAt ℝ ∞ f z) :
    (∑ p, ∑ q, M⁻¹ p q*dzbar (e q) (dz (e p) (fun y => (f y:ℂ))) z) =
      (((M⁻¹*PotentialKaehler.potentialMatrix f z).trace.re : ℝ):ℂ) := by
  rw [trace_mul_real hM.inv.isHermitian (PotentialKaehler.potentialMatrix_hermitian hf)]
  simp only [Matrix.trace]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  change M⁻¹ p q*dzbar (e q) (dz (e p) (fun y => (f y:ℂ))) z = M⁻¹ p q*PotentialKaehler.potentialMatrix f z q p
  rw [potentialMatrix_eq_dzbar_dz hf]
  rfl

lemma inverse_wirtinger_complex (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.PosDef)
    {f : V n → ℂ} {z : V n} (hf : ContDiffAt ℝ ∞ f z) :
    (∑ p, ∑ q, M⁻¹ p q*dzbar (e q) (dz (e p) f) z) =
      ((M⁻¹*PotentialKaehler.potentialMatrix (fun y => (f y).re) z).trace.re:ℂ) +
      Complex.I*((M⁻¹*PotentialKaehler.potentialMatrix (fun y => (f y).im) z).trace.re:ℂ) := by
  simp only [wirtinger_re_im hf,mul_add,sum_add_distrib]
  have he : (∑ p, ∑ q, M⁻¹ p q*(Complex.I*dzbar (e q) (dz (e p) (fun y => ((f y).im:ℂ))) z)) =
      Complex.I*(∑ p, ∑ q, M⁻¹ p q*dzbar (e q) (dz (e p) (fun y => ((f y).im:ℂ))) z) := by
    simp only [Finset.mul_sum]
    exact sum_congr rfl (fun p _ => sum_congr rfl (fun q _ => by ring))
  have hr : ContDiffAt ℝ ∞ (fun y => (f y).re) z := Complex.reCLM.contDiff.contDiffAt.comp z hf
  have hi : ContDiffAt ℝ ∞ (fun y => (f y).im) z := Complex.imCLM.contDiff.contDiffAt.comp z hf
  rw [he,inverse_wirtinger_real M hM hr,inverse_wirtinger_real M hM hi]
end KaehlerCalculus

end
end

end OAI
