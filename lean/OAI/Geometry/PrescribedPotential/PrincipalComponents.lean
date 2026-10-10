import Mathlib
import OAI.Geometry.PrescribedPotential.ComplexHessian
import OAI.Geometry.PrescribedPotential.MatrixHilbertCoordinates
import OAI.Geometry.PrescribedPotential.MatrixWirtinger
import OAI.Geometry.PrescribedPotential.ScalarPrincipalWirtinger

namespace OAI

/-! Principal Components. -/

section

noncomputable section
open Set Filter Topology Matrix Finset
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace HigherJet
open EllipticKernel FrozenPoisson KaehlerCalculus
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {ι : Type*} [Fintype ι]
lemma principalApply_postcomp (e : OrthonormalBasis ι ℝ E) (L : SecondOrder E)
    (H : E →L[ℝ] E →L[ℝ] F) (_J : G) (l : F →L[ℝ] G)
    (Q : E →L[ℝ] E →L[ℝ] G) (hQ : ∀ v w, Q v w = l (H v w)) :
    principalApply e L Q = l (principalApply e L H) := by
  simp only [principalApply,map_sum,map_smul,hQ]
lemma principalApply_hessian_postcomp (e : OrthonormalBasis ι ℝ E) (L : SecondOrder E)
    {f : E → F} {x : E} (hf : ContDiffAt ℝ ∞ f x) (l : F →L[ℝ] G) :
    principalApply e L (fderiv ℝ (fderiv ℝ (fun y => l (f y))) x) =
      l (principalApply e L (fderiv ℝ (fderiv ℝ f) x)) :=
  principalApply_postcomp e L _ (0:G) l _ (fun v w => GlobalElliptic.second_postcomp_general hf l v w)
end HigherJet
namespace MetricSystem
open EllipticKernel FrozenPoisson HigherJet KaehlerCalculus
variable {n : ℕ} {ι : Type*} [Fintype ι]
local instance componentRealECIP : InnerProductSpace ℝ (EC n) := InnerProductSpace.rclikeToReal ℂ (EC n)
lemma complex_principal (basis : OrthonormalBasis ι ℝ (EC n)) (M : Mat n) (hM : M.PosDef)
    {f : EC n → ℂ} {x : EC n} (hf : ContDiffAt ℝ ∞ f x) :
    principalApply basis (traceBilin M) (fderiv ℝ (fderiv ℝ f) x) =
      ∑ p, ∑ q, M⁻¹ p q*dzbar (e q) (dz (e p) (f ∘ (coordinateEquiv n).symm)) (coordinateEquiv n x) := by
  have hcomp : ContDiffAt ℝ ∞ (f ∘ (coordinateEquiv n).symm) (coordinateEquiv n x) :=
    (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using hf : ContDiffAt ℝ ∞ f ((coordinateEquiv n).symm (coordinateEquiv n x))).comp _ (coordinateEquiv n).symm.contDiff.contDiffAt
  rw [inverse_wirtinger_complex M hM hcomp]
  apply Complex.ext
  · have hr : ContDiffAt ℝ ∞ (fun y => (f y).re) x := Complex.reCLM.contDiff.contDiffAt.comp x hf
    have he := scalar_principal_real basis M hr
    have hp := principalApply_hessian_postcomp basis (traceBilin M) hf Complex.reCLM
    simpa [Function.comp_def] using hp.symm.trans he
  · have hi : ContDiffAt ℝ ∞ (fun y => (f y).im) x := Complex.imCLM.contDiff.contDiffAt.comp x hf
    have he := scalar_principal_real basis M hi
    have hp := principalApply_hessian_postcomp basis (traceBilin M) hf Complex.imCLM
    simpa [Function.comp_def] using hp.symm.trans he

 def entryCLM (i j : Fin n) : HM n →L[ℝ] ℂ :=
  ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.proj i)).comp (encode n).symm.toContinuousLinearMap
@[simp] lemma entryCLM_apply (i j : Fin n) (u : HM n) : entryCLM i j u = u (i,j) := rfl

lemma encoded_principal (basis : OrthonormalBasis ι ℝ (EC n))
    {M : V n → Mat n} {z : V n} (hM : ContDiffAt ℝ ∞ M z) (hp : (M z).PosDef) :
    principalBilinear basis (M z)⁻¹
      (fderiv ℝ (fderiv ℝ (fun x => encode n (M (coordinateEquiv n x)))) ((coordinateEquiv n).symm z)) =
      encode n (∑ p, ∑ q, (M z)⁻¹ p q • mderiv Complex.I (e q) (mderiv (-Complex.I) (e p) M) z) := by
  let u : EC n → HM n := fun x => encode n (M (coordinateEquiv n x))
  let x := (coordinateEquiv n).symm z
  have hu : ContDiffAt ℝ ∞ u x := (encode n).contDiff.contDiffAt.comp x
    ((by simpa only [x,ContinuousLinearEquiv.apply_symm_apply] using hM : ContDiffAt ℝ ∞ M (coordinateEquiv n x)).comp x (coordinateEquiv n).contDiff.contDiffAt)
  rw [principalBilinear_inv]
  apply PiLp.ext
  intro ij
  obtain ⟨i,j⟩ := ij
  have he := complex_principal basis (M z) hp ((entryCLM i j).contDiff.contDiffAt.comp x hu)
  have hpcomp := principalApply_hessian_postcomp basis (traceBilin (M z)) hu (entryCLM i j)
  have he := hpcomp.symm.trans he
  have hf : (fun y => entryCLM i j (u y)) ∘ (coordinateEquiv n).symm = fun y => M y i j := by
    funext y
    simp [u]
  change _ = ∑ p, ∑ q, (M z)⁻¹ p q*dzbar (e q) (dz (e p) ((fun y => entryCLM i j (u y)) ∘ (coordinateEquiv n).symm)) (coordinateEquiv n x) at he
  rw [hf] at he
  simpa only [entryCLM_apply,u,x,ContinuousLinearEquiv.apply_symm_apply,encode_apply,
    Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,mderiv,dzbar,dz] using he
end MetricSystem

end
end

end OAI
