import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.SeparationHomogeneity
import OAI.Combinatorics.Chromatic.Shuffle.ClearingKernel

namespace OAI

section
namespace ElementaryPositivity.LaurentAtInfinity
variable {R : Type*} [CommRing R] [Algebra ℚ R]
lemma polynomial_rat_smul (r : ℚ) (x : Polynomial R) :
    polynomial (r • x)=r • polynomial x := by
  rw [Algebra.smul_def,Polynomial.algebraMap_apply,map_mul,polynomial_C,rat_smul_series]
lemma rat_smul_mul (r : ℚ) (x y : LaurentSeries R) :
    (r • x)*y=r • (x*y) := by
  rw [rat_smul_series,rat_smul_series,mul_assoc]
end ElementaryPositivity.LaurentAtInfinity

namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity SeparationInfinity
open ElementaryPositivity.PackConvolution
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
noncomputable local instance clearedSepTensorRing (d e : I → ℕ) : CommRing (S d⊗[ℚ]S e) := inferInstance
noncomputable local instance clearedSepTensorAlg (d e : I → ℕ) : Algebra ℚ (S d⊗[ℚ]S e) := inferInstance

lemma normalize_cleared_tensor (d e : I → ℕ) (x y : S d⊗[ℚ]S e)
    (h : crossTensor d e*x=crossSign d e • y) :
    (inverseKernelUnit (fun _ _ : I=>0) d e).val *
      polynomial (relativeTaylor d e x)=polynomial (relativeTaylor d e y) := by
  have H := congrArg (fun z=>polynomial (relativeTaylor d e z)) h
  rw [map_mul,map_mul,polynomial_crossTensor] at H
  have hs : relativeTaylor d e (crossSign d e • y)=
      crossSign d e • relativeTaylor d e y := (relativeTaylor d e).toLinearMap.map_smul _ _
  rw [hs,polynomial_rat_smul,rat_smul_mul] at H
  have H' := congrArg (fun z=>crossSign d e • z) H
  simpa only [smul_smul,crossSign_sq,one_smul] using H'

lemma separation_of_cleared (a : I → I → ℕ) (d e : I → ℕ) (x y : S d⊗[ℚ]S e)
    (h : crossTensor d e*x=crossSign d e • y) :
    (inverseKernelUnit a d e).val * polynomial (relativeTaylor d e x)=
    ((inverseKernelUnit a d e)*(inverseKernelUnit (fun _ _ : I=>0) d e)⁻¹).val *
      polynomial (relativeTaylor d e y) := by
  rw [←normalize_cleared_tensor d e x y h,Units.val_mul]
  simp only [mul_assoc,Units.inv_mul_cancel_left]

variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
lemma separation_shuffle_grid (a : I → I → ℕ) {d e α β : I → ℕ} (h : d+e=α+β)
    (f : S d) (g : S e) {s : Pack (A:=A)} (R : Realization (α+β) s) :
    tensorSeparationSeries a α β (castS h (shufflePolynomial a f g))=
    ((inverseKernelUnit a α β)*(inverseKernelUnit (fun _ _ : I=>0) α β)⁻¹).val *
      polynomial (relativeTaylor α β
        (gridTensor a f g (cutRealizationEquiv R (firstCut α β)).val
          (leftRealization R (firstCut α β)) (rightRealization R (firstCut α β)))) :=
  separation_of_cleared a α β _ _ (cleared_restrictTensor a h f g R (firstCut α β))

end ElementaryPositivity.RawShuffle

end

end OAI
