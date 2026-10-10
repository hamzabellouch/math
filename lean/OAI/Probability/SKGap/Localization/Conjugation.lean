import Mathlib
import OAI.Probability.SKGap.Localization.RealPart

namespace OAI

section
noncomputable section
namespace SKGap.ComplexMatrix
open Matrix
open scoped Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma conjugate_frobenius (U : unitary (Matrix ι ι ℂ)) (M : Matrix ι ι ℂ) :
    ‖conjugate U M‖ = ‖M‖ := by
  change ‖(U : Matrix ι ι ℂ)*M*(U : Matrix ι ι ℂ)ᴴ‖ = _
  rw [frobenius_mul_unitary ((U : Matrix ι ι ℂ)*M) ((U : Matrix ι ι ℂ)ᴴ) (Unitary.star_mem U.property),
    frobenius_unitary_mul _ _ U.property]

noncomputable def conjugateIsometry (U : unitary (Matrix ι ι ℂ)) :
    Matrix ι ι ℂ ≃ₗᵢ[ℝ] Matrix ι ι ℂ where
  toLinearEquiv := (conjugate U).toAlgEquiv.toLinearEquiv.restrictScalars ℝ
  norm_map' := conjugate_frobenius U

lemma conjugate_opNorm (U : unitary (Matrix ι ι ℂ)) (M : Matrix ι ι ℂ) :
    opNorm (conjugate U M) = opNorm M := by
  change ‖lin ((U : Matrix ι ι ℂ)*M*(U : Matrix ι ι ℂ)ᴴ)‖ = _
  rw [lin_mul,lin_mul]
  have hstar : lin ((U : Matrix ι ι ℂ)ᴴ) ∈ unitary _ := lin_unitary _ (Unitary.star_mem U.property)
  rw [CStarRing.norm_mul_mem_unitary _ hstar,
    CStarRing.norm_mem_unitary_mul _ (lin_unitary _ U.property)]
  rfl

lemma matrixProject_conjugate (U : unitary (Matrix ι ι ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (M : Matrix ι ι ℂ) :
    matrixProject R hR (conjugate U M) = conjugate U (matrixProject R hR M) := by
  apply convexProject_equivariant (hermitianBall_good hR) (conjugateIsometry U)
  intro N
  change ((conjugate U N)ᴴ = conjugate U N ∧ opNorm (conjugate U N) ≤ R) ↔
    (Nᴴ = N ∧ opNorm N ≤ R)
  have hh : (conjugate U N)ᴴ = conjugate U Nᴴ := (map_star (conjugate U) N).symm
  have he : conjugate U Nᴴ = conjugate U N ↔ Nᴴ=N :=
    ⟨fun h => (conjugate U).injective h,fun h => congrArg (conjugate U) h⟩
  rw [hh,he,conjugate_opNorm]

lemma truncatedG_conjugate (f : 𝓢(ℝ,ℂ)) (U : unitary (Matrix ι ι ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B D M : Matrix ι ι ℂ) (hB : Bᴴ=B) (hD : Dᴴ=D) :
    truncatedG f R hR (conjugate U B) (conjugate U D) (conjugate U M) =
      conjugate U (truncatedG f R hR B D M) := by
  have hs : sandShift (conjugate U B) (conjugate U D) (matrixProject R hR (conjugate U M)) =
      conjugate U (sandShift B D (matrixProject R hR M)) := by
    simp only [sandShift,matrixProject_conjugate,map_sub,map_mul]
  unfold truncatedG
  rw [hs,schwartzMatrix_conjugate f U _
    (sandShift_hermitian _ _ _ hB hD (matrixProject_bound R hR M).1)]
  simp only [map_mul]

lemma truncatedK_conjugate (f : 𝓢(ℝ,ℂ)) (U : unitary (Matrix ι ι ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (B D C M : Matrix ι ι ℂ) (hB : Bᴴ=B) (hD : Dᴴ=D) :
    truncatedK f R hR (conjugate U B) (conjugate U D) (conjugate U C) (conjugate U M) =
      conjugate U (truncatedK f R hR B D C M) := by
  simp only [truncatedK,truncatedG_conjugate f U hR B D M hB hD,matrixProject_conjugate,
    map_add,map_one,map_mul,map_sub]
end SKGap.ComplexMatrix
end
end

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory
open RealComplex ComplexMatrix
open scoped Matrix.Norms.Frobenius SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def signConjugate (s : ι → ℝ) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i k => s i*s k*M i k

noncomputable def signUnitary (s : ι → ℝ) (hs : ∀ i, s i^2=1) :
    unitary (Matrix ι ι ℂ) :=
  ⟨diagonal (fun i => (s i : ℂ)), by
    have hh : ∀ i, (s i : ℂ)*(s i : ℂ)=1 := by
      intro i
      exact_mod_cast (show s i*s i=1 by nlinarith [hs i])
    change (diagonal (fun i => (s i : ℂ)))ᴴ*diagonal (fun i => (s i : ℂ))=1 ∧
      diagonal (fun i => (s i : ℂ))*(diagonal (fun i => (s i : ℂ)))ᴴ=1
    simp only [diagonal_conjTranspose,Pi.star_apply,Complex.star_def,Complex.conj_ofReal,
      diagonal_mul_diagonal,hh,diagonal_one,and_self]⟩

lemma sign_conjugate_entry (s : ι → ℝ) (hs : ∀ i, s i^2=1) (M : Matrix ι ι ℂ) (i k : ι) :
    conjugate (signUnitary s hs) M i k = (s i:ℂ)*(s k:ℂ)*M i k := by
  change (diagonal (fun b => (s b:ℂ))*M*(diagonal (fun b => (s b:ℂ)))ᴴ) i k = _
  simp only [diagonal_conjTranspose,Pi.star_apply,Complex.star_def,Complex.conj_ofReal,mul_diagonal,diagonal_mul]
  ring

lemma sign_conjugate_diagonal (s : ι → ℝ) (hs : ∀ i, s i^2=1) (d : ι → ℝ) :
    conjugate (signUnitary s hs) (liftMatrix (diagonal d)) = liftMatrix (diagonal d) := by
  ext i k
  rw [sign_conjugate_entry]
  by_cases hik : i=k
  · subst k
    simp only [liftMatrix,Matrix.map_apply,diagonal_apply_eq]
    have h : (s i:ℂ)*(s i:ℂ)=1 := by exact_mod_cast (show s i*s i=1 by nlinarith [hs i])
    rw [h,one_mul]
  · simp [liftMatrix,Matrix.diagonal,hik]

lemma sign_conjugate_lift (s : ι → ℝ) (hs : ∀ i, s i^2=1) (M : Matrix ι ι ℝ) :
    conjugate (signUnitary s hs) (liftMatrix M) = liftMatrix (signConjugate s M) := by
  ext i k
  simp [sign_conjugate_entry,liftMatrix,signConjugate]

lemma realPart_sign_conjugate (s : ι → ℝ) (hs : ∀ i, s i^2=1) (M : Matrix ι ι ℂ) :
    RealComplex.realPart (conjugate (signUnitary s hs) M) = signConjugate s (RealComplex.realPart M) := by
  ext i k
  simp [RealComplex.realPart,sign_conjugate_entry,signConjugate,Complex.mul_re]

lemma realTruncatedK_sign (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (s : ι → ℝ) (hs : ∀ i, s i^2=1) (d c : ι → ℝ) (M : Matrix ι ι ℝ) :
    realTruncatedK f R hR (diagonal d) (diagonal c) (signConjugate s M) =
      signConjugate s (realTruncatedK f R hR (diagonal d) (diagonal c) M) := by
  unfold realTruncatedK
  rw [← sign_conjugate_lift s hs M]
  have hd := liftMatrix_hermitian (diagonal d) (diagonal_transpose _)
  have hc := liftMatrix_hermitian (diagonal c) (diagonal_transpose _)
  have hB : (1+liftMatrix (diagonal d)*liftMatrix (diagonal c)*liftMatrix (diagonal d))ᴴ =
      1+liftMatrix (diagonal d)*liftMatrix (diagonal c)*liftMatrix (diagonal d) := by
    simp only [conjTranspose_add,conjTranspose_one,conjTranspose_mul,hd,hc,mul_assoc]
  have he := truncatedK_conjugate f (signUnitary s hs) hR
    (1+liftMatrix (diagonal d)*liftMatrix (diagonal c)*liftMatrix (diagonal d))
    (liftMatrix (diagonal d)) (liftMatrix (diagonal c)) (liftMatrix M) hB hd
  simp only [map_add,map_one,map_mul,sign_conjugate_diagonal] at he
  rw [he,realPart_sign_conjugate]
end SKGap
end
end

end OAI
