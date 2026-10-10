import Mathlib
import OAI.Analysis.Commutator.MatrixNormalTrace
import OAI.Analysis.Commutator.MatrixTowerDiffuse

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

local instance matrixDiffuseTransferIndexDecidableEq : DecidableEq ι := Classical.decEq ι

lemma entry_diagonal (a : H →L[ℂ] H) (i : ι) :
    entry ι (diagonal (H:=H) ι a) i i=a := by
  ext x
  simp only [entry_apply,diagonal_single,single_apply,ite_true]

def diagonalHom : M →⋆ₐ[ℂ] matrixVonNeumann ι i₀ M :=
  rangeRestriction (matrixVonNeumann ι i₀ M)
    ((diagonal (H:=H) ι).comp M.toStarSubalgebra.subtype)
    (fun a => diagonal_mem_matrixVonNeumann ι i₀ M a.property)

lemma coe_diagonalHom (a : M) :
    (diagonalHom ι i₀ M a:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι)=
      diagonal (H:=H) ι (a:H →L[ℂ] H) := rfl

lemma diagonalHom_injective : Function.Injective (diagonalHom ι i₀ M) := by
  intro a b h
  apply Subtype.ext
  have he := congrArg (fun T : matrixVonNeumann ι i₀ M =>
    entry ι (T:SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) i₀ i₀) h
  simpa only [coe_diagonalHom,entry_diagonal] using he

lemma matrixTrace_diagonal (τ : M →ₚ[ℂ] ℂ) (a : M) :
    matrixTrace ι i₀ M τ (diagonalHom ι i₀ M a)=τ a := by
  rw [matrixTrace_apply]
  have he (i : ι) : (⟨entry ι ((diagonalHom ι i₀ M a):SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) i i,
    (mem_matrixVonNeumann ι i₀ M _).mp (diagonalHom ι i₀ M a).property i i⟩:M)=a := by
    apply Subtype.ext
    exact entry_diagonal ι (a:H →L[ℂ] H) i
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  let : Nonempty ι := ⟨i₀⟩
  rw [←mul_assoc,inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α:=ι)),one_mul]

theorem matrix_diffuse_of_stages (hM : FactorCorner.IsFactor M)
    (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M,τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (F : ℕ → MatrixTower.Stage M) (hsize : ∀ N : ℕ,∃ n,N<Fintype.card (F n).I) :
    DiffuseProjection.HasNoMinimalProjections (matrixVonNeumann ι i₀ M) := by
  apply MatrixTower.diffuse_of_small (matrixVonNeumann ι i₀ M) (matrixTrace ι i₀ M τ)
    (matrixTrace_tracial ι i₀ M τ hτ) (matrixTrace_faithful ι i₀ M τ hfaith)
    (factor_matrixVonNeumann ι i₀ M hM)
  intro ε hε
  obtain ⟨q,hq,hqn,hqt⟩ := MatrixTower.small_of_stages M τ hτ h1 F hsize hε
  refine ⟨diagonalHom ι i₀ M q,hq.map (diagonalHom ι i₀ M),?_,?_⟩
  · intro h
    apply hqn
    apply diagonalHom_injective ι i₀ M
    simpa only [map_zero] using h
  · rwa [matrixTrace_diagonal]

end Kadison.OperatorAmplification

end

end
end

end OAI
