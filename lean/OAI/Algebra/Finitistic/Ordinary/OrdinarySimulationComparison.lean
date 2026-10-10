import OAI.Algebra.Finitistic.Ordinary.OrdinaryFullTensorComplex
import OAI.Algebra.Finitistic.Ordinary.OrdinarySupportedExtension
import OAI.Algebra.Finitistic.Ordinary.OrdinaryShiftSign

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)

theorem differential_transport {n n' m m' : ℤ} (hn : n = n') (hm : m = m') :
    eqToHom (congrArg P.X hn) ≫ P.d n' m' = P.d n m ≫ eqToHom (congrArg P.X hm) := by
  subst n'
  subst m'
  simp only [eqToHom_refl,Category.id_comp,Category.comp_id]

/-- Align the finite resolution's degree n with the source's degree a+n. -/
def restrictedShiftIso : P.restriction (ComplexShape.embeddingUpIntGE a) ≅
    (unsignedShift P (a+(l:ℤ))).restriction (TensorResolution.degreeEmbedding l) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => eqToIso (by
    change P.X (a+(n:ℤ)) = P.X ((-(l:ℤ)+n)+(a+l))
    congr 1
    omega)) (by
      intro n m _
      have hn : (-(l:ℤ)+(n:ℤ))+(a+l) = a+n := by omega
      have hm : (-(l:ℤ)+(m:ℤ))+(a+l) = a+m := by omega
      change eqToHom (congrArg P.X hn.symm) ≫ P.d ((-(l:ℤ)+n)+(a+l)) ((-(l:ℤ)+m)+(a+l)) =
        P.d (a+n) (a+m) ≫ eqToHom (congrArg P.X hm.symm)
      exact differential_transport P hn.symm hm.symm)

/-- The lower support condition of the manuscript supplies strict support after reindexing. -/
theorem unsignedSupport (hP : ∀ n : ℤ, n < a → IsZero (P.X n)) :
    (unsignedShift P (a+(l:ℤ))).IsStrictlySupported (TensorResolution.degreeEmbedding l) :=
  ⟨fun n hn => by
    have hlt : n < -(l:ℤ) := by
      by_contra h
      let j := (n+(l:ℤ)).toNat
      have hj : (TensorResolution.degreeEmbedding l).f j = n := by
        simp only [TensorResolution.degreeEmbedding_apply]
        dsimp [j]
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      exact hn j hj
    exact hP (n+(a+l)) (by omega)⟩

/-- The computed BC-balanced tensor complex in degrees -l,...,0 with both B-actions. -/
def computedTensorComplex : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ :=
  (FullTensorTerm.complex P a l).extend (TensorResolution.degreeEmbedding l)

/-- Full bimodule chain comparison, including all zero terms and the genuine integer shift sign. -/
def computedTensorIso
    (hLower : ∀ n : ℤ, n < a → IsZero (P.X n))
    (hUpper : ∀ n : ℕ, l < n → IsZero (P.X (a+(n:ℤ)))) :
    computedTensorComplex P a l ≅ P⟦a+(l:ℤ)⟧ := by
  letI := unsignedSupport P a l hLower
  exact ((TensorResolution.degreeEmbedding l).extendFunctor (ModuleCat.{u} (Enveloping k B))).mapIso
      (FullTensorTerm.complexIso P a l hUpper ≪≫ restrictedShiftIso P a l) ≪≫
    SupportedExtension.iso (unsignedShift P (a+(l:ℤ))) (TensorResolution.degreeEmbedding l) ≪≫
    shiftSignIso P (a+(l:ℤ))

/-- Exact source indexing: b=a+l, with only the manuscript's support hypothesis. -/
def sourceShiftComparison (b : ℤ) (hb : a+(l:ℤ)=b)
    (hP : ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) :
    computedTensorComplex P a l ≅ P⟦b⟧ := by
  subst b
  exact computedTensorIso P a l (fun n hn => hP n (Or.inl hn))
    (fun n hn => hP (a+(n:ℤ)) (Or.inr (by omega)))
end LittleFinitistic.OrdinarySimulation

end

end OAI
