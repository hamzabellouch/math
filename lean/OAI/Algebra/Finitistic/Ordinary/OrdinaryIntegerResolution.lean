import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorResolutionComplex
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation.TensorResolution
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ)

def degreeEmbedding : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ) :=
  ComplexShape.embeddingUpIntGE (-(l:ℤ))

instance degreeEmbedding_rel : (degreeEmbedding l).IsRelIff :=
  inferInstanceAs ((ComplexShape.embeddingUpIntGE (-(l:ℤ))).IsRelIff)

@[simp] theorem degreeEmbedding_apply (n : ℕ) : (degreeEmbedding l).f n = -(l:ℤ)+n := rfl

/-- Q_T in the manuscript's cohomological degrees -l,...,0. -/
def integerComplex : CochainComplex (ModuleCat.{u} (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ) ℤ :=
  (complex k B l).extend (degreeEmbedding l)

def integerTermIso (n : ℕ) : (integerComplex k B l).X (-(l:ℤ)+n) ≅ termObject k B l n :=
  (complex k B l).extendXIso (degreeEmbedding l) rfl

/-- The terminal simple is in degree zero after the actual reindexing. -/
def integerAugmentation : integerComplex k B l ⟶
    (HomologicalComplex.single _ (.up ℤ) 0).obj
      (ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B)) :=
  HomologicalComplex.extendMap (augmentationMap k B l) (degreeEmbedding l) ≫
    (HomologicalComplex.extendSingleIso (e := degreeEmbedding l)
      (X := ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B)) l 0 (by simp)).hom

theorem integerAugmentation_quasiIso : QuasiIso (integerAugmentation k B l) := by
  have := augmentationMap_quasiIso k B l
  exact inferInstanceAs (QuasiIso
    (HomologicalComplex.extendMap (augmentationMap k B l) (degreeEmbedding l) ≫
      (HomologicalComplex.extendSingleIso (e := degreeEmbedding l)
        (X := ModuleCat.of (B ⊗[k] ChainAlgebra k l)ᵐᵒᵖ (TerminalTensor B)) l 0 (by simp)).hom))

theorem integerTerm_lower (n : ℤ) (h : n < -(l:ℤ)) : IsZero ((integerComplex k B l).X n) := by
  apply (complex k B l).isZero_extend_X (degreeEmbedding l) n
  intro j hj
  simp only [degreeEmbedding_apply] at hj
  omega

theorem integerTerm_upper (n : ℤ) (h : 0 < n) : IsZero ((integerComplex k B l).X n) := by
  let j := (n+(l:ℤ)).toNat
  have hj : (degreeEmbedding l).f j = n := by
    simp only [degreeEmbedding_apply]
    dsimp [j]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  have hjl : l < j := by
    have hc : (j:ℤ) = n+(l:ℤ) := Int.toNat_of_nonneg (by omega)
    omega
  exact (term_vanishes k B l j hjl).of_iso ((complex k B l).extendXIso (degreeEmbedding l) hj)

theorem integerTerm_projective (n : ℤ) : Projective ((integerComplex k B l).X n) := by
  by_cases h : n < -(l:ℤ)
  · exact (integerTerm_lower k B l n h).projective
  let j := (n+(l:ℤ)).toNat
  have hj : (degreeEmbedding l).f j = n := by
    simp only [degreeEmbedding_apply]
    dsimp [j]
    rw [Int.toNat_of_nonneg (by omega)]
    omega
  exact Projective.of_iso ((complex k B l).extendXIso (degreeEmbedding l) hj).symm (projectiveTerm k B l j)
end LittleFinitistic.OrdinarySimulation.TensorResolution

end

end OAI
