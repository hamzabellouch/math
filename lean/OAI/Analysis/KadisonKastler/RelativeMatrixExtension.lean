import OAI.Analysis.KadisonKastler.RelativeMatrixFactorEquiv

namespace OAI

/-! # Extending a finite matrix stage inside its relative commutant -/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem matrix_concrete_mono
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (E : MatrixUnitSystem ι (Algebra M)) (F : MatrixUnitSystem κ (Algebra M))
    (h : E.algebra ≤ F.algebra) : E.concreteAlgebra ≤ F.concreteAlgebra := by
  intro x hx
  let a : Algebra M := ⟨x,E.concreteAlgebra_le hx⟩
  exact (F.mem_concreteAlgebra a).mpr (h ((E.mem_concreteAlgebra a).mp hx))

private theorem matrix_relative_commutes (E : FiniteMatrixStage M)
    (F : FiniteMatrixStage E.units.relativeVonNeumann) :
    ∀ i j k l, Commute (E.units.entry i j)
      ((F.units.map (StarSubalgebra.inclusion E.units.relativeVonNeumann_le)).entry k l) := by
  intro i j k l
  apply Subtype.ext
  exact ((E.units.relativeStar_mem _).mp (F.units.entry k l).property).2 i j

def relativeMatrixExtension (E : FiniteMatrixStage M)
    (F : FiniteMatrixStage E.units.relativeVonNeumann) : FiniteMatrixStage M := by
  classical
  let I := Fin E.size × Fin F.size
  let : Nonempty I := ⟨⟨⟨0,E.positive⟩,⟨0,F.positive⟩⟩⟩
  let G := F.units.map (StarSubalgebra.inclusion E.units.relativeVonNeumann_le)
  let P := E.units.product G (matrix_relative_commutes E F)
  exact ⟨Fintype.card I,Fintype.card_pos,P.reindex (Fintype.equivFin I).symm⟩

theorem relativeMatrixExtension_algebra (E : FiniteMatrixStage M)
    (F : FiniteMatrixStage E.units.relativeVonNeumann) :
    (relativeMatrixExtension E F).units.algebra =
      E.units.algebra ⊔
        (F.units.map (StarSubalgebra.inclusion E.units.relativeVonNeumann_le)).algebra := by
  classical
  exact ((E.units.product _ (matrix_relative_commutes E F)).reindex_algebra
    (Fintype.equivFin (Fin E.size × Fin F.size)).symm).trans
      (E.units.product_algebra_eq_sup _ (matrix_relative_commutes E F))

theorem relativeMatrixExtension_contains_left (E : FiniteMatrixStage M)
    (F : FiniteMatrixStage E.units.relativeVonNeumann) :
    E.units.concreteAlgebra ≤ (relativeMatrixExtension E F).units.concreteAlgebra := by
  apply matrix_concrete_mono
  rw [relativeMatrixExtension_algebra]
  exact le_sup_left

theorem relativeMatrixExtension_contains_right (E : FiniteMatrixStage M)
    (F : FiniteMatrixStage E.units.relativeVonNeumann) :
    F.units.concreteAlgebra ≤ (relativeMatrixExtension E F).units.concreteAlgebra := by
  intro x hx
  obtain ⟨a,ha⟩ := hx
  change F.units.concreteHom a = x at ha
  let f := StarSubalgebra.inclusion E.units.relativeVonNeumann_le
  let G := F.units.map f
  have he : G.concreteHom a = F.units.concreteHom a := by
    change M.toStarSubalgebra.subtype (∑ i, ∑ j, a i j • f (F.units.entry i j)) =
      E.units.relativeVonNeumann.toStarSubalgebra.subtype (∑ i, ∑ j, a i j • F.units.entry i j)
    simp only [map_sum,map_smul]
    rfl
  have hm : G.concreteHom a ∈ G.concreteAlgebra := ⟨a,rfl⟩
  rw [he,ha] at hm
  apply matrix_concrete_mono G (relativeMatrixExtension E F).units ?_ hm
  rw [relativeMatrixExtension_algebra]
  exact le_sup_right

theorem TypeIIIFactor.exists_matrixStage_extension_containing_projection
    [TopologicalSpace.SeparableSpace H] (hM : TypeIIIFactor M) (E : FiniteMatrixStage M)
    (p : AlgebraProjection E.units.relativeVonNeumann) :
    ∃ F : FiniteMatrixStage M, E.units.concreteAlgebra ≤ F.units.concreteAlgebra ∧
      p.val.val ∈ F.units.concreteAlgebra := by
  obtain ⟨G,hG⟩ := (hM.relative_matrix E).exists_matrixStage_containing_projection p
  exact ⟨relativeMatrixExtension E G,relativeMatrixExtension_contains_left E G,
    relativeMatrixExtension_contains_right E G hG⟩

end

end KadisonKastler

end OAI
