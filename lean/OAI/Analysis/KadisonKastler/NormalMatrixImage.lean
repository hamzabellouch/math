import OAI.Analysis.KadisonKastler.NormalRepresentationRange
import OAI.Analysis.KadisonKastler.IncreasingMatrixPreparation
import OAI.Analysis.KadisonKastler.OriginalIrreducibleSubfactor

namespace OAI

/-! # Increasing matrix generators under the normal cyclic representation -/

namespace KadisonKastler

noncomputable section

open Generator

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H}
  (φ : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (A : ℕ → FiniteMatrixStage M)

def normalImageMatrixUnits (n : ℕ) : MatrixUnitSystem (Fin (A n).size) (K →L[ℂ] K) :=
  (A n).units.map φ

theorem normalImageMatrixUnits_mono
    (hA : Monotone (fun n => (A n).units.concreteAlgebra)) :
    Monotone (fun n => (normalImageMatrixUnits φ A n).algebra) := by
  intro i j hij T hT
  obtain ⟨a, rfl⟩ := hT
  have hai : ((A i).units.hom a).val ∈ (A i).units.concreteAlgebra :=
    ((A i).units.mem_concreteAlgebra _).mpr ⟨a, rfl⟩
  obtain ⟨b, hb⟩ := ((A j).units.mem_concreteAlgebra _).mp (hA hij hai)
  refine ⟨b, ?_⟩
  change ((A j).units.map φ).hom b = ((A i).units.map φ).hom a
  rw [mapped_matrixUnits_hom, mapped_matrixUnits_hom]
  exact congrArg φ hb

theorem normalImageMatrixUnits_generated (hφ : BoundedWeakNormal M φ)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (hgen : FiniteMatrixStage.generatedVonNeumann A = M) :
    generatedVonNeumannAlgebra (⨆ n, (normalImageMatrixUnits φ A n).algebra) =
      generatedVonNeumannAlgebra φ.range := by
  let P := generatedVonNeumannAlgebra (⨆ n, (normalImageMatrixUnits φ A n).algebra)
  apply le_antisymm
  · apply generatedVonNeumannAlgebra_le_of_le
    apply iSup_le
    intro n T hT
    obtain ⟨a, rfl⟩ := hT
    exact subset_generatedVonNeumannAlgebra _
      ⟨(A n).units.hom a, (mapped_matrixUnits_hom (A n).units φ a).symm⟩
  · apply generatedVonNeumannAlgebra_le_of_le
    rintro T ⟨a, rfl⟩
    have hBM : FiniteMatrixStage.stageUnion A ≤ M.toStarSubalgebra :=
      iSup_le fun n => (A n).units.concreteAlgebra_le
    have hMB : M ≤ generatedVonNeumannAlgebra (FiniteMatrixStage.stageUnion A) := by
      have he : FiniteMatrixStage.generatedVonNeumann A =
          generatedVonNeumannAlgebra (FiniteMatrixStage.stageUnion A) := by
        simpa only [matrixStageConcreteUnits_algebra, FiniteMatrixStage.stageUnion] using
          generated_matrixStages_eq A hA
      exact (hgen.symm.trans he).le
    apply boundedWeakNormal_maps_generated M φ hφ (FiniteMatrixStage.stageUnion A) hBM hMB P _ a
    intro b
    have hb : b.val ∈ (FiniteMatrixStage.stageUnion A : Set (H →L[ℂ] H)) := b.property
    rw [FiniteMatrixStage.stageUnion_coe A hA] at hb
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hb
    obtain ⟨c, hc⟩ := ((A n).units.mem_concreteAlgebra
      (⟨b.val, hBM b.property⟩ : Algebra M)).mp hn
    apply subset_generatedVonNeumannAlgebra
    apply (le_iSup (fun n => (normalImageMatrixUnits φ A n).algebra) n)
    refine ⟨c, ?_⟩
    change ((A n).units.map φ).hom c = φ ⟨b.val, hBM b.property⟩
    rw [mapped_matrixUnits_hom]
    exact congrArg φ hc

end

end KadisonKastler

end OAI
