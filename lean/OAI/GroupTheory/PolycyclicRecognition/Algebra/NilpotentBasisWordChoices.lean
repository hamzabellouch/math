import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordBasisCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Algebra.WordExponents

namespace OAI

/-! # Finite word choices for the actual Cartan basis -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [LieRing.IsNilpotent L]

/-- A fixed linear basis supplies a finite generating alphabet. Nilpotence
and finite maximization supply all remaining word-chart choices. -/
theorem exists_nilpotent_basis_word_choices (b : Basis (Fin (finrank ℝ L)) ℝ L) :
    ∃ (d : ℕ) (β : WordBasisSelections (fun i => b i) (boundedBracketWords d)),
      lowerCentralSeries ℝ L L d = ⊥ ∧
      (∀ i : Fin (finrank ℝ L), FreeMagma.of i ∈ boundedBracketWords d) ∧
      IsMaximizingColumnBasis (wordListCoordinates (fun i => b i) (boundedBracketWords d) b)
        (fun w => bracketWordExponent (fun _ : Fin (finrank ℝ L) => 1) w) β.val := by
  classical
  obtain ⟨k, hk⟩ := LieModule.IsNilpotent.nilpotent ℝ L L
  have hd : lowerCentralSeries ℝ L L (k + 2) = ⊥ := by
    apply eq_bot_iff.mpr
    exact (antitone_lowerCentralSeries ℝ L L (by omega : k ≤ k + 2)).trans (by rw [hk])
  have hgen : LieSubalgebra.lieSpan ℝ L (Set.range fun i => b i) = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    exact LieSubalgebra.submodule_span_le_lieSpan
      (by rw [show Submodule.span ℝ (Set.range fun i => b i) = ⊤ from b.span_eq]; trivial)
  let : Nonempty (WordBasisSelections (fun i => b i) (boundedBracketWords (k + 2))) :=
    nonempty_wordBasisSelections (fun i => b i) hd hgen
  obtain ⟨β, hβ⟩ := exists_maximizing_wordBasis (fun i => b i) (boundedBracketWords (k + 2)) b
    (fun w => bracketWordExponent (fun _ : Fin (finrank ℝ L) => 1) w)
  refine ⟨k + 2, β, hd, ?_, hβ⟩
  intro i
  simp only [mem_boundedBracketWords, bracketWordDepth]
  omega

end PolycyclicRecognition

end

end OAI
