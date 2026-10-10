import OAI.GroupTheory.PolycyclicRecognition.Geometry.CompactLieLaws
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BracketWords

namespace OAI

/-! # Generation persists in the compact normalized family

The word-normalization equations express a fixed vector-space basis as words
in the generators. They therefore imply Lie generation for every limiting law.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {V I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The recursively evaluated operation agrees with the Lie structure that
it defines. -/
theorem evalBilinearWord_eq_lieWord (B : V →L[ℝ] V →L[ℝ] V)
    (h : IsLieBracket B) (X : I → V) (w : FreeMagma I) :
    letI := lieRingOfBilinear B h
    letI := lieAlgebraOfBilinear B h
    evalBilinearWord B X w = evalBracketWord X w := by
  let := lieRingOfBilinear B h
  let := lieAlgebraOfBilinear B h
  induction w using FreeMagma.rec with
  | of i => rfl
  | mul a b ha hb => change B _ _ = B _ _; rw [ha, hb]

/-- Fixed basis-word identities prevent loss of generation in a limit. -/
theorem lieSpan_eq_top_of_word_basis (B : V →L[ℝ] V →L[ℝ] V)
    (h : IsLieBracket B) (X : I → V) (b : Basis J ℝ V) (w : J → FreeMagma I)
    (hw : ∀ j, evalBilinearWord B X (w j) = b j) :
    letI := lieRingOfBilinear B h
    letI := lieAlgebraOfBilinear B h
    LieSubalgebra.lieSpan ℝ V (Set.range X) = ⊤ := by
  let := lieRingOfBilinear B h
  let := lieAlgebraOfBilinear B h
  have hb (j : J) : b j ∈ LieSubalgebra.lieSpan ℝ V (Set.range X) := by
    rw [← hw j, evalBilinearWord_eq_lieWord B h]
    exact evalBracketWord_mem_lieSpan X (w j)
  have hspan : (⊤ : Submodule ℝ V) ≤
      (LieSubalgebra.lieSpan ℝ V (Set.range X)).toSubmodule := by
    rw [← b.span_eq]
    exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hb j)
  apply top_unique
  intro v _
  exact hspan (Submodule.mem_top)

end PolycyclicRecognition

end

end OAI
