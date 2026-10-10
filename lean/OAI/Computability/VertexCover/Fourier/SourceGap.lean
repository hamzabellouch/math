import Mathlib
import OAI.Computability.VertexCover.Fourier.SourceSoundness
import OAI.Computability.VertexCover.Fourier.SourceHonest
import OAI.Computability.VertexCover.Fourier.SourceBounds
import OAI.Computability.VertexCover.PCP.SourceParameters

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                     
section

namespace UniqueGames.Foundations.Hastad.SourceGap

open Target SourceContexts SourceOccurrences SourceGame
open UniqueGames.Integration.SourceParameters
open UniqueGames.Reduction

def ClauseGap (F : Formula) (η : ℚ) : Prop :=
  F.clauses ≠ [] ∧ ∀ assignment : Fin F.«variables» → Bool,
    (η : ℝ) * F.clauses.length ≤
      (PCP.failureCount F assignment (PCP.allIndices F) : ℝ)

theorem third_pos {η : ℚ} (hη : 0 < η) : 0 < η / 3 := by positivity

theorem third_le_one {η : ℚ} (hη : η ≤ 1) : η / 3 ≤ 1 := by linarith

def repetitionCount (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (D : ℕ) (hD : 0 < D) : ℕ :=
  repetitionLength (η / 3) ξ (third_pos hη) (third_le_one hη1) hξ D hD

theorem repetitionCount_pos (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hξ : 0 < ξ) (D : ℕ) (hD : 0 < D) :
    0 < repetitionCount η ξ hη hη1 hξ D hD :=
  (repetitionLength_spec (η / 3) ξ (third_pos hη) (third_le_one hη1) hξ D hD).1

theorem repeated_game_bound (F : Formula) (η ξ : ℚ)
    (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ) (D : ℕ) (hD : 0 < D)
    (hgap : ClauseGap F η) :
    ((baseGame F hgap.1).repetition
      (repetitionCount η ξ hη hη1 hξ D hD)).value ≤
        4 * (D : ℝ)⁻¹ * (ξ : ℝ)^2 := by
  have hb : (baseGame F hgap.1).value ≤ 1 - ((η / 3 : ℚ) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      base_value_le_of_clause_gap F hgap.1 (η : ℝ) hgap.2
  have hc : Fintype.card Bool * Fintype.card PCP.ClauseAnswer = 16 := by
    simp
  exact (game_repetition_rate (baseGame F hgap.1) (third_pos hη)
    (third_le_one hη1) hc hb _).trans
      (repetitionLength_real_bound (η / 3) ξ (third_pos hη)
        (third_le_one hη1) hξ D hD)

def source (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (D : ℕ) (hD : 0 < D) (F : Formula) : SourceEncoding.Input :=
  sourceInput F (repetitionCount η ξ hη hη1 hξ D hD) D hD

theorem source_complete (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (D : ℕ) (hD : 0 < D) (hnoise : (D : ℚ)⁻¹ ≤ ξ)
    (F : Formula) (hF : F.Satisfiable) :
    ∃ bits : Fin (source η ξ hη hη1 hξ D hD F).«variables» → Bool,
      1 - ξ ≤ (((source η ξ hη hη1 hξ D hD F).equations.countP
        (fun e => CloneGap.satisfied e bits) : ℚ) /
          (source η ξ hη hη1 hξ D hD F).equations.length) := by
  obtain ⟨assignment, hs⟩ := hF
  refine ⟨SourceHonest.honestBits F _ assignment, ?_⟩
  have h := SourceHonest.sourceList_honest_acceptance_rat F
    (repetitionCount η ξ hη hη1 hξ D hD) D hD assignment hs
  exact (sub_le_sub_left hnoise 1).trans h

theorem source_sound (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (D : ℕ) (hD : 0 < D) (hDtwo : 2 ≤ D)
    (F : Formula) (hgap : ClauseGap F η)
    (bits : Fin (source η ξ hη hη1 hξ D hD F).«variables» → Bool) :
    ((source η ξ hη hη1 hξ D hD F).equations.countP
      (fun e => CloneGap.satisfied e bits) : ℚ) /
        (source η ξ hη hη1 hξ D hD F).equations.length ≤ (1 + ξ) / 2 :=
  SourceSoundness.sourceList_sound_rat F hgap.1
    (repetitionCount η ξ hη hη1 hξ D hD) D hD hDtwo ξ hξ.le
      (repeated_game_bound F η ξ hη hη1 hξ D hD hgap) bits

theorem source_size (η ξ : ℚ) (hη : 0 < η) (hη1 : η ≤ 1) (hξ : 0 < ξ)
    (D : ℕ) (hD : 0 < D) :
    ∃ p : Polynomial ℕ, ∀ F : Formula,
      (SourceEncoding.inputBits (source η ξ hη hη1 hξ D hD F)).length ≤
        p.eval (Complexity.formulaBits F).length :=
  SourceBounds.fixed_parameters_source_size (repetitionCount η ξ hη hη1 hξ D hD) D hD

end UniqueGames.Foundations.Hastad.SourceGap

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
