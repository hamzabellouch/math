import Mathlib
import OAI.Computability.VertexCover.Fourier.SourceGame
import OAI.Computability.VertexCover.Fourier.SourceOccurrences

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

noncomputable section
namespace UniqueGames.Foundations.Hastad.SourceSoundness

open scoped BigOperators
open Target SourceContexts SourceOccurrences SourceGame

def leftTable (F : Formula) (u : ℕ) (bits : Fin (nBits F u) → Bool)
    (v : VariableContext F u) : HalfCube (leftAnchor u) → Bool :=
  fun h => bits ((proofEncoding F u).code (.inl (v, h.val)))

def rightOracle (F : Formula) (u : ℕ) (bits : Fin (nBits F u) → Bool)
    («c» : ClauseContext F u) : ConditionedOracle (validJ F «c») :=
  match h : rightAnchor F «c» with
  | none => .empty ((rightAnchor_none_iff F «c»).mp h)
  | some j₀ => .stored j₀
      (fun h => bits ((proofEncoding F u).code
        (.inr (.inl («c», extendRestricted (validJ F «c») h.val)))))

@[simp] theorem rightOracle_answer (F : Formula) (u : ℕ)
    (bits : Fin (nBits F u) → Bool) («c» : ClauseContext F u) :
    (rightOracle F u bits «c»).answer = rightResponse F u bits «c» := by
  unfold rightOracle
  split <;> simp_all [rightResponse, ConditionedOracle.answer]

@[simp] theorem leftTable_answer (F : Formula) (u : ℕ)
    (bits : Fin (nBits F u) → Bool) (v : VariableContext F u) :
    foldedAnswer (leftAnchor u) (leftTable F u bits v) = leftResponse F u bits v := rfl

theorem sourceList_sound (F : Formula) (hne : F.clauses ≠ []) (u D : ℕ)
    (hD : 0 < D) (hDtwo : 2 ≤ D) (δ : ℝ) (hδ : 0 ≤ δ)
    (hvalue : ((baseGame F hne).repetition u).value ≤
      4 * (D : ℝ)⁻¹ * δ ^ 2)
    (bits : Fin (nBits F u) → Bool) :
    ((sourceList F u D).countP (fun e => UniqueGames.Reduction.CloneGap.satisfied e bits) : ℝ) /
      (sourceList F u D).length ≤ (1 + δ) / 2 := by
  rw [sourceList_nonempty F u D hne, rawSourceList_acceptance F u D hD]
  have hε : (0 : ℝ) < (D : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hD)
  have hε' : (D : ℝ)⁻¹ ≤ (1 : ℝ) / 2 := by
    have hd : (2 : ℝ) ≤ D := by exact_mod_cast hDtwo
    simpa only [one_div] using
      (inv_le_inv₀ (Nat.cast_pos.mpr hD) (by norm_num : (0 : ℝ) < 2)).mpr hd
  have h := source_acceptance_le_split F hne u ((D : ℝ)⁻¹) δ
    (fun _ => leftAnchor u) (leftTable F u bits) (rightOracle F u bits)
    hε hε' hδ hvalue
  simpa only [leftTable_answer, rightOracle_answer] using h

theorem sourceList_sound_rat (F : Formula) (hne : F.clauses ≠ []) (u D : ℕ)
    (hD : 0 < D) (hDtwo : 2 ≤ D) (δ : ℚ) (hδ : 0 ≤ δ)
    (hvalue : ((baseGame F hne).repetition u).value ≤
      4 * (D : ℝ)⁻¹ * (δ : ℝ) ^ 2)
    (bits : Fin (nBits F u) → Bool) :
    ((sourceList F u D).countP (fun e => UniqueGames.Reduction.CloneGap.satisfied e bits) : ℚ) /
      (sourceList F u D).length ≤ (1 + δ) / 2 := by
  have h := sourceList_sound F hne u D hD hDtwo (δ : ℝ)
    (by exact_mod_cast hδ) hvalue bits
  apply (Rat.cast_le (K := ℝ)).mp
  push_cast
  exact h

end UniqueGames.Foundations.Hastad.SourceSoundness

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
