import Mathlib
import OAI.Analysis.RecorderRadix.Tape
import OAI.Computability.SolenoidalRecorder.Checkpoints

namespace OAI

/-! Exact rational radix coordinates of the initialized recorder. -/

namespace Solenoidal
namespace Bridge
variable {M : Machine}
def blankLetter (M : Machine) : Recorder.Letter M := ⟨M.blank, .empty, false⟩

 

theorem initial_tape_left (w : List M.Symbol) (k : ℤ) (hk : k < 0) :
    (Recorder.initial w 2).tape k = blankLetter M := by
  have hk₂ : k ≠ 2 := by omega
  simp [Recorder.initial, Recorder.checkpoint, Recorder.tracks, Machine.inputTape,
    Recorder.initialHistory, hk₂, not_le.mpr hk, blankLetter]

theorem initial_tape_right (w : List M.Symbol) (k : ℤ)
    (hk : ((max w.length 3 : ℕ) : ℤ) ≤ k) :
    (Recorder.initial w 2).tape k = blankLetter M := by
  have hk₀ : 0 ≤ k := by omega
  have hk₂ : k ≠ 2 := by omega
  have hlen : w.length ≤ k.toNat := by omega
  have hw : w[k.toNat]? = none := by simp [List.getElem?_eq_none hlen]
  simp [Recorder.initial, Recorder.checkpoint, Recorder.tracks, Machine.inputTape,
    Recorder.initialHistory, hk₂, hk₀, hw, blankLetter]

 

def initialRadixRational {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1))
    (w : List M.Symbol) : ℚ × ℚ :=
  let t : ℤ → Fin (m + 1) := fun k => e ((Recorder.initial w 2).tape k)
  (Radix.finiteCode (Radix.leftStack t 0) (e (blankLetter M)) 0,
    Radix.finiteCode (Radix.rightStack t 0) (e (blankLetter M)) (max w.length 3))

theorem initial_radix_is_rational {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1))
    (w : List M.Symbol) :
    Radix.tapeCode (fun k => e ((Recorder.initial w 2).tape k)) 0 =
      (((initialRadixRational e w).1 : ℝ), ((initialRadixRational e w).2 : ℝ)) := by
  apply Prod.ext
  · apply Radix.code_is_finiteCode
    intro j _
    change e ((Recorder.initial w 2).tape (0 - ((j : ℤ) + 1))) = _
    rw [initial_tape_left w _ (by omega)]
  · apply Radix.code_is_finiteCode
    intro j hj
    change e ((Recorder.initial w 2).tape (0 + (j : ℤ))) = _
    rw [initial_tape_right w _ (by omega)]
end Bridge
end Solenoidal

end OAI
