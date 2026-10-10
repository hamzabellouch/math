import OAI.Dynamics.ConditionalShuffle.OverlayLaw

namespace OAI

noncomputable section
open scoped Classical
namespace Revealed.Color
open Thorp Thorp.Conditional Revealed.Overlay

def predictResample (d : ℕ) (M : (t : ℕ) → History (d+1) t → Position d → Bool) :
    (t : ℕ) → History (d+1) t → History (d+1) t → History (d+1) t
  | 0, _, _ => Fin.elim0
  | t+1, c, r => Fin.snoc (predictResample d M t (Fin.init c) (Fin.init r))
      (maskedCoin (M t (Fin.init c)) (c (Fin.last t)) (r (Fin.last t)))

def historyXor (d t : ℕ) (c : History (d+1) t) : Equiv.Perm (History (d+1) t) :=
  Function.Involutive.toPerm (fun r i x => c i x ^^ r i x) (by
    intro r; funext i x
    change (c i x ^^ (c i x ^^ r i x)) = r i x
    cases c i x <;> cases r i x <;> rfl)

lemma resample_xor (d : ℕ) (M : (t : ℕ) → History (d+1) t → Position d → Bool)
    (t : ℕ) (c r : History (d+1) t) :
    predictResample d M t c (historyXor d t c r) =
      predictableHistory d (fun k a _ => M k a) t c r := by
  induction t with
  | zero => exact Subsingleton.elim _ _
  | succ t ih =>
      rw [predictResample, predictableHistory]
      apply congrArg₂ Fin.snoc
      · exact ih (Fin.init c) (Fin.init r)
      · funext x
        change (if M t (Fin.init c) x then c (Fin.last t) x ^^ r (Fin.last t) x else c (Fin.last t) x) =
          (c (Fin.last t) x ^^ (if M t (Fin.init c) x then r (Fin.last t) x else false))
        cases M t (Fin.init c) x <;> simp

lemma predictResample_stationary (d : ℕ)
    (M : (t : ℕ) → History (d+1) t → Position d → Bool) (t : ℕ)
    (f : History (d+1) t → ℝ) :
    mean (fun c => mean (fun r => f (predictResample d M t c r))) = mean f := by
  calc
    _ = mean (fun c => mean (fun r => f (predictableHistory d (fun k a _ => M k a) t c r))) := by
      apply mean_congr; intro c
      have he := mean_equiv (historyXor d t c) (fun r => f (predictResample d M t c r))
      change mean (fun r => f (predictResample d M t c (historyXor d t c r))) = _ at he
      simp_rw [resample_xor] at he
      exact he.symm
    _ = mean (fun r => mean (fun c => f (predictableHistory d (fun k a _ => M k a) t c r))) := mean_comm _
    _ = mean (fun _ : History (d+1) t => mean f) := by
      apply mean_congr; intro r
      exact mean_equiv (predictableEquiv d (fun k a _ => M k a) t r) f
    _ = mean f := mean_const _

end Revealed.Color

end

end OAI
