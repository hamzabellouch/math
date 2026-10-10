import Mathlib
import OAI.Combinatorics.KMedianRecovery.Model
import OAI.Combinatorics.KMedianRecovery.Sampling.ExtractPrefix

namespace OAI

namespace MetricKMedianRecovery.BitMachine

noncomputable def PolyComputes.reencode {α β : Type} {f : α → β} {g : List Bool → List Bool}
    (h : PolyComputes g) (ea : α → List Bool) (eb : β → List Bool)
    (he : ∀ x, g (ea x) = eb (f x)) : Turing.TM2ComputableInPolyTime ea eb f where
  tm := h.program.machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := h.time
  outputsFun x := by simpa [he x] using h.outputs (ea x)

noncomputable def inputProjection : Turing.TM2ComputableInPolyTime pairBits id Prod.fst :=
  extractPrefix_computes.reencode pairBits id (fun p => extractPrefix_pair p.1 p.2)

noncomputable def randomProjection : Turing.TM2ComputableInPolyTime pairBits id Prod.snd :=
  discardPrefix_computes.reencode pairBits id (fun p => discardPrefix_pair p.1 p.2)

lemma pairBits_length (p : List Bool × List Bool) :
    (pairBits p).length = 2*p.1.length+1+p.2.length := by
  rcases p with ⟨x,y⟩
  induction x with
  | nil => simp [pairBits,Nat.add_comm]
  | cons b xs ih =>
    simp only [pairBits,List.flatMap_cons,List.cons_append,List.nil_append,List.length_cons] at ih ⊢
    omega

end MetricKMedianRecovery.BitMachine

end OAI
