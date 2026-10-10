import Mathlib
import OAI.Combinatorics.KMedian.Machines.Hardcoded

namespace OAI

section Inline_PCPBlendCompiler
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic

variable {X D S : Type} [Coding X] [Coding D] [Coding S]
noncomputable def blendProgram (f : X → D → ℕ × D) (g : X → S → ℕ × S)
    (x : X) (d : Fin 3 × D × S) : ℕ × (Fin 3 × D × S) :=
  if d.1=0 then
    let q := f x d.2.1
    (q.1,(d.1,(q.2,d.2.2)))
  else
    let q := g x d.2.2
    (q.1,(d.1,(d.2.1,q.2)))
lemma poly_blendProgram (f : X → D → ℕ × D) (g : X → S → ℕ × S)
    (hf : Poly (fun p : X × D => f p.1 p.2))
    (hg : Poly (fun p : X × S => g p.1 p.2)) :
    Poly (fun p : X × (Fin 3 × D × S) => blendProgram f g p.1 p.2) := by
  unfold blendProgram
  dsimp only
  apply Poly.ite_prop
  · exact (hardcoded (fun i : Fin 3 => decide (i=0))).comp (Poly.fst.comp Poly.snd)
  · have hp : Poly (fun x : X × (Fin 3 × D × S) => f x.1 x.2.2.1) :=
      hf.comp (Poly.pair Poly.fst (Poly.fst.comp (Poly.snd.comp Poly.snd)))
    exact Poly.pair (Poly.fst.comp hp) (Poly.pair (Poly.fst.comp Poly.snd)
      (Poly.pair (Poly.snd.comp hp) (Poly.snd.comp (Poly.snd.comp Poly.snd))))
  · have hp : Poly (fun x : X × (Fin 3 × D × S) => g x.1 x.2.2.2) :=
      hg.comp (Poly.pair Poly.fst (Poly.snd.comp (Poly.snd.comp Poly.snd)))
    exact Poly.pair (Poly.fst.comp hp) (Poly.pair (Poly.fst.comp Poly.snd)
      (Poly.pair (Poly.fst.comp (Poly.snd.comp Poly.snd)) (Poly.snd.comp hp)))
end MetricKMedian.PCP.Compiler

end Inline_PCPBlendCompiler

end OAI
