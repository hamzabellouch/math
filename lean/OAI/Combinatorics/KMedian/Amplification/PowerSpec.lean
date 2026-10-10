import Mathlib
import OAI.Combinatorics.KMedian.Amplification.PowerPrograms

namespace OAI

section Inline_PCPPowerSpec
namespace MetricKMedian.PCP.Compiler.PowerProgram
open Binary Binary.Automatic
open scoped Classical

variable {V D A T : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
  [Inhabited D] [Fintype A] [Inhabited A] [DecidableEq A] [Coding T] [Coding D] [Hardcoded D]
variable {G : PortGraph V D} (C : PortCSP G A)
def edgeEquiv (t cap : ℕ) : V × Tag (D := D) t cap ≃ PortCSP.PowerEdge (G := G) t cap where
  toFun z := (z.2.1,PortGraph.Walk.ofWord z.1 z.2.2)
  invFun z := (z.2.vertex 0,(z.1,z.2.port))
  left_inv z := by simp only [PortGraph.Walk.ofWord,PortGraph.trace_zero]
  right_inv z := by
    apply Prod.ext
    · rfl
    · exact PortGraph.Walk.wordEquiv.symm_apply_apply z.2
variable (rot : T → ℕ → D → ℕ × D) (allow : T → ℕ → D → Finset (A × A))
  (code : V → ℕ) (s : T)
omit [Fintype V] [Nonempty V] [Nonempty D] [DecidableEq A] [Coding T] [Coding D]
  [Hardcoded D] in
lemma row_correct (hr : ∀ v d, rot s (code v) d=(code (G.step v d),G.back v d))
    (ha : ∀ v d, allow s (code v) d=C.allowed (v,d))
    (t cap : ℕ) (z : PortCSP.PowerEdge (G := G) t cap) :
    row rot allow t cap s (code (z.2.vertex 0)) (z.1,z.2.port)=
      (code ((C.powered (cap := cap) t).left z),code ((C.powered (cap := cap) t).right z),
        (C.powered (cap := cap) t).allowed z) := by
  unfold row
  rw [RawWalk.at_correct rot G code s hr]
  · have hb : RawWalk.backs rot cap s (code (z.2.vertex 0)) z.2.port=
        fun i => G.back (z.2.vertex i.castSucc) (z.2.port i) := by
      funext i
      exact RawWalk.backs_correct rot G code s hr cap z.2 i
    have hl : rels rot allow cap s (code (z.2.vertex 0)) z.2.port=
        fun i => C.allowed (z.2.vertex i.castSucc,z.2.port i) := by
      funext i
      unfold rels
      rw [RawWalk.at_correct rot G code s hr cap z.2 i.val (Nat.le_of_lt i.isLt),ha]
      rfl
    rw [hb,hl,relation_correct C cap z.2 (stop t cap z.1)]
    simp only [PortCSP.powered,PortCSP.stoppedPath,stop,PortGraph.Walk.segment,Nat.zero_add,Fin.val_zero,Fin.val_last]
    rfl
  · exact Nat.le_of_lt_succ (stop t cap z.1).isLt
end MetricKMedian.PCP.Compiler.PowerProgram

end Inline_PCPPowerSpec

end OAI
