import Mathlib
import OAI.Combinatorics.KMedian.Machines.RawCSP
import OAI.Combinatorics.KMedian.Machines.RawWalk
import OAI.Combinatorics.KMedian.PCP.PathTable

namespace OAI

section Inline_PCPPowerPrograms
namespace MetricKMedian.PCP.Compiler.PowerProgram
open Binary Binary.Automatic
open scoped Classical

variable {T D A : Type} [Coding T] [Fintype D] [Coding D] [Hardcoded D] [Inhabited D]
  [Fintype A] [DecidableEq A] [Inhabited A]
variable (rot : T → ℕ → D → ℕ × D) (allow : T → ℕ → D → Finset (A × A))
variable (hr : Poly (fun s : (T × ℕ) × D => rot s.1.1 s.1.2 s.2))
  (ha : Poly (fun s : (T × ℕ) × D => allow s.1.1 s.1.2 s.2))
abbrev Tag (t cap : ℕ) := (Fin cap → Fin (t+1)) × (Fin cap → D)
noncomputable def stop (t cap : ℕ) (c : Fin cap → Fin (t+1)) : Fin (cap+1) :=
  ⟨Stopped.length t cap c, by have := Stopped.length_le t cap c; omega⟩
def rels (cap : ℕ) (s : T) (v : ℕ) (w : Fin cap → D) : Fin cap → Finset (A × A) :=
  fun i => allow s (RawWalk.vertexAt rot cap s v w i.val) (w i)
include hr ha in
omit [Hardcoded D] [DecidableEq A] [Inhabited A] in
lemma poly_rels (cap : ℕ) : Poly (fun p : (T × ℕ) × (Fin cap → D) => rels rot allow cap p.1.1 p.1.2 p.2) := by
  apply poly_coordinates
  intro i
  have hc : Poly (fun w : Fin cap → D => w i) := hardcoded _
  exact ha.comp (Poly.pair (Poly.pair (Poly.fst.comp Poly.fst) (RawWalk.poly_at rot hr cap i.val)) (hc.comp Poly.snd))
noncomputable def row (t cap : ℕ) (s:T) (v:ℕ) (tag:Tag (D := D) t cap) : CSPRow (Advice D A cap) :=
  (v,RawWalk.vertexAt rot cap s v tag.2 (stop t cap tag.1).val,
    relation cap (stop t cap tag.1) tag.2 (RawWalk.backs rot cap s v tag.2) (rels rot allow cap s v tag.2))
include hr ha in
omit [DecidableEq A] in
lemma poly_row (t cap : ℕ) : Poly (fun p : (T × ℕ) × Tag (D := D) t cap => row rot allow t cap p.1.1 p.1.2 p.2) := by
  have hs : Poly (fun c : Fin cap → Fin (t+1) => stop t cap c) := hardcoded _
  have hw : Poly (fun p : (T × ℕ) × Tag (D := D) t cap => (p.1,p.2.2)) := by fun_prop
  have hn := hs.comp (Poly.fst.comp Poly.snd : Poly (fun p : (T × ℕ) × Tag (D := D) t cap => p.2.1))
  have hv := (RawWalk.poly_vertex rot hr cap).comp (Poly.pair hw hn)
  have hb := (RawWalk.poly_backs rot hr cap).comp hw
  have hl := (poly_rels rot allow hr ha cap).comp hw
  have hc : Poly (fun q : (Fin (cap+1) × (Fin cap → D)) × ((Fin cap → D) × (Fin cap → Finset (A × A))) =>
    relation cap q.1.1 q.1.2 q.2.1 q.2.2) := hardcoded _
  have hrel := hc.comp (Poly.pair (Poly.pair hn (Poly.snd.comp Poly.snd)) (Poly.pair hb hl))
  exact Poly.pair (Poly.snd.comp Poly.fst) (Poly.pair hv hrel)
end MetricKMedian.PCP.Compiler.PowerProgram

end Inline_PCPPowerPrograms

end OAI
