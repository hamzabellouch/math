import Mathlib
import OAI.Combinatorics.KMedian.Expanders.PortWalk
import OAI.Combinatorics.KMedian.Machines.FiniteCases
import OAI.Combinatorics.KMedian.Machines.FiniteCoordinates

namespace OAI

section Inline_PCPRawWalk
namespace MetricKMedian.PCP.Compiler.RawWalk
open Binary Binary.Automatic
open scoped Classical

variable {T D A : Type} [Coding T] [Fintype D] [Coding D] [Hardcoded D] [Inhabited D]
variable (rotate : T → ℕ → D → ℕ × D)
variable (hp : Poly (fun p : (T × ℕ) × D => rotate p.1.1 p.1.2 p.2))
def port (cap : ℕ) (w : Fin cap → D) (n : ℕ) : D := if h:n<cap then w ⟨n,h⟩ else default
def vertexAt (cap : ℕ) (t:T) (v:ℕ) (w : Fin cap → D) : ℕ → ℕ
  | 0 => v
  | n+1 => (rotate t (vertexAt cap t v w n) (port cap w n)).1
include hp
omit [Hardcoded D] in
lemma poly_at (cap n : ℕ) : Poly (fun p : (T × ℕ) × (Fin cap → D) => vertexAt rotate cap p.1.1 p.1.2 p.2 n) := by
  induction n with
  | zero => exact Poly.snd.comp Poly.fst
  | succ n ih =>
    have hc : Poly (fun w : Fin cap → D => port cap w n) := hardcoded _
    exact Poly.fst.comp (hp.comp (Poly.pair (Poly.pair (Poly.fst.comp Poly.fst) ih) (hc.comp Poly.snd)))
omit [Hardcoded D] in
lemma poly_vertex (cap : ℕ) : Poly (fun p : ((T × ℕ) × (Fin cap → D)) × Fin (cap+1) =>
    vertexAt rotate cap p.1.1.1 p.1.1.2 p.1.2 p.2.val) := by
  have hf := poly_finite_cases (fun i : Fin (cap+1) => fun p : (T × ℕ) × (Fin cap → D) =>
    vertexAt rotate cap p.1.1 p.1.2 p.2 i.val) (fun i => poly_at rotate hp cap i.val)
  exact hf.comp (Poly.pair Poly.snd Poly.fst)
def backs (cap : ℕ) (t:T) (v:ℕ) (w : Fin cap → D) : Fin cap → D :=
  fun i => (rotate t (vertexAt rotate cap t v w i.val) (w i)).2
lemma poly_backs (cap : ℕ) : Poly (fun p : (T × ℕ) × (Fin cap → D) => backs rotate cap p.1.1 p.1.2 p.2) := by
  apply poly_coordinates
  intro i
  have hc : Poly (fun w : Fin cap → D => w i) := hardcoded _
  exact Poly.snd.comp (hp.comp (Poly.pair (Poly.pair (Poly.fst.comp Poly.fst) (poly_at rotate hp cap i.val))
    (hc.comp Poly.snd)))
omit hp
omit [Coding T] [Fintype D] [Coding D] [Hardcoded D]
variable {V : Type} (G : PortGraph V D) (code : V → ℕ)
lemma at_correct (t:T) (h : ∀ v d, rotate t (code v) d=(code (G.step v d),G.back v d))
    (cap : ℕ) (p : G.Walk cap) (n : ℕ) (hn : n≤cap) :
    vertexAt rotate cap t (code (p.vertex 0)) p.port n=code (p.vertex ⟨n,by omega⟩) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [vertexAt,ih (by omega)]
    simp only [port,dite_eq_left (by omega : n<cap)]
    rw [h]
    exact congrArg code (p.chain ⟨n,by omega⟩)
lemma backs_correct (t:T) (h : ∀ v d, rotate t (code v) d=(code (G.step v d),G.back v d))
    (cap : ℕ) (p : G.Walk cap) (i:Fin cap) :
    backs rotate cap t (code (p.vertex 0)) p.port i=G.back (p.vertex i.castSucc) (p.port i) := by
  unfold backs
  rw [at_correct rotate G code t h cap p i.val (Nat.le_of_lt i.isLt),h]
  rfl
end MetricKMedian.PCP.Compiler.RawWalk

end Inline_PCPRawWalk

end OAI
