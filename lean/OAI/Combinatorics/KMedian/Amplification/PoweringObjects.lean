import Mathlib
import OAI.Combinatorics.KMedian.Expanders.WalkSegments

namespace OAI

section Inline_PCPPoweringObjects

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph.Walk
variable {V D : Type} {G : PortGraph V D} {n : ℕ}

@[simp] theorem reverse_end (p : G.Walk n) : p.reverse.vertex (Fin.last n) = p.vertex 0 := by
  simp [reverse]

def centerEquiv (n m : ℕ) : G.Walk (n+(m+1)) ≃ (V × (Fin n → D)) × (D × (Fin m → D)) :=
  (splitEquiv n (m+1)).trans (Equiv.prodCongr
    ((reverseEquiv (G := G) (n := n)).trans wordEquiv)
    (Fin.consEquiv (fun _ : Fin (m+1) => D)).symm)

@[simp] theorem center_vertex (n m : ℕ) (p : G.Walk (n+(m+1))) :
    (centerEquiv n m p).1.1 = p.vertex ⟨n,by omega⟩ := by
  simp [centerEquiv, splitEquiv, reverseEquiv, wordEquiv, segment, reverse]

@[simp] theorem center_port (n m : ℕ) (p : G.Walk (n+(m+1))) :
    (centerEquiv n m p).2.1 = p.port ⟨n,by omega⟩ := by
  simp [centerEquiv, splitEquiv, Fin.consEquiv, segment]

@[simp] theorem center_left_end (n m : ℕ) (s : (V × (Fin n → D)) × (D × (Fin m → D))) :
    ((centerEquiv (G := G) n m).symm s).vertex 0 =
      (ofWord (G := G) s.1.1 s.1.2).vertex (Fin.last n) := by
  simp [centerEquiv, splitEquiv, reverseEquiv, wordEquiv]

@[simp] theorem center_right_end (n m : ℕ) (s : (V × (Fin n → D)) × (D × (Fin m → D))) :
    ((centerEquiv (G := G) n m).symm s).vertex (Fin.last (n+(m+1))) =
      (ofWord (G := G) (G.step s.1.1 s.2.1) s.2.2).vertex (Fin.last m) := by
  change ((ofWord (G := G) s.1.1 s.1.2).reverse.concat
    (ofWord ((ofWord (G := G) s.1.1 s.1.2).reverse.vertex (Fin.last n))
      (Fin.cons s.2.1 s.2.2)) (by simp [ofWord])).vertex (Fin.last (n+(m+1))) = _
  rw [concat_end, reverse_end]
  change G.trace (m+1) (G.trace n s.1.1 s.1.2 0)
    (Fin.cons s.2.1 s.2.2) (Fin.last m).succ = _
  simp only [PortGraph.trace_zero, PortGraph.trace_succ, Fin.cons_zero, Fin.cons_succ]
  rfl

end PortGraph.Walk

structure PortCSP {V D : Type} (G : PortGraph V D) (A : Type) where
  allowed : V × D → Finset (A × A)
  symmetric : ∀ p a b, (a,b) ∈ allowed (G.rotate p) ↔ (b,a) ∈ allowed p

namespace PortCSP
variable {V D A : Type} {G : PortGraph V D}
variable [DecidableEq A] (C : PortCSP G A)

def Satisfies (x : V → A) : Prop := ∀ v d, (x v,x (G.step v d)) ∈ C.allowed (v,d)
def Bad (x : V → A) (p : V × D) : Prop := (x p.1,x (G.step p.1 p.2)) ∉ C.allowed p

instance badDecidable (x : V → A) : DecidablePred (C.Bad x) := fun _ => inferInstanceAs (Decidable (_ ∉ _))

omit [DecidableEq A] in
theorem bad_symmetric (x : V → A) (p : V × D) : C.Bad x (G.rotate p) ↔ C.Bad x p := by
  unfold Bad
  change (x (G.step p.1 p.2),x (G.step (G.step p.1 p.2) (G.back p.1 p.2))) ∉
    C.allowed (G.rotate p) ↔ _
  rw [G.step_back,C.symmetric]

end PortCSP

abbrev Advice (D A : Type) (cap : ℕ) := (n : Fin (cap+1)) → (Fin n.val → D) → A

namespace Advice
variable {D A : Type} {cap : ℕ}
variable [Inhabited A]

def get (a : Advice D A cap) (n : ℕ) (c : Fin n → D) : A :=
  if h : n ≤ cap then a ⟨n,by omega⟩ c else default

@[simp] theorem get_le (a : Advice D A cap) (n : ℕ) (c : Fin n → D) (h : n ≤ cap) :
    a.get n c = a ⟨n,by omega⟩ c := by simp [get,h]

end Advice

namespace PortGraph
variable {V D A : Type} {cap : ℕ} (G : PortGraph V D) [Inhabited A]

def honest (x : V → A) (v : V) : Advice D A cap :=
  fun n c => x (G.trace n.val v c (Fin.last n.val))

def opinion (a : V → Advice D A cap) (n : ℕ) (v : V) (c : Fin n → D) : A :=
  (a ((Walk.ofWord (G := G) v c).vertex (Fin.last n))).get n (Walk.ofWord (G := G) v c).reverse.port

theorem honest_opinion (x : V → A) (n : ℕ) (hn : n ≤ cap) (v : V) (c : Fin n → D) :
    G.opinion (G.honest x : V → Advice D A cap) n v c = x v := by
  unfold opinion
  rw [Advice.get_le _ _ _ hn]
  change x (G.trace n ((Walk.ofWord (G := G) v c).vertex (Fin.last n))
    (Walk.ofWord (G := G) v c).reverse.port (Fin.last n)) = x v
  have hp := Walk.vertex_eq_trace (Walk.ofWord (G := G) v c).reverse
  have hs : (Walk.ofWord (G := G) v c).reverse.vertex 0 =
      (Walk.ofWord (G := G) v c).vertex (Fin.last n) := Walk.reverse_start _
  rw [← hs, ← hp, Walk.reverse_end]
  simp [Walk.ofWord]

end PortGraph
end MetricKMedian.PCP

end Inline_PCPPoweringObjects

end OAI
