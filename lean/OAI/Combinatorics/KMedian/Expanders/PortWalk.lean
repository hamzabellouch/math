import Mathlib

namespace OAI

section Inline_PCPPortWalk

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

structure PortGraph (V D : Type) where
  rotate : V × D ≃ V × D
  involutive : Function.Involutive rotate

namespace PortGraph
variable {V D : Type} (G : PortGraph V D)
def step (v : V) (d : D) : V := (G.rotate (v,d)).1
def back (v : V) (d : D) : D := (G.rotate (v,d)).2

@[simp] theorem rotate_step_back (v : V) (d : D) :
    G.rotate (G.step v d, G.back v d) = (v,d) := G.involutive (v,d)
@[simp] theorem step_back (v : V) (d : D) :
    G.step (G.step v d) (G.back v d) = v := congrArg Prod.fst (G.rotate_step_back v d)
@[simp] theorem back_back (v : V) (d : D) :
    G.back (G.step v d) (G.back v d) = d := congrArg Prod.snd (G.rotate_step_back v d)

def trace : (n : ℕ) → V → (Fin n → D) → Fin (n+1) → V
  | 0, v, _ => fun _ => v
  | n+1, v, c => Fin.cases v (trace n (G.step v (c 0)) (fun i => c i.succ))

@[simp] theorem trace_zero (n : ℕ) (v : V) (c : Fin n → D) : G.trace n v c 0 = v := by
  cases n <;> rfl

@[simp] theorem trace_succ (n : ℕ) (v : V) (c : Fin (n+1) → D) (i : Fin (n+1)) :
    G.trace (n+1) v c i.succ = G.trace n (G.step v (c 0)) (fun j => c j.succ) i := rfl

theorem trace_chain (n : ℕ) (v : V) (c : Fin n → D) (i : Fin n) :
    G.step (G.trace n v c i.castSucc) (c i) = G.trace n v c i.succ := by
  induction n generalizing v with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change G.step v (c 0) = G.trace n (G.step v (c 0)) (fun k => c k.succ) 0
      exact (G.trace_zero n _ _).symm
    · simpa only [Fin.castSucc_succ, trace_succ] using
        ih (G.step v (c 0)) (fun k => c k.succ) j

structure Walk (n : ℕ) where
  vertex : Fin (n+1) → V
  port : Fin n → D
  chain : ∀ i, G.step (vertex i.castSucc) (port i) = vertex i.succ

namespace Walk
variable {G} {n : ℕ}
@[ext] theorem ext {p q : G.Walk n} (hv : p.vertex = q.vertex) (hp : p.port = q.port) : p = q := by
  cases p; cases q; cases hv; cases hp; rfl

theorem vertex_eq_trace (p : G.Walk n) :
    p.vertex = G.trace n (p.vertex 0) p.port := by
  funext i
  induction i using Fin.induction with
  | zero => simp
  | succ i hi =>
    rw [← p.chain i, ← G.trace_chain n (p.vertex 0) p.port i, hi]

def ofWord (v : V) (c : Fin n → D) : G.Walk n :=
  ⟨G.trace n v c, c, G.trace_chain n v c⟩

def wordEquiv : G.Walk n ≃ V × (Fin n → D) where
  toFun p := (p.vertex 0, p.port)
  invFun p := ofWord p.1 p.2
  left_inv p := by
    apply Walk.ext
    · exact p.vertex_eq_trace.symm
    · rfl
  right_inv p := by simp [ofWord]

instance [Fintype V] [Fintype D] : Fintype (G.Walk n) := Fintype.ofEquiv _ wordEquiv.symm

theorem card [Fintype V] [Fintype D] : Fintype.card (G.Walk n) =
    Fintype.card V * Fintype.card D ^ n := by
  rw [Fintype.card_congr (wordEquiv (G := G) (n := n))]
  simp

def reverse (p : G.Walk n) : G.Walk n where
  vertex i := p.vertex i.rev
  port i := G.back (p.vertex i.rev.castSucc) (p.port i.rev)
  chain i := by
    have h := p.chain i.rev
    rw [Fin.rev_castSucc, Fin.rev_succ]
    rw [← h]
    exact G.step_back _ _

@[simp] theorem reverse_reverse (p : G.Walk n) : p.reverse.reverse = p := by
  apply Walk.ext
  · funext i
    simp [reverse]
  · funext i
    simp only [reverse, Fin.rev_rev, Fin.rev_castSucc]
    rw [← p.chain i]
    exact G.back_back _ _

def reverseEquiv : G.Walk n ≃ G.Walk n :=
  ⟨reverse,reverse,reverse_reverse,reverse_reverse⟩

@[simp] theorem reverse_start (p : G.Walk n) : p.reverse.vertex 0 = p.vertex (Fin.last n) := by
  simp [reverse]

theorem reverse_expect [Fintype V] [Fintype D] (f : G.Walk n → ℝ) :
    (𝔼 p : G.Walk n, f p.reverse) = 𝔼 p : G.Walk n, f p :=
  Fintype.expect_equiv (reverseEquiv (G := G) (n := n)) _ _ (fun _ => rfl)

end Walk
end PortGraph
end MetricKMedian.PCP

end Inline_PCPPortWalk

end OAI
