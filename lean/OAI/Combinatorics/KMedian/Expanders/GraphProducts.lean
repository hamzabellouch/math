import Mathlib
import OAI.Combinatorics.KMedian.Expanders.SpectralWalk

namespace OAI

section Inline_PCPGraphProducts

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph
variable {V D S : Type}

def squareRotate (G : PortGraph V D) (p : V × (D × D)) : V × (D × D) :=
  (G.step (G.step p.1 p.2.1) p.2.2,
   (G.back (G.step p.1 p.2.1) p.2.2,G.back p.1 p.2.1))

lemma squareRotate_involutive (G : PortGraph V D) : Function.Involutive (squareRotate G) := by
  rintro ⟨v,d,e⟩
  simp only [squareRotate,step_back,back_back]

def square (G : PortGraph V D) : PortGraph V (D × D) where
  rotate := { toFun := squareRotate G
              invFun := squareRotate G
              left_inv := squareRotate_involutive G
              right_inv := squareRotate_involutive G }
  involutive := squareRotate_involutive G

@[simp] lemma square_step (G : PortGraph V D) (v : V) (de : D × D) :
    G.square.step v de=G.step (G.step v de.1) de.2 := rfl

variable [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]

omit [Fintype V] [Nonempty V] [Nonempty D] in
lemma square_adjacency (G : PortGraph V D) (f : V → ℝ) :
    G.square.adjacency f=G.adjacency (G.adjacency f) := by
  funext v
  unfold adjacency
  simp_rw [square_step]
  exact expect_prod _

omit [Nonempty V] in
theorem square_contracts (G : PortGraph V D) {ρ : ℝ} (h : G.Contracts ρ) :
    G.square.Contracts (ρ^2) := by
  intro f hf
  rw [square_adjacency]
  have hh := G.propagate_contract h 2 f hf
  simpa only [propagate_succ,propagate_zero,show 2*2=4 by decide,← pow_mul] using hh

def zigzagRotate (G : PortGraph V D) (H : PortGraph D S)
    (p : (V × D) × (S × S)) : (V × D) × (S × S) :=
  ((G.step p.1.1 (H.step p.1.2 p.2.1),
    H.step (G.back p.1.1 (H.step p.1.2 p.2.1)) p.2.2),
   (H.back (G.back p.1.1 (H.step p.1.2 p.2.1)) p.2.2,H.back p.1.2 p.2.1))

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]

lemma zigzagRotate_involutive (G : PortGraph V D) (H : PortGraph D S) :
    Function.Involutive (zigzagRotate G H) := by
  rintro ⟨⟨v,d⟩,s,t⟩
  simp only [zigzagRotate,step_back,back_back]

def zigzag (G : PortGraph V D) (H : PortGraph D S) : PortGraph (V × D) (S × S) where
  rotate := { toFun := zigzagRotate G H
              invFun := zigzagRotate G H
              left_inv := zigzagRotate_involutive G H
              right_inv := zigzagRotate_involutive G H }
  involutive := zigzagRotate_involutive G H

@[simp] lemma zigzag_step (G : PortGraph V D) (H : PortGraph D S) (v : V × D) (s : S × S) :
    (G.zigzag H).step v s=(G.step v.1 (H.step v.2 s.1),
      H.step (G.back v.1 (H.step v.2 s.1)) s.2) := rfl

variable [Fintype S] [Nonempty S]

noncomputable def cloud (H : PortGraph D S) (f : V × D → ℝ) : V × D → ℝ :=
  fun p => H.adjacency (fun d => f (p.1,d)) p.2
noncomputable def permute (G : PortGraph V D) (f : V × D → ℝ) : V × D → ℝ :=
  fun p => f (G.rotate p)

omit [Nonempty S] in
lemma zigzag_adjacency (G : PortGraph V D) (H : PortGraph D S) (f : V × D → ℝ) :
    (G.zigzag H).adjacency f=cloud H (permute G (cloud H f)) := by
  funext p
  unfold adjacency cloud permute
  simp_rw [zigzag_step]
  rw [expect_prod]
  rfl

end PortGraph
end MetricKMedian.PCP

end Inline_PCPGraphProducts

end OAI
