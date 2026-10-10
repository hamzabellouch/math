import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.Interior

namespace OAI

/-! Parallel copies. -/

section

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical
variable {n m : ℕ}

abbrev Copy (a : Fin m → ℕ) := Σe, Fin (a e)

def copyEquiv (a : Fin m → ℕ) : Copy a ≃ Fin (Fintype.card (Copy a)) := Fintype.equivFin _

def copyProjection (a : Fin m → ℕ) (f : Fin (Fintype.card (Copy a))) : Fin m :=
  ((copyEquiv a).symm f).1

def copies (G : MultiGraph n m) (a : Fin m → ℕ) : MultiGraph n (Fintype.card (Copy a)) where
  left f := G.left (copyProjection a f)
  right f := G.right (copyProjection a f)
  loopless f := G.loopless (copyProjection a f)

lemma sum_copies (a : Fin m → ℕ) (f : Fin m → ℝ) :
    (∑j : Fin (Fintype.card (Copy a)), f (copyProjection a j))=∑e, (a e:ℝ)*f e := by
  rw [←(copyEquiv a).sum_comp]
  simp [copyProjection,Fintype.sum_sigma,nsmul_eq_mul]

lemma fiber_copies (a : Fin m → ℕ) (e : Fin m) :
    (∑_copy ∈ univ.filter (fun f => copyProjection a f=e), (1:ℝ))=a e := by
  rw [sum_filter]
  simpa using sum_copies a (fun e' => if e'=e then (1:ℝ) else 0)

lemma capacity_unit (G : MultiGraph n m) (p : Setoid (Fin n)) :
    capacity G.left G.right (fun _ => 1) p=(Partitions.crossing G p).card := by
  rw [capacity_eq_sum]
  simp

lemma capacity_copies (G : MultiGraph n m) (a : Fin m → ℕ) (p : Setoid (Fin n)) :
    ((Partitions.crossing (copies G a) p).card:ℝ)=
      capacity G.left G.right (fun e => a e) p := by
  rw [←capacity_unit]
  simp only [capacity,one_mul,copies]
  exact sum_copies a (fun e => crossingIndicator p (G.left e) (G.right e))

lemma partCount_ker (p : Fin n → Fin n) : partCount (Setoid.ker p)=partitionSize p := by
  let f : Quotient (Setoid.ker p) → (univ.image p : Finset (Fin n)) :=
    Quotient.lift (fun v => ⟨p v,mem_image.mpr ⟨v,mem_univ _,rfl⟩⟩)
      (fun a b h => Subtype.ext h)
  have hf : Function.Bijective f := by
    constructor
    · intro a b
      induction a,b using Quotient.inductionOn₂ with
      | h a b =>
        intro he
        exact Quotient.sound (congrArg Subtype.val he)
    · intro A
      obtain ⟨v,_,hv⟩ := mem_image.mp A.property
      exact ⟨Quotient.mk (Setoid.ker p) v,Subtype.ext hv⟩
  exact (Fintype.card_congr (Equiv.ofBijective f hf)).trans (Fintype.card_coe _)

lemma crossing_ker (G : MultiGraph n m) (p : Fin n → Fin n) :
    Partitions.crossing G (Setoid.ker p)=G.crossing univ p := by
  ext e
  simp [Partitions.crossing,MultiGraph.crossing]

lemma packing_of_partitions (G : MultiGraph n m) (hn : 0 < n) {r : ℕ} (hr : 0 < r)
    (hp : ∀p : Setoid (Fin n), (r:ℝ)*((partCount p:ℝ)-1) ≤
      capacity G.left G.right (fun _ => 1) p) : G.TreePackable univ r := by
  apply G.partition_criterion_sufficient univ hr hn
  intro p
  have h := hp (Setoid.ker p)
  rw [capacity_unit,crossing_ker,partCount_ker] at h
  have hp0 : 1 ≤ partitionSize p := by
    apply card_pos.mpr
    exact ⟨p ⟨0,hn⟩,mem_image.mpr ⟨⟨0,hn⟩,mem_univ _,rfl⟩⟩
  have he : ((r*(partitionSize p-1):ℕ):ℝ)=(r:ℝ)*((partitionSize p:ℝ)-1) := by
    rw [Nat.cast_mul,Nat.cast_sub hp0,Nat.cast_one]
  exact_mod_cast (show ((r*(partitionSize p-1):ℕ):ℝ) ≤ (G.crossing univ p).card by rwa [he])

end
end AlgorithmicThinTrees.Orientations
end

end OAI
