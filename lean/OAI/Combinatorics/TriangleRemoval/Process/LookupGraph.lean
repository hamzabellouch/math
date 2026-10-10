import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.RestrictLabel

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

def lookupGraph {n : ℕ} (G : Graph n) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ {x,y} ∈ G
  symm := ⟨fun x y h => ⟨h.1.symm,by simpa only [Finset.pair_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def initialVertices (N k : ℕ) : Finset (Fin N) := Finset.univ.filter (fun x => x.val < k)

@[simp] lemma mem_initialVertices (N k : ℕ) (x : Fin N) :
    x ∈ initialVertices N k ↔ x.val < k := by simp [initialVertices]

def initialLabel {N n k : ℕ} (hk : k ≤ N) (φ : Fin N ↪ Fin n) : Fin k ↪ Fin n :=
  ⟨fun i => φ (Fin.castLE hk i),φ.injective.comp (Fin.castLE_injective hk)⟩

def initialSubtypeLabel {N n k : ℕ} (ψ : Fin k ↪ Fin n) :
    {x // x ∈ initialVertices N k} ↪ Fin n where
  toFun x := ψ ⟨x.val.val,(mem_initialVertices N k x.val).mp x.property⟩
  inj' := by
    intro x y h
    have he := congrArg Fin.val (ψ.injective h)
    apply Subtype.ext
    exact Fin.ext he

@[simp] lemma initialSubtypeLabel_initialLabel {N n k : ℕ} (hk : k ≤ N)
    (φ : Fin N ↪ Fin n) : initialSubtypeLabel (initialLabel hk φ) =
      restrictLabel (initialVertices N k) φ := by
  ext x
  rfl

end SharpTerminalLeave

end

end OAI
