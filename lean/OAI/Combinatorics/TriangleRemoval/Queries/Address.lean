import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.TriangleGrowth
import OAI.Combinatorics.TriangleRemoval.Embeddings.PathBirthIndex
import OAI.Combinatorics.TriangleRemoval.Process.LookupGraph
import OAI.Combinatorics.TriangleRemoval.Process.PathForest
import OAI.Combinatorics.TriangleRemoval.Process.PathPattern

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave
namespace PathForest
variable {s : ℕ} {α : Type*}

def address (F : PathForest s) (key : Fin s → α) (i : Fin s) : List α :=
  key i :: match _hp : F.parent i with
    | none => []
    | some j => F.address key j
termination_by i.val
decreasing_by exact F.property i j _hp

lemma address_none (F : PathForest s) (key : Fin s → α) (i : Fin s)
    (hp : F.parent i = none) : F.address key i = [key i] := by
  rw [address,hp]

lemma address_some (F : PathForest s) (key : Fin s → α) (i j : Fin s)
    (hp : F.parent i = some j) : F.address key i = key i :: F.address key j := by
  rw [address,hp]

lemma address_unique (F : PathForest s) (key : Fin s → α) (ρ : Fin s → List α)
    (hρ : ∀ i, ρ i = key i :: (F.parent i).elim [] ρ) (i : Fin s) :
    F.address key i = ρ i := by
  induction i using (measure (fun i : Fin s => i.val)).wf.induction with
  | h i ih =>
    cases hp : F.parent i with
    | none => rw [F.address_none key i hp,hρ i,hp]; rfl
    | some j =>
      rw [F.address_some key i j hp,ih j (F.property i j hp),hρ i,hp]
      rfl

end PathForest

def indexedTriangleKey {K s n : ℕ} (birth : Fin s → Fin K)
    (f : Fin s → Finset (Fin K)) (ψ : Fin K → Fin n) (i : Fin s) :
    Finset (Fin n) × Finset (Fin n) :=
  ((f i).image ψ,insert (ψ (birth i)) ((f i).image ψ))

namespace TriangleGrowth
variable {n N R : ℕ} {G : Graph n} (A : TriangleGrowth (lookupGraph G) N R)

lemma pathAttachments_image (a b : Fin N) (hR : R ≤ N)
    (hi : Set.InjOn A.label (A.pathUnion a b)) (i : Fin (A.pathSuffix a b R).card) :
    (A.pathAttachments a b hR i).image (A.pathAssignment a b hi) =
      A.attach ((A.pathSuffix a b R).orderEmbOfFin rfl i) := by
  rw [A.pathAttachments_eq]
  change (reindexSet (A.pathUnion a b) _).image
    (A.label ∘ (A.pathUnion a b).orderEmbOfFin rfl) = _
  rw [← Finset.image_image,image_reindexSet]
  · exact ((A.older_invariants _).2 ((A.mem_pathSuffix a b _ R).mp
      ((A.pathSuffix a b R).orderEmbOfFin_mem rfl i)).2).2.1
  · intro x hx
    exact A.pathUnion_older_closed ((A.mem_pathSuffix a b _ R).mp
      ((A.pathSuffix a b R).orderEmbOfFin_mem rfl i)).1 hx

lemma indexedTriangleKey_actual (a b : Fin N) (hR : R ≤ N)
    (hi : Set.InjOn A.label (A.pathUnion a b)) (i : Fin (A.pathSuffix a b R).card) :
    indexedTriangleKey (A.pathBirthIndex a b hR) (A.pathAttachments a b hR)
      (A.pathAssignment a b hi) i =
      (A.attach ((A.pathSuffix a b R).orderEmbOfFin rfl i),
        insert (A.label ((A.pathSuffix a b R).orderEmbOfFin rfl i))
          (A.attach ((A.pathSuffix a b R).orderEmbOfFin rfl i))) := by
  unfold indexedTriangleKey
  rw [A.pathAttachments_image]
  change (_,insert (A.label ((A.pathUnion a b).orderEmbOfFin rfl _)) _) = _
  rw [A.pathBirthIndex_embedding]

end TriangleGrowth
end SharpTerminalLeave

end

end OAI
