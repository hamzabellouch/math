import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.ContactSourceInputProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactGeometryBlockSemantics
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceBondLists
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorListCorrectness

namespace OAI

/-! The raw-list program uses exactly the original source endpoints and
exactly the calibrated lengths of the final mediator edges. -/

noncomputable section
namespace ContinuumCoulomb.ContactSourceInputProgram
open ContactMediator

private theorem lookup_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (d : α) (i : Fin n) :
    ((List.ofFn f).drop i.val).headD d = f i := by
  rw [List.drop_eq_getElem_cons (by simpa only [List.length_ofFn] using i.isLt)]
  simp only [List.headD_cons, List.getElem_ofFn]

def literalInput (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ) : Input :=
  (P, (List.ofFn d.coordinate, (d.bonds.toList, List.ofFn ℓ)))

theorem local_lookup (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ)
    (e : Fin d.edges) (negative : Bool) (a : LocalEdge) :
    ContactLocalInputProgram.lookup
      (P, (d.edges, (e.val, (negative, List.ofFn ℓ)))) a = ℓ (encodeEdge d.edges e a) := by
  unfold ContactLocalInputProgram.lookup
  rw [← encodeEdge_val]
  exact lookup_ofFn ℓ 1 (encodeEdge d.edges e a)

theorem local_record (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ)
    (e : Fin d.edges) (negative : Bool) :
    ContactLocalInputProgram.record (P, (d.edges, (e.val, (negative, List.ofFn ℓ)))) =
      ContactRationalLocal.input P negative (fun a => ℓ (encodeEdge d.edges e a)) := by
  simp only [ContactLocalInputProgram.record, ContactRationalLocal.input, local_lookup]

theorem literal_bond (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ)
    (e : Fin d.edges) :
    bond (e.val, literalInput d P ℓ) = ((d.left e).val, ((d.right e).val, d.coefficient e)) := by
  change ((List.ofFn (fun e : Fin d.edges =>
    ((d.left e).val, ((d.right e).val, d.coefficient e)))).drop e.val).headD _ = _
  exact lookup_ofFn _ _ e

theorem literal_edge (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ)
    (e : Fin d.edges) :
    edge (e.val, literalInput d P ℓ) = ContactGeometryBlockProgram.literalEdge d P ℓ e := by
  unfold edge
  rw [literal_bond]
  change Prod.mk
    (Prod.mk (((List.ofFn d.coordinate).drop (d.left e).val).headD (0, 0))
      (((List.ofFn d.coordinate).drop (d.right e).val).headD (0, 0)))
    (ContactLocalInputProgram.record (P, ((d.bonds.toList).length,
      (e.val, (decide (d.coefficient e < 0), List.ofFn ℓ))))) = _
  rw [lookup_ofFn, lookup_ofFn]
  have hlen : d.bonds.toList.length = d.edges := by simp [MediatorIteration.Bonds.toList]
  rw [hlen, local_record]
  rfl

theorem literal_edges (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ) :
    edges (literalInput d P ℓ) =
      List.ofFn (ContactGeometryBlockProgram.literalEdge d P ℓ) := by
  apply List.ext_getElem
  · simp [edges, literalInput, MediatorIteration.Bonds.toList]
  · intro i h₁ h₂
    have hi : i < d.edges := by simpa only [List.length_ofFn] using h₂
    simp only [edges, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    exact literal_edge d P ℓ ⟨i, hi⟩

theorem literal_positions (d : SquareLatticeHeisenberg) (P : ℕ) (ℓ : GlobalEdge d → ℚ) :
    positions (literalInput d P ℓ) =
      ContactGeometryBlockProgram.positions (ContactGeometryBlockProgram.literalInput d P ℓ) := by
  unfold positions
  rw [literal_edges]
  rfl

end ContinuumCoulomb.ContactSourceInputProgram

end

end OAI
