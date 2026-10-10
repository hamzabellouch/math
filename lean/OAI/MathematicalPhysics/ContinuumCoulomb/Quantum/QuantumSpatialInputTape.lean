import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkRoutingData
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListInitialSpatial

namespace OAI

/-! The computed fork-state/cell tape is exactly the array of the spatial
model. Only cells at actual spin indices are read. -/

noncomputable section
namespace ContinuumCoulomb.QuantumSpatialInputTape
open QuantumForkList QuantumForkGridProgram QuantumRouteCode

def coordinates {rows width : ℕ} (p : QMAGridCell rows width) : QuantumRouteCode.Pair :=
  (p.1.val,p.2.val)

private theorem iterate_coordinates {rows width : ℕ} (N : ℚ) (s : State)
    (cell : ℕ → QMAGridCell rows width) (k : ℕ) :
    iterateCell N k s (coordinates ∘ cell) = coordinates ∘ iterateCell N k s cell := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext v
    simp only [iterateCell,nextCell,Function.comp_apply]
    split <;> exact congrFun ih _

def input {rows width A D : ℕ} (I : SpatialInput rows width A D) : PreparedInput :=
  ((I.precision,I.n,I.bonds,I.constant),List.ofFn (fun v : Fin I.n => coordinates (I.cell v.val)))

theorem state_eq {rows width A D : ℕ} (I : SpatialInput rows width A D) :
    (output D (input I)).1 = I.state := output_state D (input I)

private theorem prepare_represents_input {rows width A D : ℕ}
    (I : SpatialInput rows width A D) :
    Represents (prepare (input I)).2 (coordinates ∘ initialCell I.n I.bonds I.cell) := by
  intro v hv
  change v < I.n+2*I.bonds.length at hv
  change lookup (initialCells (I.n,I.bonds,
    List.ofFn (fun v : Fin I.n => coordinates (I.cell v.val)))) v = _
  rw [lookup_initialCells _ v hv]
  change initialCell I.n I.bonds
    (lookup (List.ofFn (fun v : Fin I.n => coordinates (I.cell v.val)))) v = _
  by_cases h : v < I.n
  · simp only [Function.comp_apply,initialCell,h,ite_true]
    exact QuantumOrdinalProgram.lookup_ofFn _ ⟨v,h⟩
  · have hb : v-I.n < 2*I.bonds.length := by
      change v < I.n+2*I.bonds.length at hv
      omega
    have he := initialEndpoint_bound I.n I.bonds I.bounded (v-I.n) hb
    simp only [initialCell,h,ite_false,Function.comp_apply]
    exact QuantumOrdinalProgram.lookup_ofFn _ ⟨_,he⟩

theorem output_represents_input {rows width A D : ℕ}
    (I : SpatialInput rows width A D) :
    Represents (output D (input I)) (coordinates ∘ I.cells) := by
  have h := run_represents D (prepare (input I)) (initial_validPorts _ _ _ _)
    (coordinates ∘ initialCell I.n I.bonds I.cell) (prepare_represents_input I)
  change Represents (output D (input I))
    (iterateCell I.precision D (initial I.n I.bonds I.constant I.precision)
      (coordinates ∘ initialCell I.n I.bonds I.cell)) at h
  rw [iterate_coordinates] at h
  exact h

theorem output_eq {rows width A D : ℕ} (I : SpatialInput rows width A D) :
    output D (input I) =
      (I.state,List.ofFn (fun v : Fin I.state.1 => coordinates (I.cells v.val))) := by
  apply Prod.ext
  · exact state_eq I
  · apply List.ext_getElem
    · rw [List.length_ofFn,output_length,state_eq]
    · intro i hi hj
      have hi' : i < I.state.1 := by simpa only [List.length_ofFn] using hj
      have h := output_represents_input I i (by rwa [state_eq])
      simpa only [lookup,List.headD_eq_head?_getD,List.head?_drop,
        List.getElem?_eq_getElem hi,Option.getD_some,Function.comp_apply,
        List.getElem_ofFn] using h

theorem routing_eq {rows width A D : ℕ} (I : SpatialInput rows width A D) :
    QuantumForkRoutingData.value (output D (input I)) =
      QuantumRoutingInputProgram.actualData I.model (Equiv.refl _) := by
  rw [output_eq]
  exact QuantumForkRoutingData.value_spatialModel I.state I.validPorts I.state_bounded
    I.state_noLoops I.cells (spatialDensity A D) I.state_density I.state_degree I.state_locality

end ContinuumCoulomb.QuantumSpatialInputTape

end

end OAI
