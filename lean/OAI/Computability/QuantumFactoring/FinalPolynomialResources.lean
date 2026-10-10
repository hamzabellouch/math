import Mathlib
import OAI.Computability.QuantumFactoring.FactoringCircuit
import OAI.Computability.QuantumFactoring.TreeReadoutResources
import OAI.Computability.QuantumFactoring.RetainedQuarterPolynomial

namespace OAI



section

namespace ExactQuantumFactoring
namespace PhysicalTree
lemma factoringProgram_at {α : Type*} (len : α→ℕ) (hpos : ∀x,0<len x) :
    PolyAt len (fun x=>(factoringProgram (len x) (hpos x)).length) := by
  have hprep:=PolyAt.ofPoly PreparationPolynomial.quarterSteps len
  have hflag : PolyAt len (fun x=>(quarterFlag (len x) (hpos x)).net.count):=quarterFlag_at len hpos
  have hwidth:=PolyAt.ofPoly PreparationPolynomial.quarterWidth len
  have hresult:=PolyAt.ofPoly PreparationPolynomial.physicalResultBound len
  exact (((((((PolyAt.const len 3).mul hprep).add ((PolyAt.const len 8).mul hflag)).add
    ((PolyAt.const len 16).mul hwidth)).add ((PolyAt.const len 4).mul hresult)).add
      ((PolyAt.const len 34).mul ((PolyAt.self len).mul (PolyAt.self len)))).add
        (PolyAt.const len 492)).of_le (fun x=>(factoringProgram_resources_reduced (len x) (hpos x)).1)
lemma readoutWidth_at {α : Type*} (len : α→ℕ) (hpos : ∀x,0<len x) :
    PolyAt len (fun x=>readoutWidth (len x) (hpos x)) := by
  have hflag : PolyAt len (fun x=>(quarterFlag (len x) (hpos x)).net.count):=quarterFlag_at len hpos
  have hwidth:=PolyAt.ofPoly PreparationPolynomial.quarterWidth len
  have hresult:=PolyAt.ofPoly PreparationPolynomial.physicalResultBound len
  exact ((((((PolyAt.const len 3).mul hwidth).add hflag).add hresult).add
    ((PolyAt.const len 9).mul ((PolyAt.self len).mul (PolyAt.self len)))).add
      (PolyAt.const len 120)).of_le (fun x=>(factoringProgram_resources_reduced (len x) (hpos x)).2)
lemma paddedLength_poly : PolyBound paddedLength :=
  (PolyBound.const 128).max PolyBound.id
lemma finalCircuit_qubits_poly : PolyBound (fun ℓ=>(finalCircuit ℓ).qubits) := by
  obtain ⟨p,hp⟩:=readoutWidth_at paddedLength paddedLength_pos
  exact (PolyBound.comp (⟨p,fun _=>le_rfl⟩ : PolyBound (fun n=>p.eval n)) paddedLength_poly).of_le hp
lemma finalCircuit_gates_poly : PolyBound (fun ℓ=>(finalCircuit ℓ).instructions.length) := by
  obtain ⟨p,hp⟩:=factoringProgram_at paddedLength paddedLength_pos
  apply (PolyBound.comp (⟨p,fun _=>le_rfl⟩ : PolyBound (fun n=>p.eval n)) paddedLength_poly).of_le
  intro ℓ
  rw [finalCircuit_length]
  exact hp ℓ
theorem finalCircuit_resources : PolynomialResources finalCircuit := by
  obtain ⟨p,hp⟩:=finalCircuit_qubits_poly
  obtain ⟨q,hq⟩:=finalCircuit_gates_poly
  refine ⟨p+q,fun ℓ=>?_⟩
  rw [Polynomial.eval_add]
  exact ⟨(hp ℓ).trans (Nat.le_add_right _ _),(hq ℓ).trans (Nat.le_add_left _ _)⟩
end PhysicalTree
end ExactQuantumFactoring

end


end OAI
