import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFirstUseProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedReference

namespace OAI

/-! Literal numeric descriptors for the actual history terms, in the exact
finite-sum order used before time grouping. -/

noncomputable section
namespace ContinuumCoulomb.QuantumHistoryDescriptors
open ExactQuantumFactoring.BitStackProgram QuantumCircuitCode

abbrev Descriptor := ℕ × ℕ
def descriptorCode : Descriptor → List Bool := prodCode Nat.bits Nat.bits

def encode (c : QMACircuit) : QMACircuitTerm c → Descriptor
  | .inl i => (0,i.val)
  | .inr (.inl b) => (1,b.val)
  | .inr (.inr (.inl i)) => (2,i.val)
  | .inr (.inr (.inr (.inl _))) => (3,0)
  | .inr (.inr (.inr (.inr t))) => (4,t.val)

def atIndex (work time i : ℕ) : Descriptor :=
  if i < time+1 then (0,i) else
  if i < time+1+2 then (1,i-(time+1)) else
  if i < time+1+2+(work+1) then (2,i-(time+1+2)) else
  if i < time+1+2+(work+1)+1 then (3,0) else
    (4,i-(time+1+2+(work+1)+1))

theorem atIndex_actual (c : QMACircuit) (a : QMACircuitTerm c) :
    atIndex c.work c.gates.length ((qmaHistoryTermIndex c) a).val = encode c a := by
  rcases a with i | (b | (i | (u | t)))
  · have hi := i.isLt
    change atIndex c.work c.gates.length i.val=(0,i.val)
    simp only [atIndex,ite_eq_left hi]
  · have hb := b.isLt
    change atIndex c.work c.gates.length (c.gates.length+1+b.val)=(1,b.val)
    have h₁ : ¬c.gates.length+1+b.val < c.gates.length+1 := by omega
    have h₂ : c.gates.length+1+b.val < c.gates.length+1+2 := by omega
    simp only [atIndex,ite_eq_right h₁,ite_eq_left h₂,Nat.add_sub_cancel_left]
  · have hi := i.isLt
    change atIndex c.work c.gates.length (c.gates.length+1+(2+i.val))=(2,i.val)
    have h₁ : ¬c.gates.length+1+(2+i.val) < c.gates.length+1 := by omega
    have h₂ : ¬c.gates.length+1+(2+i.val) < c.gates.length+1+2 := by omega
    have h₃ : c.gates.length+1+(2+i.val) < c.gates.length+1+2+(c.work+1) := by omega
    simp only [atIndex,ite_eq_right h₁,ite_eq_right h₂,ite_eq_left h₃]
    congr 1
    omega
  · cases u
    change atIndex c.work c.gates.length (c.gates.length+1+(2+(c.work+1)+0))=(3,0)
    have h₁ : ¬c.gates.length+1+(2+(c.work+1)+0) < c.gates.length+1 := by omega
    have h₂ : ¬c.gates.length+1+(2+(c.work+1)+0) < c.gates.length+1+2 := by omega
    have h₃ : ¬c.gates.length+1+(2+(c.work+1)+0) < c.gates.length+1+2+(c.work+1) := by omega
    have h₄ : c.gates.length+1+(2+(c.work+1)+0) < c.gates.length+1+2+(c.work+1)+1 := by omega
    simp only [atIndex,ite_eq_right h₁,ite_eq_right h₂,ite_eq_right h₃,ite_eq_left h₄]
  · have ht := t.isLt
    change atIndex c.work c.gates.length
      (c.gates.length+1+(2+((c.work+1)+(1+t.val))))=(4,t.val)
    have h₁ : ¬c.gates.length+1+(2+((c.work+1)+(1+t.val))) < c.gates.length+1 := by omega
    have h₂ : ¬c.gates.length+1+(2+((c.work+1)+(1+t.val))) < c.gates.length+1+2 := by omega
    have h₃ : ¬c.gates.length+1+(2+((c.work+1)+(1+t.val))) < c.gates.length+1+2+(c.work+1) := by omega
    have h₄ : ¬c.gates.length+1+(2+((c.work+1)+(1+t.val))) < c.gates.length+1+2+(c.work+1)+1 := by omega
    simp only [atIndex,ite_eq_right h₁,ite_eq_right h₂,ite_eq_right h₃,ite_eq_right h₄]
    congr 1
    omega

def source (c : QMACircuit) : List Descriptor :=
  (List.range (2*c.gates.length+c.work+5)).map (atIndex c.work c.gates.length)

theorem source_actual (c : QMACircuit) :
    source c=(qmaHistoryTermList c).map (encode c) := by
  apply List.ext_getElem
  · simp only [source,List.length_map,List.length_range,qmaHistoryTermList,List.length_ofFn,
      qmaHistoryReferenceWork]
  · intro i hi hj
    simp only [source,List.getElem_map,List.getElem_range,qmaHistoryTermList,
      List.getElem_ofFn]
    have he := atIndex_actual c ((qmaHistoryTermIndex c).symm ⟨i,by
      simpa only [List.length_map,qmaHistoryTermList,List.length_ofFn] using hj⟩)
    simpa only [Equiv.apply_symm_apply] using he

theorem source_length (c : QMACircuit) : (source c).length=2*c.gates.length+c.work+5 := by
  simp only [source,List.length_map,List.length_range]

end ContinuumCoulomb.QuantumHistoryDescriptors

end

end OAI
