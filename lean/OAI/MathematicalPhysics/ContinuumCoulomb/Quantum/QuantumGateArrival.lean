import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumGridLocality

namespace OAI

/-! The insertion column is an actual operand, so adjacent gates remain close to the sweep. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaGateSites_nonempty (work : ℕ) (g : QMAGate) : (qmaGateSites work g).Nonempty := by
  cases g <;> simp [qmaGateSites]

def qmaGateArrivalIndex (work : ℕ) (e : Equiv.Perm (Fin (work+1))) (g : QMAGate) :
    Fin (work+1) :=
  ⟨qmaGateCut work e g-1,by
    have h := qmaGateCut_le work e g
    have hp : 0 < qmaGateCut work e g := by unfold qmaGateCut; omega
    omega⟩

def qmaGateArrivalColumn (work : ℕ) (e : Equiv.Perm (Fin (work+1))) (g : QMAGate) :
    Fin (work+1) := e (qmaGateArrivalIndex work e g)

theorem qmaGateArrivalColumn_mem (work : ℕ) (e : Equiv.Perm (Fin (work+1))) (g : QMAGate) :
    qmaGateArrivalColumn work e g ∈ qmaGateSites work g := by
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup (qmaGateSites work g)
    (qmaGateSites_nonempty work g) (fun j => (e.symm j).val)
  have heq : qmaGateArrivalIndex work e g = e.symm i := by
    apply Fin.ext
    change (qmaGateSites work g).sup (fun j => (e.symm j).val)+1-1 = _
    omega
  simpa only [qmaGateArrivalColumn,heq,Equiv.apply_symm_apply] using hi

theorem qmaGateArrivalColumn_near (work : ℕ) (e : Equiv.Perm (Fin (work+1)))
    (g : QMAGate) (hg : g.WellFormed (work+1)) (ha : g.Adjacent)
    (i : Fin (work+1)) (hi : i ∈ qmaGateSites work g) :
    i.val ≤ (qmaGateArrivalColumn work e g).val+1 ∧
      (qmaGateArrivalColumn work e g).val ≤ i.val+1 := by
  obtain ⟨lo,hlo⟩ := qmaAdjacentGate_window work g hg ha
  have h1 := hlo i hi
  have h2 := hlo _ (qmaGateArrivalColumn_mem work e g)
  omega

end ContinuumCoulomb

end

end OAI
