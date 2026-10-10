import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumWireGrid

namespace OAI

/-! Exact composition of logical gates with successive physical wire transfers. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

abbrev QMAWireInstruction (work : ℕ) := List (Fin (work+1) × Fin (work+1)) × QMAGate

def qmaRoutedFrame {work : ℕ} (σ : Equiv.Perm (Fin (work+1))) :
    List (QMAWireInstruction work) → Equiv.Perm (Fin (work+1))
  | [] => σ
  | (ps,_)::xs => qmaRoutedFrame ((qmaTransferPermutation ps).trans σ) xs

def qmaRoutedGates (work : ℕ) (σ : Equiv.Perm (Fin (work+1))) :
    List (QMAWireInstruction work) → List QMAGate
  | [] => []
  | (ps,g)::xs =>
    let next := (qmaTransferPermutation ps).trans σ
    qmaTransferGates ps ++ [qmaRelabelGate work next.symm g] ++ qmaRoutedGates work next xs

theorem qmaWireBasis_product {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    qmaWirePermutation (qmaWireBasis σ)*qmaWirePermutation (qmaWireBasis τ) =
      qmaWirePermutation (qmaWireBasis (σ.trans τ)) := by
  rw [qmaWirePermutation_mul]
  rfl

theorem qmaRoutedGates_matrix (work : ℕ) (σ : Equiv.Perm (Fin (work+1)))
    (xs : List (QMAWireInstruction work))
    (hx : ∀ x ∈ xs, ∀ p ∈ x.1, p.1 ≠ p.2) :
    qmaGateProduct work (qmaRoutedGates work σ xs)*qmaWirePermutation (qmaWireBasis σ) =
      qmaWirePermutation (qmaWireBasis (qmaRoutedFrame σ xs))*
        qmaGateProduct work (xs.map Prod.snd) := by
  induction xs generalizing σ with
  | nil => simp [qmaRoutedGates,qmaRoutedFrame,qmaGateProduct_nil]
  | cons x xs ih =>
    rcases x with ⟨ps,g⟩
    let next := (qmaTransferPermutation ps).trans σ
    have hp : ∀ p ∈ ps, p.1 ≠ p.2 := hx (ps,g) (by simp)
    have ht : ∀ x ∈ xs, ∀ p ∈ x.1, p.1 ≠ p.2 := fun x h => hx x (by simp [h])
    have hframe : qmaGateProduct work (qmaTransferGates ps)*qmaWirePermutation (qmaWireBasis σ) =
        qmaWirePermutation (qmaWireBasis next) := by
      rw [qmaTransferGates_matrix ps hp]
      exact qmaWireBasis_product _ _
    change qmaGateProduct work (qmaTransferGates ps++[qmaRelabelGate work next.symm g]++
      qmaRoutedGates work next xs)*qmaWirePermutation (qmaWireBasis σ) =
      qmaWirePermutation (qmaWireBasis (qmaRoutedFrame next xs))*
        qmaGateProduct work (g::xs.map Prod.snd)
    rw [show g::xs.map Prod.snd = [g]++xs.map Prod.snd from rfl]
    simp only [qmaGateProduct_append,qmaGateProduct_singleton]
    calc
      _ = qmaGateProduct work (qmaRoutedGates work next xs)*
          (qmaGateMatrix work (qmaRelabelGate work next.symm g)*
            (qmaGateProduct work (qmaTransferGates ps)*qmaWirePermutation (qmaWireBasis σ))) := by
            simp only [mul_assoc]
      _ = qmaGateProduct work (qmaRoutedGates work next xs)*
          (qmaWirePermutation (qmaWireBasis next)*qmaGateMatrix work g) := by
            rw [hframe,←qmaGate_wire_intertwines]
      _ = _ := by rw [←mul_assoc,ih next ht,mul_assoc]

theorem qmaRoutedGates_length (work : ℕ) (σ : Equiv.Perm (Fin (work+1)))
    (xs : List (QMAWireInstruction work)) :
    (qmaRoutedGates work σ xs).length = (xs.map (fun x => 3*x.1.length+1)).sum := by
  induction xs generalizing σ with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨ps,g⟩
    simp [qmaRoutedGates,qmaTransferGates_length,ih,Nat.add_assoc]
    omega

theorem qmaRoutedGates_wellFormed (work : ℕ) (σ : Equiv.Perm (Fin (work+1)))
    (xs : List (QMAWireInstruction work))
    (hx : ∀ x ∈ xs, (∀ p ∈ x.1, p.1 ≠ p.2) ∧ x.2.WellFormed (work+1)) :
    ∀ g ∈ qmaRoutedGates work σ xs, g.WellFormed (work+1) := by
  induction xs generalizing σ with
  | nil => simp [qmaRoutedGates]
  | cons x xs ih =>
    rcases x with ⟨ps,g⟩
    intro h hh
    have hp := hx (ps,g) (by simp)
    simp only [qmaRoutedGates,List.mem_append,List.mem_singleton] at hh
    rcases hh with (hh | rfl) | hh
    · exact qmaTransferGates_wellFormed ps hp.1 h hh
    · exact qmaRelabelGate_wellFormed _ _ _ hp.2
    · exact ih _ (fun x h => hx x (by simp [h])) h hh

end ContinuumCoulomb

end

end OAI
