import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSweepCircuit

namespace OAI

/-! Each sweep stage uses only vertical transfers and its single horizontal gate. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaTransferGates_member {work : ℕ}
    (ps : List (Fin (work+1) × Fin (work+1))) (g : QMAGate) :
    g ∈ qmaTransferGates ps ↔ ∃ p ∈ ps, g ∈ qmaWireSwapGates p.1 p.2 := by
  induction ps with
  | nil => simp [qmaTransferGates]
  | cons p ps ih =>
    rcases p with ⟨i,j⟩
    simp only [qmaTransferGates,List.mem_append,ih,List.mem_cons]
    aesop

theorem qmaRowStage_member (width work : ℕ)
    (l r : Fin (width+1) → Fin (work+1)) (e : Equiv.Perm (Fin (width+1)))
    (g k : QMAGate) (hk : k ∈ qmaRowStage width work l r e g) :
    k = qmaMapGate width work r g ∨
      ∃ i : Fin (width+1), k ∈ qmaWireSwapGates (l i) (r i) := by
  simp only [qmaRowStage,List.mem_append,List.mem_singleton] at hk
  rcases hk with (hk | rfl) | hk
  · obtain ⟨p,hp,hk⟩ := (qmaTransferGates_member _ k).mp hk
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hp)
    exact Or.inr ⟨e i,hk⟩
  · exact Or.inl rfl
  · obtain ⟨p,hp,hk⟩ := (qmaTransferGates_member _ k).mp hk
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_drop hp)
    exact Or.inr ⟨e i,hk⟩

theorem qmaWireSwap_sites {work : ℕ} (i j : Fin (work+1))
    (g : QMAGate) (hg : g ∈ qmaWireSwapGates i j) :
    ∀ k ∈ qmaGateSites work g, k = i ∨ k = j := by
  simp only [qmaWireSwapGates,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl <;>
    simp [qmaGateSites,qmaQubit_fin,or_comm]

theorem qmaAdjacentGate_window (work : ℕ) (g : QMAGate)
    (hg : g.WellFormed (work+1)) (ha : g.Adjacent) :
    ∃ lo : Fin (work+1), ∀ i ∈ qmaGateSites work g,
      lo.val ≤ i.val ∧ i.val ≤ lo.val+1 := by
  cases g with
  | hadamard i =>
    refine ⟨⟨i,hg⟩,?_⟩
    intro k hk
    simp only [qmaGateSites,Finset.mem_singleton] at hk
    subst k
    simp [qmaQubit,Nat.mod_eq_of_lt hg]
  | phaseT i =>
    refine ⟨⟨i,hg⟩,?_⟩
    intro k hk
    simp only [qmaGateSites,Finset.mem_singleton] at hk
    subst k
    simp [qmaQubit,Nat.mod_eq_of_lt hg]
  | controlledNot i j =>
    refine ⟨⟨min i j,lt_of_le_of_lt (min_le_left _ _) hg.1⟩,?_⟩
    intro k hk
    simp only [qmaGateSites,Finset.mem_insert,Finset.mem_singleton] at hk
    change i+1 = j ∨ j+1 = i at ha
    rcases hk with rfl | rfl
    · simp only [qmaQubit,Fin.val_mk,Nat.mod_eq_of_lt hg.1]
      omega
    · simp only [qmaQubit,Fin.val_mk,Nat.mod_eq_of_lt hg.2.1]
      omega

end ContinuumCoulomb

end

end OAI
