import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumUntouchedInput

namespace OAI

/-! Exact sweeps of disjoint three-CNOT wire transfers. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical

def qmaTransferGates {work : ℕ} : List (Fin (work+1) × Fin (work+1)) → List QMAGate
  | [] => []
  | (i,j)::ps => qmaWireSwapGates i j ++ qmaTransferGates ps

def qmaTransferPermutation {n : ℕ} : List (Fin n × Fin n) → Equiv.Perm (Fin n)
  | [] => Equiv.refl _
  | (i,j)::ps => (qmaTransferPermutation ps).trans (Equiv.swap i j)

theorem qmaTransferGates_length {work : ℕ} (ps : List (Fin (work+1) × Fin (work+1))) :
    (qmaTransferGates ps).length = 3*ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨i,j⟩
    simp only [qmaTransferGates,List.length_append,qmaWireSwapGates,List.length_cons,
      List.length_nil,ih]
    omega

theorem qmaTransferGates_wellFormed {work : ℕ} (ps : List (Fin (work+1) × Fin (work+1)))
    (hp : ∀ p ∈ ps, p.1 ≠ p.2) :
    ∀ g ∈ qmaTransferGates ps, g.WellFormed (work+1) := by
  induction ps with
  | nil => simp [qmaTransferGates]
  | cons p ps ih =>
    rcases p with ⟨i,j⟩
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact qmaWireSwapGates_wellFormed i j (hp (i,j) (by simp)) g hg
    · exact ih (fun p h => hp p (by simp [h])) g hg

theorem qmaTransferGates_matrix {work : ℕ} (ps : List (Fin (work+1) × Fin (work+1)))
    (hp : ∀ p ∈ ps, p.1 ≠ p.2) :
    qmaGateProduct work (qmaTransferGates ps) =
      qmaWirePermutation (fun s => s ∘ qmaTransferPermutation ps) := by
  induction ps with
  | nil =>
    ext s t
    simp [qmaTransferGates,qmaGateProduct_nil,qmaTransferPermutation,qmaWirePermutation,Matrix.one_apply]
  | cons p ps ih =>
    rcases p with ⟨i,j⟩
    rw [qmaTransferGates,qmaGateProduct_append,ih (fun p h => hp p (by simp [h]))]
    rw [show qmaGateProduct work (qmaWireSwapGates i j) =
      qmaWirePermutation (fun s => s ∘ Equiv.swap i j) from
        qmaWireSwap_matrix i j (hp (i,j) (by simp))]
    rw [qmaWirePermutation_mul]
    rfl

theorem qmaTransferPermutation_fixed {n : ℕ} (ps : List (Fin n × Fin n)) (k : Fin n)
    (hk : ∀ p ∈ ps, k ≠ p.1 ∧ k ≠ p.2) : qmaTransferPermutation ps k = k := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨i,j⟩
    change Equiv.swap i j (qmaTransferPermutation ps k) = k
    rw [ih (fun p h => hk p (by simp [h]))]
    exact Equiv.swap_apply_of_ne_of_ne (hk (i,j) (by simp)).1 (hk (i,j) (by simp)).2

def QMATransferDisjoint {n : ℕ} (p q : Fin n × Fin n) : Prop :=
  p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2

theorem qmaTransferPermutation_exchanges {n : ℕ} (ps : List (Fin n × Fin n))
    (hp : ps.Pairwise QMATransferDisjoint) (p : Fin n × Fin n) (hm : p ∈ ps) :
    qmaTransferPermutation ps p.1 = p.2 ∧ qmaTransferPermutation ps p.2 = p.1 := by
  induction ps with
  | nil => simp at hm
  | cons q ps ih =>
    obtain ⟨hq,ht⟩ := List.pairwise_cons.mp hp
    rcases List.mem_cons.mp hm with rfl | hm
    · have h₁ : qmaTransferPermutation ps p.1 = p.1 :=
        qmaTransferPermutation_fixed ps p.1 (fun p h => ⟨(hq p h).1,(hq p h).2.1⟩)
      have h₂ : qmaTransferPermutation ps p.2 = p.2 :=
        qmaTransferPermutation_fixed ps p.2 (fun p h => ⟨(hq p h).2.2.1,(hq p h).2.2.2⟩)
      change Equiv.swap p.1 p.2 (qmaTransferPermutation ps p.1) = p.2 ∧
        Equiv.swap p.1 p.2 (qmaTransferPermutation ps p.2) = p.1
      simp [h₁,h₂]
    · obtain ⟨h₁,h₂⟩ := ih ht hm
      change Equiv.swap q.1 q.2 (qmaTransferPermutation ps p.1) = p.2 ∧
        Equiv.swap q.1 q.2 (qmaTransferPermutation ps p.2) = p.1
      rw [h₁,h₂]
      exact ⟨Equiv.swap_apply_of_ne_of_ne (hq p hm).2.1.symm (hq p hm).2.2.2.symm,
        Equiv.swap_apply_of_ne_of_ne (hq p hm).1.symm (hq p hm).2.2.1.symm⟩

end ContinuumCoulomb

end

end OAI
