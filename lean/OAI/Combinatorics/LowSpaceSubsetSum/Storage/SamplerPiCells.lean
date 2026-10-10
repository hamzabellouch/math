import OAI.Combinatorics.LowSpaceSubsetSum.Storage.SamplerProductCells

namespace OAI

/-! # Sequential finite sampler arrays with unread-tail storage -/

noncomputable section
namespace LowSpaceSubsetSum.SamplerPiCells

open scoped BigOperators

def run : (k : ℕ) → (A : Fin k → Type) → [∀ i, Fintype (A i)] →
    (S : ∀ i, SamplerCoupling (A i)) →
    (∀ i, (S i).Seed → SamplerExecution.Trace (A i) × ℕ) →
    (Fin k → ℕ) → (SamplerCoupling.pi k A S).Seed →
      SamplerExecution.Trace (∀ i, A i) × ℕ
  | 0, _, _, _, _, _, _ => (⟨some (fun i => Fin.elim0 i), 0, 0⟩, 8)
  | k+1, A, _, S, X, K, s =>
    let tail := run k (fun i => A i.succ) (fun i => S i.succ)
      (fun i => X i.succ) (fun i => K i.succ)
    let r := SamplerProductCells.run (X 0) tail
      ((∑ i : Fin k, K i.succ)+24*k+8) s
    (⟨r.1.value.map (Fin.consEquiv A), r.1.reads, r.1.tests⟩, r.2+8)

theorem value (k : ℕ) (A : Fin k → Type) [∀ i, Fintype (A i)]
    (S : ∀ i, SamplerCoupling (A i))
    (X : ∀ i, (S i).Seed → SamplerExecution.Trace (A i) × ℕ)
    (K : Fin k → ℕ) (source : ∀ i, SamplerExecution.Execution (S i))
    (hv : ∀ i s, (X i s).1 = (source i).run s)
    (s : (SamplerCoupling.pi k A S).Seed) :
    (run k A S X K s).1 = (SamplerExecution.pi k A S source).run s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ht := ih (fun i => A i.succ) (fun i => S i.succ)
      (fun i => X i.succ) (fun i => K i.succ) (fun i => source i.succ)
      (fun i => hv i.succ)
    have hp := SamplerProductCells.value (X 0)
      (run k (fun i => A i.succ) (fun i => S i.succ)
        (fun i => X i.succ) (fun i => K i.succ))
      ((∑ i : Fin k, K i.succ)+24*k+8) (source 0)
      (SamplerExecution.pi k (fun i => A i.succ) (fun i => S i.succ) (fun i => source i.succ))
      (hv 0) ht s
    simp only [run, SamplerExecution.pi, SamplerExecution.map, hp]

theorem cells (k : ℕ) (A : Fin k → Type) [∀ i, Fintype (A i)]
    (S : ∀ i, SamplerCoupling (A i))
    (X : ∀ i, (S i).Seed → SamplerExecution.Trace (A i) × ℕ)
    (K : Fin k → ℕ) (hc : ∀ i s, (X i s).2 ≤ K i)
    (s : (SamplerCoupling.pi k A S).Seed) :
    (run k A S X K s).2 ≤ (∑ i, K i)+24*k+8 := by
  induction k with
  | zero => simp only [run, Fin.sum_univ_zero, Nat.mul_zero, Nat.zero_add, le_refl]
  | succ k ih =>
    have ht := ih (fun i => A i.succ) (fun i => S i.succ)
      (fun i => X i.succ) (fun i => K i.succ) (fun i => hc i.succ)
    have hp := SamplerProductCells.cells (X 0)
      (run k (fun i => A i.succ) (fun i => S i.succ)
        (fun i => X i.succ) (fun i => K i.succ))
      (K 0) ((∑ i : Fin k, K i.succ)+24*k+8) (hc 0) ht s
    change _+8 ≤ _
    rw [Fin.sum_univ_succ]
    omega

end LowSpaceSubsetSum.SamplerPiCells

end

end OAI
