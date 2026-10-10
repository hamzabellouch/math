import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceFlagPruningBasic

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairSourceFlagPruning

theorem prunedSupport_atom_le {α : Type*} (S : Finset α) (μ : α → ℝ) (A : ℝ)
    (h : ∀z∈S,μ z≠0 → μ z≤A) : ∀z∈prunedSupport S μ,μ z≤A :=
  prunedSupport_forall S μ (fun z => μ z≤A) h

theorem prunedSupport_nonneg {α : Type*} (S : Finset α) (μ : α → ℝ)
    (h : ∀z∈S,0≤μ z) : ∀z∈prunedSupport S μ,0≤μ z := by
  intro z hz
  exact h z (prunedSupport_subset S μ hz)

theorem product_mass_prunedSupport {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (S : ι → Finset α) (μ : ι → α → ℝ) :
    (∑x∈Fintype.piFinset (fun i => prunedSupport (S i) (μ i)),∏i,μ i (x i)) =
      ∑x∈Fintype.piFinset S,∏i,μ i (x i) := by
  simpa only [mul_one] using (product_sum_prunedSupport S μ (fun _ => 1)).symm

theorem double_sum_update_prunedSupport {ι α β : Type*}
    [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (S : ι → Finset α) (μ : ι → α → ℝ) (primes : Finset β) (ν : β → ℝ)
    (r : ι) (value : β → α) (F : (ι → α) → ℝ) :
    (∑x∈Fintype.piFinset S, (∏i,μ i (x i))*
      ∑n∈primes,ν n*F (Function.update x r (value n))) =
      ∑x∈Fintype.piFinset (fun i => prunedSupport (S i) (μ i)),
        (∏i,μ i (x i))*∑n∈prunedSupport primes ν,
          ν n*F (Function.update x r (value n)) :=
  double_sum_prunedSupport S μ primes ν (fun x n => F (Function.update x r (value n)))

theorem double_sum_eq_of_nonzero {ι α β : Type*}
    [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (S : ι → Finset α) (μ : ι → α → ℝ) (primes : Finset β) (ν : β → ℝ)
    (F G : (ι → α) → β → ℝ)
    (h : ∀x∈Fintype.piFinset S,∀n∈primes,
      (∏i,μ i (x i))≠0 → ν n≠0 → F x n=G x n) :
    (∑x∈Fintype.piFinset S,(∏i,μ i (x i))*∑n∈primes,ν n*F x n) =
      ∑x∈Fintype.piFinset S,(∏i,μ i (x i))*∑n∈primes,ν n*G x n := by
  classical
  rw [double_sum_prunedSupport S μ primes ν F,double_sum_prunedSupport S μ primes ν G]
  apply Finset.sum_congr rfl
  intro x hx
  apply congrArg (fun z => (∏i,μ i (x i))*z)
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hx,hx0⟩ := (mem_pi_prunedSupport S μ x).mp hx
  obtain ⟨hn,hn0⟩ := (mem_prunedSupport primes ν n).mp hn
  rw [h x hx n hn hx0 hn0]

end Ostmann.Arithmetic.HistoryPairSourceFlagPruning

end

end OAI
