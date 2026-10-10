import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsFinite

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairSourceFlagPruning
attribute [local instance] Classical.propDecidable

def prunedSupport {α : Type*} (S : Finset α) (μ : α → ℝ) : Finset α :=
  S.filter (fun z => μ z ≠ 0)

@[simp] theorem mem_prunedSupport {α : Type*} (S : Finset α) (μ : α → ℝ) (z : α) :
    z ∈ prunedSupport S μ ↔ z ∈ S ∧ μ z ≠ 0 := Finset.mem_filter

theorem prunedSupport_subset {α : Type*} (S : Finset α) (μ : α → ℝ) :
    prunedSupport S μ ⊆ S := Finset.filter_subset _ _

theorem weighted_sum_prunedSupport {α : Type*} (S : Finset α) (μ F : α → ℝ) :
    (∑z∈S, μ z * F z) = ∑z∈prunedSupport S μ, μ z * F z := by
  classical
  symm
  unfold prunedSupport
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : μ z = 0 <;> simp only [h,ne_eq,not_true_eq_false,not_false_eq_true,
    ite_false,ite_true,zero_mul]

@[simp] theorem sum_prunedSupport {α : Type*} (S : Finset α) (μ : α → ℝ) :
    (∑z∈prunedSupport S μ, μ z) = ∑z∈S, μ z := by
  simpa only [mul_one] using (weighted_sum_prunedSupport S μ (fun _ => 1)).symm

theorem mem_pi_prunedSupport {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (S : ι → Finset α) (μ : ι → α → ℝ) (x : ι → α) :
    x ∈ Fintype.piFinset (fun i => prunedSupport (S i) (μ i)) ↔
      x ∈ Fintype.piFinset S ∧ (∏i, μ i (x i)) ≠ 0 := by
  classical
  simp only [Fintype.mem_piFinset,mem_prunedSupport,Finset.prod_ne_zero_iff,
    Finset.mem_univ,true_implies]
  exact forall_and

theorem product_sum_prunedSupport {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (S : ι → Finset α) (μ : ι → α → ℝ) (F : (ι → α) → ℝ) :
    (∑x∈Fintype.piFinset S, (∏i,μ i (x i))*F x) =
      ∑x∈Fintype.piFinset (fun i => prunedSupport (S i) (μ i)),
        (∏i,μ i (x i))*F x := by
  classical
  symm
  apply Finset.sum_subset
  · intro x hx
    exact ((mem_pi_prunedSupport S μ x).mp hx).1
  · intro x hx hnot
    have hz : (∏i,μ i (x i)) = 0 := by
      by_contra hn
      exact hnot ((mem_pi_prunedSupport S μ x).mpr ⟨hx,hn⟩)
    simp only [hz,zero_mul]

theorem double_sum_prunedSupport {ι α β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (S : ι → Finset α) (μ : ι → α → ℝ) (primes : Finset β) (ν : β → ℝ)
    (F : (ι → α) → β → ℝ) :
    (∑x∈Fintype.piFinset S, (∏i,μ i (x i))*∑n∈primes,ν n*F x n) =
      ∑x∈Fintype.piFinset (fun i => prunedSupport (S i) (μ i)),
        (∏i,μ i (x i))*∑n∈prunedSupport primes ν,ν n*F x n := by
  rw [product_sum_prunedSupport]
  apply Finset.sum_congr rfl
  intro x hx
  rw [weighted_sum_prunedSupport]

theorem prunedSupport_mass_le {α : Type*} (S : Finset α) (μ : α → ℝ) (C : ℝ)
    (h : ∑z∈S,μ z ≤ C) : ∑z∈prunedSupport S μ,μ z ≤ C := by
  rwa [sum_prunedSupport]

theorem prunedSupport_forall {α : Type*} (S : Finset α) (μ : α → ℝ) (P : α → Prop)
    (h : ∀z∈S,μ z≠0 → P z) : ∀z∈prunedSupport S μ,P z := by
  intro z hz
  exact h z ((mem_prunedSupport S μ z).mp hz).1 ((mem_prunedSupport S μ z).mp hz).2

theorem prunedSupport_pos {α : Type*} (S : Finset α) (μ : α → ℝ)
    (h : ∀z∈S,0≤μ z) : ∀z∈prunedSupport S μ,0<μ z := by
  intro z hz
  obtain ⟨hz,hn⟩ := (mem_prunedSupport S μ z).mp hz
  exact lt_of_le_of_ne (h z hz) (Ne.symm hn)

end Ostmann.Arithmetic.HistoryPairSourceFlagPruning

end

end OAI
