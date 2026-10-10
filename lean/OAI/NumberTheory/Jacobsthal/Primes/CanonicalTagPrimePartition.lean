import OAI.NumberTheory.Jacobsthal.Paths.TagSubbinWidths

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosTagSubbins
open ErdosInversePrimeBin

noncomputable def subbin (R theta : ℝ) (N i : ℕ) : Finset ℕ :=
  primeBin (left R theta N i) (width R theta N i)

theorem mem_subbin {R theta : ℝ} {N i p : ℕ} (hR : 0 < R) (ht : 0 < theta)
    (hN : 0 < N) : p ∈ subbin R theta N i ↔
      p.Prime ∧ left R theta N i < (p : ℝ) ∧ (p : ℝ) ≤ right R theta N i := by
  unfold subbin
  rw [mem_primeBin (left_pos hR ht hN).le (width_pos hR ht hN).le,
    local_endpoint hR ht hN]

theorem lower_endpoint_excluded {R theta : ℝ} {N i p : ℕ} (hR : 0 < R)
    (ht : 0 < theta) (hN : 0 < N) (hp : (p : ℝ) = left R theta N i) :
    p ∉ subbin R theta N i := by
  intro h
  have hm := (mem_subbin hR ht hN).mp h
  rw [hp] at hm
  exact lt_irrefl _ hm.2.1

theorem upper_endpoint_included {R theta : ℝ} {N i p : ℕ} (hR : 0 < R)
    (ht : 0 < theta) (hN : 0 < N) (hprime : p.Prime)
    (hp : (p : ℝ) = right R theta N i) : p ∈ subbin R theta N i := by
  apply (mem_subbin hR ht hN).mpr
  rw [hp]
  exact ⟨hprime, left_lt_right hR ht hN, le_rfl⟩

theorem subbin_subset {R theta : ℝ} {N i : ℕ} (hR : 0 < R) (ht : 0 < theta)
    (hi : i < N) : subbin R theta N i ⊆ primeBin R theta := by
  intro p hp
  have hN : 0 < N := Nat.zero_lt_of_lt hi
  obtain ⟨hprime, hlo, hhi⟩ := (mem_subbin hR ht hN).mp hp
  exact (mem_primeBin hR.le ht.le p).mpr ⟨hprime,
    (left_lower (step_pos hR ht hN).le).trans_lt hlo, hhi.trans (right_upper hR ht hi)⟩

theorem unique_prime_subbin {R theta : ℝ} {N p : ℕ} (hR : 0 < R)
    (ht : 0 < theta) (hN : 0 < N) (hp : p ∈ primeBin R theta) :
    ∃! i : Fin N, p ∈ subbin R theta N i := by
  obtain ⟨hprime, hlo, hhi⟩ := (mem_primeBin hR.le ht.le p).mp hp
  obtain ⟨i, hi, hu⟩ := exists_unique_index hR ht hN hlo hhi
  refine ⟨i, (mem_subbin hR ht hN).mpr ⟨hprime, hi⟩, ?_⟩
  intro j hj
  exact hu j ((mem_subbin hR ht hN).mp hj).2

theorem subbins_pairwise_disjoint {R theta : ℝ} {N : ℕ} (hR : 0 < R)
    (ht : 0 < theta) (hN : 0 < N) :
    Pairwise (fun i j : Fin N => Disjoint (subbin R theta N i) (subbin R theta N j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  have hp := subbin_subset hR ht i.isLt hpi
  obtain ⟨k, _, hk⟩ := unique_prime_subbin hR ht hN hp
  exact hij ((hk i hpi).trans (hk j hpj).symm)

theorem finite_partition {R theta : ℝ} {N : ℕ} (hR : 0 < R)
    (ht : 0 < theta) (hN : 0 < N) :
    (Finset.univ : Finset (Fin N)).biUnion (fun i => subbin R theta N i) = primeBin R theta := by
  classical
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact subbin_subset hR ht i.isLt hi
  · intro hp
    exact (unique_prime_subbin hR ht hN hp).exists

theorem sum_partition {R theta : ℝ} {N : ℕ} {B : Type*} [AddCommMonoid B]
    (hR : 0 < R) (ht : 0 < theta) (hN : 0 < N) (reward : ℕ → B) :
    (∑ p ∈ primeBin R theta, reward p) =
      ∑ i : Fin N, ∑ p ∈ subbin R theta N i, reward p := by
  classical
  rw [← finite_partition hR ht hN]
  exact Finset.sum_biUnion (fun i _ j _ hij => subbins_pairwise_disjoint hR ht hN hij)

theorem card_partition {R theta : ℝ} {N : ℕ} (hR : 0 < R)
    (ht : 0 < theta) (hN : 0 < N) :
    (primeBin R theta).card = ∑ i : Fin N, (subbin R theta N i).card := by
  classical
  simpa only [Finset.sum_const, smul_eq_mul, mul_one, Nat.cast_id] using
    sum_partition hR ht hN (fun _ : ℕ => (1 : ℕ))

theorem actual_prime_common_geometry {R theta w Cs : ℝ} {i p : ℕ}
    (hR : 0 < R) (ht : 0 < theta) (ht1 : theta ≤ 1) (hw : 1 < w)
    (hCs : 0 ≤ Cs) (hi : i < count w Cs) (hp : p ∈ subbin R theta (count w Cs) i) :
    left R theta (count w Cs) i ≤ (p : ℝ) ∧
    (p : ℝ) ≤ right R theta (count w Cs) i ∧
    right R theta (count w Cs) i ≤
      (1 + w ^ (-2 * Cs - 10)) * left R theta (count w Cs) i := by
  have hm := (mem_subbin hR ht (count_bounds hw hCs).1).mp hp
  exact ⟨hm.2.1.le, hm.2.2, (local_common_interval_geometry hR ht ht1 hw hCs hi).2.2.1⟩

end ErdosTagSubbins

end

end Erdos970

end OAI
