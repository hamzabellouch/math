import OAI.NumberTheory.Ostmann.Arithmetic.LogCellPartitionIntegers

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.LogCellPartition
open IntegerCell Classical

theorem integer_log_eq_left_of_closed_not_assigned (N : ℕ) (lo hi η : ℝ)
    (j : Fin (gridCount lo hi η)) {p : ℕ}
    (hp : p ∈ cellSupport N (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1)))
    (hpnot : p ∉ assignedIntegerSupport N lo hi η j) :
    Real.log (p:ℝ) = gridPoint lo hi η j.val := by
  have hclosed := (mem_cellSupport _ _ _ _).mp hp
  have hnot : ¬(j.val=0 ∨ gridPoint lo hi η j.val < Real.log (p:ℝ)) := by
    intro h
    exact hpnot (Finset.mem_filter.mpr ⟨hp,h⟩)
  push Not at hnot
  exact le_antisymm hnot.2 hclosed.2.2.1

theorem integer_closed_assigned_difference_card_le (N : ℕ) (lo hi η : ℝ)
    (j : Fin (gridCount lo hi η)) :
    ((cellSupport N (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1))) \
      assignedIntegerSupport N lo hi η j).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  have hp' := Finset.mem_sdiff.mp hp
  have hq' := Finset.mem_sdiff.mp hq
  have hpl := integer_log_eq_left_of_closed_not_assigned N lo hi η j hp'.1 hp'.2
  have hql := integer_log_eq_left_of_closed_not_assigned N lo hi η j hq'.1 hq'.2
  have hpp := ((mem_cellSupport _ _ _ _).mp hp'.1).2.1
  have hqp := ((mem_cellSupport _ _ _ _).mp hq'.1).2.1
  have he : (p:ℝ)=(q:ℝ) := Real.log_injOn_pos
    (by change (0:ℝ)<p; exact_mod_cast hpp) (by change (0:ℝ)<q; exact_mod_cast hqp) (hpl.trans hql.symm)
  exact_mod_cast he

theorem norm_integer_closed_assigned_test_error {E : Type*} [NormedAddCommGroup E]
    (N : ℕ) (lo hi η : ℝ) (j : Fin (gridCount lo hi η)) (f : ℕ → E)
    {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ p ∈ cellSupport N (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1)),
      p ∉ assignedIntegerSupport N lo hi η j → ‖f p‖ ≤ A) :
    ‖(∑ p ∈ cellSupport N (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1)), f p) -
      (∑ p ∈ assignedIntegerSupport N lo hi η j, f p)‖ ≤ A := by
  have hsub : assignedIntegerSupport N lo hi η j ⊆
      cellSupport N (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1)) :=
    Finset.filter_subset _ _
  rw [← Finset.sum_sdiff_eq_sub hsub]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _p ∈ (cellSupport N (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1))) \
        assignedIntegerSupport N lo hi η j, A :=
      Finset.sum_le_sum (fun p hp => hf p (Finset.mem_sdiff.mp hp).1 (Finset.mem_sdiff.mp hp).2)
    _ = (((cellSupport N (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1))) \
        assignedIntegerSupport N lo hi η j).card:ℝ)*A := by simp
    _ ≤ A := by
      have hc : (((cellSupport N (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1))) \
        assignedIntegerSupport N lo hi η j).card:ℝ) ≤ 1 := by
        exact_mod_cast integer_closed_assigned_difference_card_le N lo hi η j
      simpa using mul_le_mul_of_nonneg_right hc hA

def assignedIntegerResidueMass (N M : ℕ) (a : ZMod M) (lo hi η G : ℝ) (φ : ℝ → ℝ)
    (j : Fin (gridCount lo hi η)) : ℝ :=
  ∑ n ∈ (assignedIntegerSupport N lo hi η j).filter (fun n : ℕ => (n:ZMod M)=a),
    Real.exp (-G)*φ (Real.log n-G)

theorem integerResidueMass_assigned_error (N M : ℕ) (a : ZMod M) (lo hi η G : ℝ)
    (φ : ℝ → ℝ) (j : Fin (gridCount lo hi η)) {B : ℝ} (hB : 0 ≤ B)
    (hφ : ∀ t ∈ Set.Icc (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1)),
      |φ (t-G)| ≤ B) :
    |integerResidueMass N M a (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1)) G φ -
      assignedIntegerResidueMass N M a lo hi η G φ j| ≤ Real.exp (-G)*B := by
  unfold integerResidueMass assignedIntegerResidueMass
  rw [integerSupport_eq_filter]
  simp only [Finset.sum_filter]
  change ‖(∑ n ∈ cellSupport N (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1)),
      if (n:ZMod M)=a then Real.exp (-G)*φ (Real.log n-G) else 0) -
    (∑ n ∈ assignedIntegerSupport N lo hi η j,
      if (n:ZMod M)=a then Real.exp (-G)*φ (Real.log n-G) else 0)‖ ≤ _
  apply norm_integer_closed_assigned_test_error N lo hi η j _ (mul_nonneg (Real.exp_pos _).le hB)
  intro n hn hnnot
  split_ifs
  · rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hφ _ ((mem_cellSupport _ _ _ _).mp hn).2.2)
      (Real.exp_pos _).le
  · simpa using mul_nonneg (Real.exp_pos (-G)).le hB

theorem assignedIntegerResidueMass_error (N M : ℕ) [NeZero M] (a : ZMod M)
    (lo hi η G : ℝ) (φ ψ : ℝ → ℝ) (j : Fin (gridCount lo hi η)) (B D : ℝ)
    (h : lo ≤ hi) (hB : 0 ≤ B)
    (hN : ⌊Real.exp (gridPoint lo hi η (j.val+1))⌋₊ ≤ N)
    (hφ : ∀ t, HasDerivAt φ (ψ t) t) (hψ : Continuous ψ)
    (hφB : ∀ t ∈ Set.Icc (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1)), |φ (t-G)| ≤ B)
    (hψD : ∀ t ∈ Set.Icc (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1)), |ψ (t-G)| ≤ D) :
    |assignedIntegerResidueMass N M a lo hi η G φ j -
      integerDensityMass M (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1)) G φ| ≤
      Real.exp (-G)*(6*B+2*D*(gridPoint lo hi η (j.val+1)-gridPoint lo hi η j.val)) := by
  have hb := integerResidueMass_assigned_error N M a lo hi η G φ j hB hφB
  have he := integerResidueMass_error N M a φ ψ G
    (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1)) B D
    (gridPoint_mono h (Nat.le_succ _)) hN hφ hψ hφB hψD
  have ht := abs_sub_le (assignedIntegerResidueMass N M a lo hi η G φ j)
    (integerResidueMass N M a (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1)) G φ)
    (integerDensityMass M (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1)) G φ)
  rw [abs_sub_comm] at hb
  nlinarith

end Ostmann.Arithmetic.LogCellPartition

end

end OAI
