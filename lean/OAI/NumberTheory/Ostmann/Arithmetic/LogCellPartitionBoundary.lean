import OAI.NumberTheory.Ostmann.Arithmetic.LogCellPartitionPrimes
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellReplacementUniform

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.LogCellPartition
open PrimeProgression PrimeCellReplacement Classical

theorem log_eq_left_of_closed_not_assigned (N : ℕ) (lo hi η : ℝ)
    (j : Fin (gridCount lo hi η)) {p : ℕ}
    (hp : p ∈ logPrimeSupport N (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1)))
    (hpnot : p ∉ assignedPrimeSupport N lo hi η j) :
    Real.log (p:ℝ) = gridPoint lo hi η j.val := by
  have hclosed := (mem_logPrimeSupport _ _ _ _).mp hp
  have hnot : ¬(j.val=0 ∨ gridPoint lo hi η j.val < Real.log (p:ℝ)) := by
    intro h
    exact hpnot (Finset.mem_filter.mpr ⟨hp,h⟩)
  push Not at hnot
  exact le_antisymm hnot.2 hclosed.2.2.1

theorem closed_assigned_difference_card_le (N : ℕ) (lo hi η : ℝ)
    (j : Fin (gridCount lo hi η)) :
    ((logPrimeSupport N (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1))) \
      assignedPrimeSupport N lo hi η j).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  have hp' := Finset.mem_sdiff.mp hp
  have hq' := Finset.mem_sdiff.mp hq
  have hpl := log_eq_left_of_closed_not_assigned N lo hi η j hp'.1 hp'.2
  have hql := log_eq_left_of_closed_not_assigned N lo hi η j hq'.1 hq'.2
  have hpp := ((mem_logPrimeSupport _ _ _ _).mp hp'.1).2.1.pos
  have hqp := ((mem_logPrimeSupport _ _ _ _).mp hq'.1).2.1.pos
  have he : (p:ℝ)=(q:ℝ) := Real.log_injOn_pos
    (by change (0:ℝ)<p; exact_mod_cast hpp) (by change (0:ℝ)<q; exact_mod_cast hqp) (hpl.trans hql.symm)
  exact_mod_cast he

theorem norm_closed_assigned_test_error {E : Type*} [NormedAddCommGroup E]
    (N : ℕ) (lo hi η : ℝ) (j : Fin (gridCount lo hi η)) (f : ℕ → E)
    {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ p ∈ logPrimeSupport N (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1)),
      p ∉ assignedPrimeSupport N lo hi η j → ‖f p‖ ≤ A) :
    ‖(∑ p ∈ logPrimeSupport N (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1)), f p) -
      (∑ p ∈ assignedPrimeSupport N lo hi η j, f p)‖ ≤ A := by
  have hsub : assignedPrimeSupport N lo hi η j ⊆
      logPrimeSupport N (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1)) :=
    Finset.filter_subset _ _
  rw [← Finset.sum_sdiff_eq_sub hsub]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _p ∈ (logPrimeSupport N (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1))) \
        assignedPrimeSupport N lo hi η j, A :=
      Finset.sum_le_sum (fun p hp => hf p (Finset.mem_sdiff.mp hp).1 (Finset.mem_sdiff.mp hp).2)
    _ = (((logPrimeSupport N (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1))) \
        assignedPrimeSupport N lo hi η j).card:ℝ)*A := by simp
    _ ≤ A := by
      have hc : (((logPrimeSupport N (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1))) \
        assignedPrimeSupport N lo hi η j).card:ℝ) ≤ 1 := by
        exact_mod_cast closed_assigned_difference_card_le N lo hi η j
      simpa using mul_le_mul_of_nonneg_right hc hA

def assignedResidueMass (N M : ℕ) (a : ZMod M) (lo hi η Z : ℝ)
    (j : Fin (gridCount lo hi η)) : ℝ :=
  ∑ p ∈ (assignedPrimeSupport N lo hi η j).filter (fun p : ℕ => (p:ZMod M)=a),
    (Z*(p:ℝ))⁻¹

theorem residueMass_assigned_error (N M : ℕ) (a : ZMod M) (lo hi η : ℝ)
    (j : Fin (gridCount lo hi η)) {Z : ℝ} (hZ : 0 < Z) :
    |residueMass N M a (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1)) Z -
      assignedResidueMass N M a lo hi η Z j| ≤ (Z*Real.exp (gridPoint lo hi η j.val))⁻¹ := by
  unfold residueMass assignedResidueMass
  simp only [Finset.sum_filter]
  change ‖(∑ p ∈ logPrimeSupport N (gridPoint lo hi η j.val) (gridPoint lo hi η (j.val+1)),
      if (p:ZMod M)=a then (Z*(p:ℝ))⁻¹ else 0) -
    (∑ p ∈ assignedPrimeSupport N lo hi η j, if (p:ZMod M)=a then (Z*(p:ℝ))⁻¹ else 0)‖ ≤ _
  apply norm_closed_assigned_test_error N lo hi η j _ (by positivity)
  intro p hp hpnot
  have hpl := log_eq_left_of_closed_not_assigned N lo hi η j hp hpnot
  have hpp : (0:ℝ) < p := by exact_mod_cast ((mem_logPrimeSupport _ _ _ _).mp hp).2.1.pos
  have he : (p:ℝ)=Real.exp (gridPoint lo hi η j.val) := by rw [← hpl,Real.exp_log hpp]
  split_ifs
  · rw [he,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  · simp
    positivity

end Ostmann.Arithmetic.LogCellPartition

end

end OAI
