import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarSchedule
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarCompactBridge

namespace OAI

/-! The actual normalized Hamiltonian follows the same disjoint pulse
schedule as the unshifted program. -/

noncomputable section
namespace ForcedComputation.PlanarTiming
open ShearFlows Set

theorem cell_in_unit (n i : ℕ) (hi : i ≤ n) {t : ℝ}
    (ht : t ∈ Icc (cut n i) (cut n (i + 1))) : t ∈ Icc (0 : ℝ) 1 := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hl : 0 ≤ cut n i := div_nonneg (Nat.cast_nonneg _) hn.le
  have hu : cut n (i + 1) ≤ 1 := by
    apply (div_le_one hn).mpr
    exact_mod_cast Nat.succ_le_succ hi
  exact ⟨hl.trans ht.1, ht.2.trans hu⟩

end ForcedComputation.PlanarTiming

namespace ForcedComputation.Recorder.Planar
open ShearFlows PlanarHamiltonian PlanarTiming Set

theorem normalizedProcessor_on_cell (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I)
    (i : Fin (actions (freshMachine I.1) (freshInput_valid hI).1).length) {t : ℝ}
    (ht : t ∈ Icc (cut (actions (freshMachine I.1) (freshInput_valid hI).1).length i.val)
      (cut (actions (freshMachine I.1) (freshInput_valid hI).1).length (i.val + 1)))
    (x : Plane) :
    processorVelocity (normalizedPulse I hI) t x = (normalizedPulse I hI i).velocity t x := by
  rw [processorVelocity_eq_sum]
  apply Finset.sum_eq_single i
  · intro j _ hji
    change pulse j t • (normalizedPulse I hI j).spatial x = 0
    rw [pulse_other_on_cell hji.symm ht, zero_smul]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem normalizedProcessor_on_tail (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {t : ℝ}
    (ht : cut (actions (freshMachine I.1) (freshInput_valid hI).1).length
      (actions (freshMachine I.1) (freshInput_valid hI).1).length ≤ t) (x : Plane) :
    processorVelocity (normalizedPulse I hI) t x = 0 := by
  rw [processorVelocity_eq_sum]
  apply Finset.sum_eq_zero
  intro i _
  change pulse i t • (normalizedPulse I hI i).spatial x = 0
  rw [pulse_on_tail i ht, zero_smul]

theorem normalizedSlice_on_unit (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (x : Plane)
    (hx₀ : x 0 ∈ Ioo (0 : ℝ) 1) (hx₁ : x 1 ∈ Ioo (0 : ℝ) 1) :
    planarSlice (normalizedHamiltonian I hI) t x =
      processorVelocity (normalizedPulse I hI) t x :=
  (normalized_planar_field_on_chart I hI t x hx₀ hx₁).symm.trans
    (periodicVelocity_on_unit (normalizedPulse_valid I hI) (normalizedPulse_inUnit I hI) ht x)

theorem normalizedSlice_on_cell (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I)
    (i : Fin (actions (freshMachine I.1) (freshInput_valid hI).1).length) {t : ℝ}
    (ht : t ∈ Icc (cut (actions (freshMachine I.1) (freshInput_valid hI).1).length i.val)
      (cut (actions (freshMachine I.1) (freshInput_valid hI).1).length (i.val + 1)))
    (x : Plane) (hx₀ : x 0 ∈ Ioo (0 : ℝ) 1) (hx₁ : x 1 ∈ Ioo (0 : ℝ) 1) :
    planarSlice (normalizedHamiltonian I hI) t x = (normalizedPulse I hI i).velocity t x :=
  (normalizedSlice_on_unit I hI (cell_in_unit _ _ i.isLt.le ht) x hx₀ hx₁).trans
    (normalizedProcessor_on_cell I hI i ht x)

theorem normalizedSlice_on_tail (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {t : ℝ}
    (ht : t ∈ Icc
      (cut (actions (freshMachine I.1) (freshInput_valid hI).1).length
        (actions (freshMachine I.1) (freshInput_valid hI).1).length) 1)
    (x : Plane) (hx₀ : x 0 ∈ Ioo (0 : ℝ) 1) (hx₁ : x 1 ∈ Ioo (0 : ℝ) 1) :
    planarSlice (normalizedHamiltonian I hI) t x = 0 := by
  have hzero : 0 ≤ cut (actions (freshMachine I.1) (freshInput_valid hI).1).length
      (actions (freshMachine I.1) (freshInput_valid hI).1).length := by
    apply div_nonneg (Nat.cast_nonneg _)
    positivity
  exact (normalizedSlice_on_unit I hI ⟨hzero.trans ht.1, ht.2⟩ x hx₀ hx₁).trans
    (normalizedProcessor_on_tail I hI ht.1 x)

end ForcedComputation.Recorder.Planar

end

end OAI
