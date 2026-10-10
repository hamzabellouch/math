import OAI.Combinatorics.BalancedRyser.Deletion.SelectedDeletionEventsLemmas
import OAI.Combinatorics.BalancedRyser.Local.Local
import OAI.Combinatorics.BalancedRyser.Local.LocalSelectedKernel
import OAI.Combinatorics.BalancedRyser.Probability.PrimeConfigurationAssembly
import OAI.Combinatorics.BalancedRyser.Probability.SelectedJointAssembly

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Filter
open scoped Topology

noncomputable section
open scoped Classical

def SelectedLocalTransport : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
    ∀ (κ : SelectedDeletion.Kernel F) (c C K : ℝ),
      0 ≤ K → SelectedDeletion.IsExperiment κ c C →
      (∀ M (J : Finset (Slot F)) (prescribed : SelectedDeletion.Output F),
        SelectedDeletion.fixedCylinderMass κ M J prescribed ≤
          (K / (Fintype.card F : ℝ)) ^ J.card) →
      ∃ Q : Local.RetentionRule F, ∃ w : Local.Kernel F,
        Local.KernelConditions Q w K ∧ ∀ E : Configuration F → Prop,
          Local.selectedProbability w E =
            SelectedDeletion.jointMass κ (fun M s => E (SelectedDeletion.configuration M s))

theorem selectedLocalTransport_proof : SelectedLocalTransport := by
  intro F _ _ _ κ c C K hK hexp hcyl
  refine ⟨Local.KernelBridge.canonicalRetention,
    Local.KernelBridge.transportedKernel κ, ?_, ?_⟩
  · exact Local.KernelBridge.transported_kernelConditions κ c C K hK hexp hcyl
  · exact Local.KernelBridge.transported_probability_eq_jointMass κ

def SelectedCoreTransport : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
    ∀ (κ : SelectedDeletion.Kernel F) (c C : ℝ)
      (Q : PMF (DeletionSet F 3)),
      SelectedDeletion.IsExperiment κ c C →
      SelectedDeletion.RealizesConditionalLaw κ Q →
      0 < SelectedDeletion.successMass κ →
      ∀ E : Finset (Line F) → Prop,
        SelectedDeletion.jointMass κ
          (fun M s => E (SelectedDeletion.configuration M s).deletedLines) =
          SelectedDeletion.successMass κ * deletionEventProbability Q (fun D => E D.val)

theorem selectedCoreTransport_proof : SelectedCoreTransport := by
  intro F _ _ _ κ c C Q hexp hreal hpos E
  exact SelectedDeletion.jointMass_eq_success_mul_eventProbability hexp hpos Q hreal E

theorem mainResult_of_selected_results_and_transports
    (hdet : DeterministicReduction.{0})
    (hselected : SelectedDeletionResult.{0})
    (hcore : CorePencilResult.{0}) (hlocal : Local.PencilLocalResult.{0})
    (hLocalTransport : SelectedLocalTransport)
    (hCoreTransport : SelectedCoreTransport) : MainResult := by
  obtain ⟨c, Cbound, K, ρ, a₀, C₀, ε, N,
    hc, hC, hK, hρ0, hρ1, ha₀, hC₀, hNfour, hεnonneg, hεlim, hkernel⟩ := hselected
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  obtain ⟨εL, hεLlim, hεLnonneg, NL, hlocalBound⟩ := hlocal K hKpos
  have htol : 0 < a₀ / 4 := by positivity
  obtain ⟨NC, hcoreBound⟩ := hcore 3 (by norm_num) C₀ hC₀.le (ρ / 4)
    (by positivity) (a₀ / 4) htol
  obtain ⟨NE, hE⟩ := eventually_atTop.1 (hεlim.eventually_lt_const htol)
  obtain ⟨NEL, hEL⟩ := eventually_atTop.1 (hεLlim.eventually_lt_const htol)
  let Nall := max N (max NL (max NC (max NE NEL)))
  apply mainResult_of_prime_configurations hdet ρ hρ0 hρ1 Nall
  intro q hprime hlarge
  let : Fact q.Prime := ⟨hprime⟩
  have hNq : N ≤ q := (le_max_left N _).trans hlarge
  have hNLq : NL ≤ q := by dsimp [Nall] at hlarge; omega
  have hNCq : NC ≤ q := by dsimp [Nall] at hlarge; omega
  have hNEq : NE ≤ q := by dsimp [Nall] at hlarge; omega
  have hNELq : NEL ≤ q := by dsimp [Nall] at hlarge; omega
  have hcard : Fintype.card (ZMod q) = q := ZMod.card q
  obtain ⟨κ, hexp, _, hcylinder, hsuccess, hoccupancy, Q, hreal, hdom⟩ :=
    hkernel (ZMod q) (by simpa only [hcard] using hNq)
  have hsuccesspos : 0 < SelectedDeletion.successMass κ := ha₀.trans_le hsuccess
  have hsuccessone : SelectedDeletion.successMass κ ≤ 1 :=
    SelectedJointAssembly.successMass_le_one κ hexp.2.1
  obtain ⟨R, w, hw, hevent⟩ := hLocalTransport (ZMod q) κ c Cbound K hKpos.le hexp hcylinder
  have hlocalError := hlocalBound (ZMod q) (by simpa only [hcard] using hNLq) R w hw
  rw [hevent] at hlocalError
  have hcoreError := hcoreBound (ZMod q) (by simpa only [hcard] using hprime)
    (by simpa only [hcard] using hNCq)
    (by rw [hcard]; omega) Q hdom
  have hcoreIdentity := hCoreTransport (ZMod q) κ c Cbound Q hexp hreal hsuccesspos
    (fun D => ¬ CorePencilEvent (ρ / 4) D)
  have hcoreIdentity' :
      SelectedDeletion.jointMass κ (fun M s =>
        ¬ (SelectedDeletion.configuration M s).CoreConcentration ρ) =
      SelectedDeletion.successMass κ *
        deletionEventProbability Q (fun D => ¬ CorePencilEvent (ρ / 4) D.val) := by
    simpa only [SelectedJointAssembly.coreConcentration_iff_pencilEvent] using hcoreIdentity
  have hprobNonneg : 0 ≤
      deletionEventProbability Q (fun D => ¬ CorePencilEvent (ρ / 4) D.val) := by
    unfold deletionEventProbability
    apply Finset.sum_nonneg
    intro D _
    split_ifs
    · exact ENNReal.toReal_nonneg
    · exact le_rfl
  have hjointCore : SelectedDeletion.jointMass κ (fun M s =>
      ¬ (SelectedDeletion.configuration M s).CoreConcentration ρ) < a₀ / 4 := by
    rw [hcoreIdentity']
    calc
      _ ≤ 1 * deletionEventProbability Q
          (fun D => ¬ CorePencilEvent (ρ / 4) D.val) :=
        mul_le_mul_of_nonneg_right hsuccessone hprobNonneg
      _ < a₀ / 4 := by simpa only [one_mul] using hcoreError
  have hsmallO : SelectedDeletion.occupancyFailureMass κ ρ < a₀ / 4 := by
    exact hoccupancy.trans_lt (by simpa only [hcard] using hE q hNEq)
  have hsmallL : SelectedDeletion.jointMass κ (fun M s =>
      ¬ (SelectedDeletion.configuration M s).LocalCondition) < a₀ / 4 := by
    exact hlocalError.trans_lt (by simpa only [hcard] using hEL q hNELq)
  obtain ⟨C, hV, hCompat, hO, hConcentration, hLoc⟩ :=
    SelectedJointAssembly.exists_configuration_of_joint_errors κ hexp
      (by linarith)
  exact ⟨C, hV, hCompat, by simpa only [hcard] using hO, hConcentration, hLoc⟩

end

theorem mainResult_of_selectedDeletion_corePencil_local_deterministic
    (hdet : DeterministicReduction.{0})
    (hselected : SelectedDeletionResult.{0})
    (hcore : CorePencilResult.{0}) (hlocal : Local.PencilLocalResult.{0}) :
    MainResult :=
  mainResult_of_selected_results_and_transports hdet hselected hcore hlocal
    selectedLocalTransport_proof selectedCoreTransport_proof

end Balanced

end OAI
