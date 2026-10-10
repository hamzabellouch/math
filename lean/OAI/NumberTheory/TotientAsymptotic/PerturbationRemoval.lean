import OAI.NumberTheory.TotientAsymptotic.PerturbationEnclosure
import OAI.NumberTheory.TotientAsymptotic.NormalizedShell
import OAI.NumberTheory.TotientAsymptotic.CofactorWitnessAggregation
import OAI.NumberTheory.TotientAsymptotic.BandRemoval

namespace OAI

/-! Removing the perturbed prefix inequalities with their full arithmetic weights. -/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory

namespace TotientAsymptotic

/-- All `xi`-perturbations in the retained prefix have negligible total
weighted volume, uniformly over every finite family of actual witnesses. -/
theorem witness_perturbation_removal (hbox : FordUnitPrimeBoxInput)
    (hmertens : MertensProductInput) (hren : FordRenewalInput) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (nhds 0) ∧
      ∀ᶠ H : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      ∀ W : Finset (TailDatum H), (∀ η ∈ W, IsWitness H (theta x) η) →
      (∑ η ∈ W, ((w η).totient : ℝ)⁻¹*
        volume.real ((perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H) \
          tailPrefixRegion x H η))/G x (m x) ≤ ε H := by
  obtain ⟨C, hC, hagg⟩ := all_cofactor_witness_aggregation hbox hmertens
  obtain ⟨δ, hδ, hnorm⟩ := normalized_additive_shell_loss hren (4*(lam/rho))
  refine ⟨fun H => C*δ H, by simpa using hδ.const_mul C, ?_⟩
  filter_upwards [hnorm, eventually_tail_cut_separated, eventually_ge_atTop 2]
    with H hnormH hcuts hH
  have hPH := P_lt_self hH
  filter_upwards [hnormH, theta_eventually_mem,
    B_tendsto.eventually (eventually_gt_atTop (0 : ℝ)),
    m_tendsto.eventually (eventually_ge_atTop (H+2))] with x hnormX hs hB hm
  intro W hW
  have hdim : L x H=R x H+(H-P H) := by unfold L R; omega
  have hn : 0 < R x H+(H-P H) := by unfold R; omega
  have hnorm' : Real.exp ((4*(lam/rho))*cofactorScale H)*
      volume.real (additiveBoxShell x (R x H) (R x H+(H-P H)) (Nat.le_add_right _ _))/
        G x (m x) ≤ δ H := by
    rw [hdim] at hnormX
    exact hnormX (Nat.le_add_right _ _)
  have hsum := hagg hs hPH.le W
    (fun η => (perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H) \ tailPrefixRegion x H η)
    (additiveBoxShell x (R x H) (R x H+(H-P H)) (Nat.le_add_right _ _)) hW
    (fun η _ => ((measurableSet_perturbedTailPrefixRegion x H η).inter
      (measurableSet_prefixBandRegion x H)).diff (measurableSet_tailPrefixRegion x H η))
    (additiveBoxShell_volume_ne_top x (Nat.le_add_right _ _) hn)
    (by
      intro η hη u hu v hv
      exact perturbed_loss_enclosure hB.le hcuts.1 hPH (by omega) (hW η hη) hu hv)
  calc
    _ ≤ (C*Real.exp ((4*(lam/rho))*cofactorScale H)*
        volume.real (additiveBoxShell x (R x H) (R x H+(H-P H)) (Nat.le_add_right _ _)))/
          G x (m x) := div_le_div_of_nonneg_right hsum (G_pos hB _).le
    _ = C*(Real.exp ((4*(lam/rho))*cofactorScale H)*
        volume.real (additiveBoxShell x (R x H) (R x H+(H-P H)) (Nat.le_add_right _ _))/
          G x (m x)) := by ring
    _ ≤ C*δ H := mul_le_mul_of_nonneg_left hnorm' hC.le

end TotientAsymptotic

end

end OAI
