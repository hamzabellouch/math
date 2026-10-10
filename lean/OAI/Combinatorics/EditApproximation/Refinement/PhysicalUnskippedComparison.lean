import OAI.Combinatorics.EditApproximation.Refinement.PhysicalOnlineBand
import OAI.Combinatorics.EditApproximation.Geometry.CellGroupSelection

namespace OAI

/-! A comparison action in the physical band passes all literal guards and belongs to its whole cell. -/

namespace EditApproximation

open Finset

theorem representativeList_grid_eligibility {n N P F b : ℕ} (a : ℚ)
    (initial : TargetInterval n → ℚ) (r : TargetInterval n)
    (hrep : (b, r) ∈ representativeList N P F a initial) :
    (seedGridSpacing b P ∣ r.lo ∧ seedGridSpacing b P ∣ r.hi) ∧
      (b : ℚ) / (4 * a) ≤ initial r ∧ initial r ≤ 8 * F * b := by
  obtain ⟨bb, _, hmem⟩ := List.mem_flatMap.mp hrep
  obtain ⟨rr, hrr, heq⟩ := List.mem_map.mp hmem
  have hb : bb = b := congrArg Prod.fst heq
  have hr : rr = r := congrArg Prod.snd heq
  subst bb rr
  have h := of_decide_eq_true (List.mem_filter.mp hrr).2
  exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

theorem physical_comparison_unskipped {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (hM : 0 < M) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (b thetaExponent : ℕ) (hb : 0 < b) (hbPower : ∃ e : ℕ, b = 2 ^ e)
    (hPPower : ∃ e : ℕ, P = 2 ^ e) (tau : ℚ) (htau : 0 < tau)
    (htheta : (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ 1 / 2)
    (hsmall : (32 * F : ℚ) * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ 1)
    (hsmall64 : (64 * F : ℚ) * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ 4)
    (hscale : (M : ℚ) ≤ (2 : ℚ) ^ (-(thetaExponent : ℤ)) * P)
    (r : TargetInterval target.length) (hrep : (b, r) ∈ stageRepresentatives source target U N P F A node)
    (comparison : Fin M → TargetInterval target.length)
    (hcomparison : comparison ∈ representativeBandActions source target (physicalSourceInterval source.length node)
      r b P tau ((2 : ℚ) ^ (-(thetaExponent : ℤ)))
        (physicalBandChildMassTable source target U N P F A T node hbelow))
    (hcost : (∑ i, (stateEditCost (physicalSource source (physicalChild node hbelow i)) target (comparison i) : ℚ)) ≤
      4 * b) :
    ∃ member : UnskippedBand source target (physicalSourceInterval source.length node) b P thetaExponent tau F
        (physicalBandChildMassTable source target U N P F A T node hbelow)
        (physicalBandChildInitial source target U N P F A node hbelow),
      member ∈ cellUnskippedBands source target (physicalSourceInterval source.length node)
        b P F thetaExponent tau (refinementFactor A F)
        (fun s => stageInitial source target U N P F A (node, s))
        (physicalBandChildMassTable source target U N P F A T node hbelow)
        (physicalBandChildInitial source target U N P F A node hbelow)
        (targetCell ((2 : ℚ) ^ (-(thetaExponent : ℤ)) * b) r) ∧
      member.center = r ∧ comparison ∈ member.actions := by
  let parent := physicalSourceInterval source.length node
  let theta : ℚ := (2 : ℚ) ^ (-(thetaExponent : ℤ))
  let child := physicalBandChildMassTable source target U N P F A T node hbelow
  let initial := physicalBandChildInitial source target U N P F A node hbelow
  let band := representativeBandActions source target parent r b P tau theta child
  change comparison ∈ band at hcomparison
  have htheta0 : 0 < theta := zpow_pos (by norm_num : (0 : ℚ) < 2) _
  have hband : band ≠ [] := by
    intro hnil
    have h := hcomparison
    change comparison ∈ band at h
    rw [hnil] at h
    exact List.not_mem_nil h
  by_cases hwide : wideActionList M parent r b P = []
  · simp only [band, representativeBandActions, dite_eq_left hwide, List.not_mem_nil] at hcomparison
  · by_cases hZ : 0 < rationalWideActionMinimum parent r b P hwide child
    · let velocity := rationalStateGap (substring source parent.lo parent.hi) target r /
        rationalWideActionMinimum parent r b P hwide child
      let computed := computedBandActions parent r b P tau theta velocity child
      have heq : band = computed := by
        simp only [band, representativeBandActions, dite_eq_right hwide, ite_eq_left hZ, computed, velocity]
      have hc : comparison ∈ computed := heq ▸ hcomparison
      have hcn : computed ≠ [] := by rw [← heq]; exact hband
      have hfactor := refinementFactor_spec A F (by omega)
      have hinitial := physicalInitialTable_bounds source target U N P F A (refinementFactor A F)
        hsize hP hF hA hfactor.1 hfactor.2 hseed
      have hgap (i : Fin M) (s : TargetInterval target.length) :
          |rationalStateGap (physicalSource source (physicalChild node hbelow i)) target s| ≤ initial i s := by
        exact (le_max_right _ _).trans (hinitial (physicalChild node hbelow i, s)).1
      have hinonneg (i : Fin M) : 0 ≤ initial i (comparison i) := (abs_nonneg _).trans (hgap i _)
      have hispatial (i : Fin M) (s t : TargetInterval target.length) :
          initial i s ≤ initial i t + (32 * F : ℚ) * targetEndpointDistance s t :=
        physicalInitialTable_spatial source target U N P F A (refinementFactor A F)
          hsize hP hF hA hfactor.1 hfactor.2 hseed (physicalChild node hbelow i) s t
      have hiupper (i : Fin M) : initial i (comparison i) ≤
          2 * F * stateEditCost (physicalSource source (physicalChild node hbelow i)) target (comparison i) :=
        (hinitial (physicalChild node hbelow i, comparison i)).2
      have hsumC := bandChildEnvelope_sum_guard source target parent r b P hb hM tau theta velocity
        htau htheta0.le child initial comparison hc (32 * F) F (by positivity)
        (by exact_mod_cast hF) hsmall hinonneg hispatial hiupper hcost
      have hsum : (∑ i, bandChildEnvelope b band initial i) ≤ 64 * F * b := by
        rw [heq]
        exact hsumC
      have hguards := roundedBandAction_guards source target parent r thetaExponent tau velocity child initial
        (computed.head hcn) (List.head_mem hcn) hM (by omega) hbPower hPPower hscale F hsmall64 htheta hgap hsumC
      have hcanonical : canonicalRoundedBandAction thetaExponent b band hband initial =
          roundedBandAction thetaExponent b computed initial (computed.head hcn) :=
        canonicalRoundedBandAction_congr thetaExponent b band computed hband hcn initial heq
      have hwideGuard : canonicalRoundedBandAction thetaExponent b band hband initial ∈ wideActionList M parent r b P := by
        rw [hcanonical]
        exact hguards.1
      have hgapGuard : ∀ i, |rationalStateGap (physicalSource source (physicalChild node hbelow i)) target
          (canonicalRoundedBandAction thetaExponent b band hband initial i)| ≤ 2 * bandChildEnvelope b band initial i := by
        intro i
        rw [hcanonical, heq]
        exact hguards.2 i
      let member : UnskippedBand source target parent b P thetaExponent tau F child initial :=
        ⟨r, hband, hsum, hwideGuard, hgapGuard⟩
      refine ⟨member, ?_, rfl, hcomparison⟩
      apply (unskippedBandList_mem_iff _ member).mpr
      have hgrid := representativeList_grid_eligibility (refinementFactor A F)
        (fun s => stageInitial source target U N P F A (node, s)) r hrep
      exact cellRepresentativeStates_contains _ _ theta r (mul_pos htheta0 (by exact_mod_cast hb)) hgrid.1 hgrid.2
    · simp only [band, representativeBandActions, dite_eq_right hwide, ite_eq_right hZ, List.not_mem_nil] at hcomparison

end EditApproximation

end OAI
