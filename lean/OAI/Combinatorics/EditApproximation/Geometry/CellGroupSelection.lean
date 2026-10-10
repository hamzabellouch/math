import OAI.Combinatorics.EditApproximation.Geometry.GroupCells
import OAI.Combinatorics.EditApproximation.Geometry.BandGroupSampling
import OAI.Combinatorics.EditApproximation.Numerics.RationalWideStep
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Literal unskipped groups of whole cells and their selected wide actions. -/

namespace EditApproximation

open Finset



theorem cellUnskippedBands_length_le {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F thetaExponent : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ) (cell : ℕ × ℕ)
    (hb : ∃ e : ℕ, b = 2 ^ e) (hP : ∃ e : ℕ, P = 2 ^ e) :
    (cellUnskippedBands source target parent b P F thetaExponent tau a parentInitial child initial cell).length ≤
      (P + 1) ^ 2 := by
  have htheta : 0 ≤ (2 : ℚ) ^ (-(thetaExponent : ℤ)) ∧
      (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ 1 := by
    refine ⟨(zpow_pos (by norm_num : (0 : ℚ) < 2) _).le, ?_⟩
    rw [zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 2))
  exact (List.length_filterMap_le _ _).trans
    (cellRepresentativeStates_length_le a parentInitial _ cell htheta hb hP)

namespace UnskippedBand

theorem canonicalRounded_congr {ny M : ℕ} (thetaExponent b : ℕ)
    (band band' : List (Fin M → TargetInterval ny)) (heq : band = band')
    (hnonempty : band ≠ []) (hnonempty' : band' ≠ [])
    (initial : Fin M → TargetInterval ny → ℚ) :
    canonicalRoundedBandAction thetaExponent b band hnonempty initial =
      canonicalRoundedBandAction thetaExponent b band' hnonempty' initial := by
  cases heq
  rfl



theorem rationalAction_wide_mem {α : Type*} {source target : List α} {M b P thetaExponent : ℕ}
    {parent : TargetInterval source.length} {tau F : ℚ}
    {child initial : Fin M → TargetInterval target.length → ℚ}
    (member : UnskippedBand source target parent b P thetaExponent tau F child initial)
    (representatives : List (ℕ × TargetInterval target.length)) (hrep : (b, member.center) ∈ representatives) :
    member.rationalAction ∈ rationalActualWideActions parent representatives P := by
  apply List.mem_flatMap.mpr
  exact ⟨(b, member.center), hrep, List.mem_map.mpr ⟨member.rounded, member.wide_guard, rfl⟩⟩

theorem rounded_cost {α : Type*} {source target : List α} {M b P thetaExponent : ℕ}
    {parent : TargetInterval source.length} {tau F : ℚ}
    {child initial : Fin M → TargetInterval target.length → ℚ}
    (member : UnskippedBand source target parent b P thetaExponent tau F child initial)
    (htau : 0 < tau) (value : Fin M → TargetInterval target.length → ℚ)
    (action : Fin M → TargetInterval target.length) (haction : action ∈ member.actions)
    (delta L : ℚ) (hL : 0 ≤ L)
    (hspatial : ∀ i s t, value i s ≤ (1 + delta) * value i t + L * targetEndpointDistance s t) :
    rationalEndpointActionValue member.center member.rounded value ≤
      (1 + delta) * (∑ i, value i (action i)) +
        (6 * L + 2) * (2 : ℚ) ^ (-(thetaExponent : ℤ)) * ∑ i, member.envelope i := by
  have hnonempty := member.nonempty
  by_cases hempty : wideActionList M parent member.center b P = []
  · simp only [representativeBandActions, dite_eq_left hempty] at hnonempty
    exact False.elim (hnonempty rfl)
  · by_cases hZ : 0 < rationalWideActionMinimum parent member.center b P hempty child
    · have hband : member.actions = computedBandActions parent member.center b P tau
          ((2 : ℚ) ^ (-(thetaExponent : ℤ)))
          (rationalStateGap (substring source parent.lo parent.hi) target member.center /
            rationalWideActionMinimum parent member.center b P hempty child) child := by
        simp only [actions, representativeBandActions, dite_eq_right hempty, ite_eq_left hZ]
      have hne : computedBandActions parent member.center b P tau
          ((2 : ℚ) ^ (-(thetaExponent : ℤ)))
          (rationalStateGap (substring source parent.lo parent.hi) target member.center /
            rationalWideActionMinimum parent member.center b P hempty child) child ≠ [] := by
        rw [← hband]
        exact member.nonempty
      have ha := haction
      rw [hband] at ha
      have hcost := canonicalRoundedBandAction_cost parent member.center thetaExponent b P tau _ htau
        child initial value hne action ha delta L hL hspatial
      have hround := canonicalRounded_congr thetaExponent b _ _ hband member.nonempty hne initial
      change member.rounded = _ at hround
      rw [hround]
      simpa only [envelope, hband] using hcost
    · simp only [representativeBandActions, dite_eq_right hempty, ite_eq_right hZ] at hnonempty
      exact False.elim (hnonempty rfl)

end UnskippedBand



theorem chooseCellGroupAction_wide_mem {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N b P F thetaExponent Q : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial value : Fin M → TargetInterval target.length → ℚ) (cell : ℕ × ℕ)
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (hb : b ∈ dyadicScales N) (action : RationalBellmanAction
      (TargetInterval target.length) (Fin M × TargetInterval target.length) M)
    (hselected : chooseCellGroupAction source target parent b P F thetaExponent Q tau a
      parentInitial child initial value cell draw = some action) :
    action ∈ rationalActualWideActions parent (representativeList N P F a parentInitial) P := by
  unfold chooseCellGroupAction at hselected
  dsimp only at hselected
  split_ifs at hselected with hempty
  have heq := Option.some.inj hselected
  rw [← heq]
  apply UnskippedBand.rationalAction_wide_mem
  apply cellRepresentativeStates_mem_representatives a parentInitial _ cell _ hb
  apply (unskippedBandList_mem_iff _ _).mp
  exact (chooseUnskippedGroup_spec Q value _ hempty draw).1

theorem group_rounding_coefficient {F L : ℚ} (hF : 1 ≤ F) (hL : 2 ≤ L) :
    (6 * L + 2) * (64 * F) + 2 * L ≤ 512 * L * F := by
  have hF0 : 0 ≤ F := by linarith only [hF]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hlarge := mul_le_mul_of_nonneg_right hL (mul_nonneg (by norm_num : (0 : ℚ) ≤ 64) hF0)
  have hcell := mul_le_mul_of_nonneg_left hF (mul_nonneg (by norm_num : (0 : ℚ) ≤ 2) hL0)
  have hprod := mul_nonneg hL0 hF0
  nlinarith only [hlarge, hcell, hprod]

/-- Estimated minimization in an actual whole cell gives the group cone
bound simultaneously for every action of the specified member's band. -/
theorem chooseCellGroup_cone_bound {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F thetaExponent Q : ℕ) (tau a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial value : Fin M → TargetInterval target.length → ℚ) (cell : ℕ × ℕ)
    (hnonempty : cellUnskippedBands source target parent b P F thetaExponent tau a
      parentInitial child initial cell ≠ [])
    (draw : ∀ scale : Fin (groupDyadicScales M b F).length,
      Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) → Fin M)
    (specified : UnskippedBand source target parent b P thetaExponent tau F child initial)
    (hspecified : specified ∈ cellUnskippedBands source target parent b P F thetaExponent tau a
      parentInitial child initial cell)
    (delta L gamma : ℚ) (hF : 1 ≤ F) (hL : 2 ≤ L) (htau : 0 < tau)
    (hspatial : ∀ i s t, value i s ≤ (1 + delta) * value i t + L * targetEndpointDistance s t)
    (haccurate : ∀ member ∈ cellUnskippedBands source target parent b P F thetaExponent tau a
        parentInitial child initial cell,
      |dyadicUnskippedGroupEstimate Q value member draw -
        rationalEndpointActionValue member.center member.rounded value| ≤ gamma * b)
    (action : Fin M → TargetInterval target.length) (haction : action ∈ specified.actions)
    (q : TargetInterval target.length) :
    let selected := chooseUnskippedGroup Q value
      (cellUnskippedBands source target parent b P F thetaExponent tau a parentInitial child initial cell)
      hnonempty draw
    rationalActionValue (fun q r => targetEndpointDistance q r) L (fun is => value is.1 is.2) q
        selected.rationalAction ≤
      L * targetEndpointDistance q specified.center + (1 + delta) * (∑ i, value i (action i)) +
        (2 * gamma + 512 * L * F * (2 : ℚ) ^ (-(thetaExponent : ℤ))) * b := by
  let members := cellUnskippedBands source target parent b P F thetaExponent tau a
    parentInitial child initial cell
  let selected := chooseUnskippedGroup Q value members hnonempty draw
  have hselected : selected ∈ members := (chooseUnskippedGroup_spec Q value members hnonempty draw).1
  have hcost := chooseUnskippedGroup_cost_le Q value members hnonempty draw specified hspecified
    (gamma * b) haccurate
  change rationalEndpointActionValue selected.center selected.rounded value ≤
    rationalEndpointActionValue specified.center specified.rounded value + 2 * (gamma * b) at hcost
  have hrounded := specified.rounded_cost htau value action haction delta L (by linarith only [hL]) hspatial
  have hcenterCell (member : UnskippedBand source target parent b P thetaExponent tau F child initial)
      (hm : member ∈ members) : member.center ∈
        cellTargetStates target.length (seedGridSpacing b P) ((2 : ℚ) ^ (-(thetaExponent : ℤ)) * b) cell := by
    have hc := (unskippedBandList_mem_iff _ member).mp hm
    exact (List.mem_filter.mp hc).1
  have hdiam := cellTargetStates_diameter cell (by unfold seedGridSpacing; omega)
    specified.center selected.center (hcenterCell specified hspecified) (hcenterCell selected hselected)
  have htriangle : (targetEndpointDistance q selected.center : ℚ) ≤
      targetEndpointDistance q specified.center + targetEndpointDistance specified.center selected.center := by
    have h := targetEndpointDistance_triangle q specified.center selected.center
    have h' : (targetEndpointDistance q selected.center : ℚ) ≤
        targetEndpointDistance specified.center selected.center + targetEndpointDistance q specified.center := by
      exact_mod_cast h
    simpa only [add_comm] using h'
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hdist := mul_le_mul_of_nonneg_left (htriangle.trans (add_le_add_right hdiam _)) hL0
  have htheta : 0 ≤ (2 : ℚ) ^ (-(thetaExponent : ℤ)) := (zpow_pos (by norm_num : (0 : ℚ) < 2) _).le
  have hsum := mul_le_mul_of_nonneg_left specified.sum_guard
    (mul_nonneg (by linarith only [hL0] : 0 ≤ 6 * L + 2) htheta)
  change (6 * L + 2) * (2 : ℚ) ^ (-(thetaExponent : ℤ)) * (∑ i, specified.envelope i) ≤
    (6 * L + 2) * (2 : ℚ) ^ (-(thetaExponent : ℤ)) * (64 * F * b) at hsum
  have hcoef := mul_le_mul_of_nonneg_right (group_rounding_coefficient (F := (F : ℚ)) (L := L)
    (by exact_mod_cast hF) hL)
    (mul_nonneg htheta (Nat.cast_nonneg (α := ℚ) b))
  dsimp only [rationalActionValue, UnskippedBand.rationalAction]
  dsimp only [rationalEndpointActionValue] at hcost hrounded
  nlinarith only [hcost, hrounded, hdist, hsum, hcoef]

end EditApproximation

end OAI
