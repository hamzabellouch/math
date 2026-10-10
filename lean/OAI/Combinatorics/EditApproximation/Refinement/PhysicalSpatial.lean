import OAI.Combinatorics.EditApproximation.Refinement.PhysicalInitial

namespace OAI

/-! Spatial regularity of the actual local initial table and physical warmup. -/

namespace EditApproximation

theorem physicalInitialTable_spatial {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A a : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A) (ha : 1 ≤ a) (hfactor : A ≤ a * F)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (node : PhysicalNode M J) (q q' : TargetInterval target.length) :
    physicalInitialTable source target U N P F A a (node, q) ≤
      physicalInitialTable source target U N P F A a (node, q') +
        (32 * F : ℚ) * targetEndpointDistance q q' := by
  unfold physicalInitialTable
  dsimp only
  split_ifs with hleaf
  · rw [shortSourceCost_eq_edit _ _ hleaf, shortSourceCost_eq_edit _ _ hleaf]
    have hcost : (stateEditCost (physicalSource source node) target q : ℚ) ≤
        stateEditCost (physicalSource source node) target q' + targetEndpointDistance q q' := by
      exact_mod_cast stateEditCost_spatial (physicalSource source node) target q q'
    have hFr : (1 : ℚ) ≤ F := by exact_mod_cast hF
    have hcharge : (targetEndpointDistance q q' : ℚ) ≤
        (32 * F : ℚ) * targetEndpointDistance q q' := by
      nlinarith only [hFr, Nat.cast_nonneg (α := ℚ) (targetEndpointDistance q q')]
    change (stateEditCost (physicalSource source node) target q : ℚ) ≤
      stateEditCost (physicalSource source node) target q' + _
    linarith only [hcost, hcharge]
  · rw [localInitialConeTable_eq_global _ _ _ N P F A a hP hF hA ha hfactor
        (fun r => physical_state_cost_le source target N hsize (node, r)) (fun r => hseed (node, r)) q,
      localInitialConeTable_eq_global _ _ _ N P F A a hP hF hA ha hfactor
        (fun r => physical_state_cost_le source target N hsize (node, r)) (fun r => hseed (node, r)) q']
    exact globalInitialConeTable_spatial _ _ _ N P F A a q q'

theorem physicalBellman_spatial {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (hL : 0 ≤ L) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (hinit : ∀ node q q', initial (node, q) ≤ initial (node, q') + L * targetEndpointDistance q q')
    (value : PhysicalEntry M J target.length → ℝ) (node : PhysicalNode M J)
    (q q' : TargetInterval target.length) :
    physicalBellman source target P L initial representatives value (node, q) ≤
      physicalBellman source target P L initial representatives value (node, q') +
        L * targetEndpointDistance q q' := by
  classical
  unfold physicalBellman
  dsimp only
  split_ifs with hbelow hleaf
  · exact hinit node q q'
  · exact finiteBellman_spatial (fun s => initial (node, s))
      (fun s t => targetEndpointDistance s t) L
      (actualWideActions (physicalSourceInterval source.length node) (representatives node) P)
      (fun is => value (physicalChild node hbelow is.1, is.2)) hL q q' (hinit node q q')
      (fun center => by exact_mod_cast targetEndpointDistance_triangle q q' center)
  · exact hinit node q q'

theorem physicalWarmup_spatial {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (hL : 0 ≤ L) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (hinit : ∀ node q q', initial (node, q) ≤ initial (node, q') + L * targetEndpointDistance q q')
    (t : ℕ) (node : PhysicalNode M J) (q q' : TargetInterval target.length) :
    physicalWarmup source target P L initial representatives t (node, q) ≤
      physicalWarmup source target P L initial representatives t (node, q') +
        L * targetEndpointDistance q q' := by
  cases t with
  | zero => exact hinit node q q'
  | succ t => exact physicalBellman_spatial source target P L hL initial representatives hinit _ node q q'

end EditApproximation

end OAI
