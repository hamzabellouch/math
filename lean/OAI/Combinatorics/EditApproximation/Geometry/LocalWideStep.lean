import OAI.Combinatorics.EditApproximation.Geometry.GroupInputDependence

namespace OAI

/-! One concrete refinement entry, using direct local representative and
cell loops. Band data and previously gathered child tables are arguments;
no complete current-index child table is enumerated. -/

namespace EditApproximation

def rationalLocalWideStep {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q : ℕ) (tau a delta : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (childMass childInitial old current : Fin M → TargetInterval target.length → ℚ)
    (draw : CellGroupDraws M F Q) (online : List (PhysicalRationalAction M target.length))
    (q : TargetInterval target.length) : ℚ :=
  let fallback := rationalBellman parentInitial (fun q r => targetEndpointDistance q r) (128 * F)
    (rationalActualWideActions parent (localRefinementRepresentatives N P F a parentInitial q) P)
    (fun is => old is.1 is.2) q
  let groups := localCellGroupActions source target parent N P F exponent Q tau a parentInitial
    childMass childInitial current draw q
  let cone := rationalMinimum fallback
    (groups.map (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F)
      (fun is => current is.1 is.2) q))
  rationalRefinementUpdate delta cone
    (rationalOnlineMinimum (online.map
      (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F)
        (fun is => current is.1 is.2) q)))

theorem rationalLocalWideStep_eq {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q : ℕ) (tau a delta : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (childMass childInitial old current : Fin M → TargetInterval target.length → ℚ)
    (draw : CellGroupDraws M F Q) (online : List (PhysicalRationalAction M target.length))
    (q : TargetInterval target.length) (ha : 1 ≤ a) (hF : 1 ≤ F)
    (hinitial : 0 ≤ parentInitial q) (hold : ∀ i r, 0 ≤ old i r) (hcurrent : ∀ i r, 0 ≤ current i r)
    (hspatial : ∀ r, |parentInitial q - parentInitial r| ≤ 32 * F * targetEndpointDistance q r) :
    rationalLocalWideStep source target parent N P F exponent Q tau a delta parentInitial
        childMass childInitial old current draw online q =
      rationalWideStep parent (representativeList N P F a parentInitial) P parentInitial (128 * F) delta
        (fun is => old is.1 is.2) (fun is => current is.1 is.2)
        (completeCellGroupActions source target parent N P F exponent Q tau a parentInitial
          childMass childInitial current draw) online q := by
  have hbellman := localRefinementBellman_eq parent N P F a parentInitial
    (fun is => old is.1 is.2) q ha hF hinitial (fun is => hold is.1 is.2) hspatial
  have hgroups := localCellGroupMinimum_eq source target parent N P F exponent Q tau a parentInitial
    childMass childInitial current draw q
    (rationalBellman parentInitial (fun q r => targetEndpointDistance q r) (128 * F)
      (rationalActualWideActions parent (representativeList N P F a parentInitial) P)
      (fun is => old is.1 is.2) q) ha hF (rationalMinimum_le_fallback _ _) hcurrent hspatial
  unfold rationalLocalWideStep rationalWideStep rationalWideStepCone
  dsimp only
  rw [hbellman, hgroups]

theorem rationalLocalWideStep_bounds {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent Q : ℕ) (tau a delta : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (childMass childInitial old current : Fin M → TargetInterval target.length → ℚ)
    (draw : CellGroupDraws M F Q) (online : List (PhysicalRationalAction M target.length))
    (q : TargetInterval target.length) (hdelta : 0 ≤ delta) (hinitial : 0 ≤ parentInitial q)
    (hold : ∀ i r, 0 ≤ old i r) (hcurrent : ∀ i r, 0 ≤ current i r) :
    0 ≤ rationalLocalWideStep source target parent N P F exponent Q tau a delta parentInitial
      childMass childInitial old current draw online q ∧
    rationalLocalWideStep source target parent N P F exponent Q tau a delta parentInitial
      childMass childInitial old current draw online q ≤ parentInitial q := by
  let fallback := rationalBellman parentInitial (fun q r => targetEndpointDistance q r) (128 * F)
    (rationalActualWideActions parent (localRefinementRepresentatives N P F a parentInitial q) P)
    (fun is => old is.1 is.2) q
  let groups := localCellGroupActions source target parent N P F exponent Q tau a parentInitial
    childMass childInitial current draw q
  let cone := rationalMinimum fallback
    (groups.map (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F)
      (fun is => current is.1 is.2) q))
  have hfallback : 0 ≤ fallback := by
    apply (le_rationalMinimum_iff _ _ _).2
    refine ⟨hinitial, ?_⟩
    intro v hv
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
    exact rationalActionValue_pruned_lower _ _ _ _ action 0 (by positivity)
      (rationalActualWideActions_connection_nonneg _ _ _ action ha) (fun i => hold _ _)
  have hgroups : ∀ action ∈ groups, action ∈
      rationalActualWideActions parent (representativeList N P F a parentInitial) P := by
    intro action ha
    exact completeCellGroupActions_wide source target parent N P F exponent Q tau a parentInitial
      childMass childInitial current draw action
      (localCellGroupActions_subset source target parent N P F exponent Q tau a parentInitial
        childMass childInitial current draw q action ha)
  have hcone : 0 ≤ cone := by
    apply (le_rationalMinimum_iff _ _ _).2
    refine ⟨hfallback, ?_⟩
    intro v hv
    obtain ⟨action, ha, rfl⟩ := List.mem_map.mp hv
    exact rationalActionValue_pruned_lower _ _ _ _ action 0 (by positivity)
      (rationalActualWideActions_connection_nonneg _ _ _ action (hgroups action ha)) (fun i => hcurrent _ _)
  have hupper : cone ≤ parentInitial q := (rationalMinimum_le_fallback _ _).trans
    (rationalMinimum_le_fallback _ _)
  change 0 ≤ rationalRefinementUpdate delta cone _ ∧ rationalRefinementUpdate delta cone _ ≤ parentInitial q
  cases hmin : rationalOnlineMinimum (online.map
      (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F)
        (fun is => current is.1 is.2) q)) with
  | none => exact ⟨hcone, hupper⟩
  | some value =>
    exact ⟨le_min hcone ((div_nonneg hcone (by linarith)).trans (le_max_left _ _)),
      (min_le_left _ _).trans hupper⟩

end EditApproximation

end OAI
