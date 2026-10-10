import OAI.Computability.BinPacking.Inventory.IntegralSpeciesCounts
import OAI.Computability.BinPacking.Inventory.PhysicalPoolLift
import OAI.Computability.BinPacking.Packing.ConstructLocalState
import OAI.Computability.BinPacking.Packing.ExtractedCover
import OAI.Computability.BinPacking.Packing.LocalTemplateBases

namespace OAI

noncomputable section

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

theorem card_template : Fintype.card D.Template = 2 * D.B := by
  simp only [Template, Fintype.card_sigma, Fintype.card_prod, Fintype.card_bool,
    D.card_localBin]
  rw [← Finset.mul_sum]
  rfl

def statePoolTemplates (hn : D.graph.n = 2 * D.k)
    (S : ∀ v s, D.LocalState v s) :
    PoolTemplates D.packingInstance D.Template (GlobalSpecies D.graph) FlagSpecies where
  base := D.templateBase S
  globalPool := D.physicalGlobalPool
  flagPool := D.physicalFlagPool
  globalSpecies := D.templateGlobalSpecies
  flagSpecies := D.templateFlagSpecies
  global_nonempty := by
    intro t
    apply (D.physicalGlobalPool_nonempty_iff _).mpr
    have hc := D.doubled_stateGlobalSpecies_count hn (D.templateGlobalSpecies t)
    have hp : 0 < (Finset.univ.filter (fun q : D.Template =>
        D.templateGlobalSpecies q = D.templateGlobalSpecies t)).card := by
      exact Finset.card_pos.mpr ⟨t, by simp⟩
    change (Finset.univ.filter (fun q : D.Template =>
      D.templateGlobalSpecies q = D.templateGlobalSpecies t)).card = _ at hc
    omega
  flag_nonempty := by
    intro t
    apply (D.physicalFlagPool_nonempty_iff _).mpr
    have hc := D.doubled_stateFlagSpecies_count (D.templateFlagSpecies t)
    have hp : 0 < (Finset.univ.filter (fun q : D.Template =>
        D.templateFlagSpecies q = D.templateFlagSpecies t)).card := by
      exact Finset.card_pos.mpr ⟨t, by simp⟩
    change (Finset.univ.filter (fun q : D.Template =>
      D.templateFlagSpecies q = D.templateFlagSpecies t)).card = _ at hc
    omega
  base_global := fun t =>
    (D.labeledItems_disjoint_physicalGlobalPool (D.templateGlobalSpecies t)).mono_left
      (D.templateBase_subset_labeledItems S t)
  base_flag := fun t =>
    (D.labeledItems_disjoint_physicalFlagPool (D.templateFlagSpecies t)).mono_left
      (D.templateBase_subset_labeledItems S t)
  global_flag := fun t => D.physicalGlobalPool_disjoint_physicalFlagPool
    (D.templateGlobalSpecies t) (D.templateFlagSpecies t)
  capacity := by
    intro t u f
    obtain ⟨j, hj⟩ := (D.mem_physicalGlobalPool (D.templateGlobalSpecies t) u.val).mp
      u.property
    obtain ⟨l, hl⟩ := (D.mem_physicalFlagPool (D.templateFlagSpecies t) f.val).mp
      f.property
    rw [← hj, ← hl]
    exact D.templateBase_capacity S t ⟨D.templateGlobalSpecies t, j⟩
      ⟨D.templateFlagSpecies t, l⟩ rfl rfl

theorem statePoolTemplates_feasible (hn : D.graph.n = 2 * D.k)
    (S : ∀ v s, D.LocalState v s) :
    IndividualFeasible D.packingInstance (D.statePoolTemplates hn S).weights := by
  apply (D.statePoolTemplates hn S).weights_feasible D.labeledItems
  · exact D.templateBase_appearance_count S
  · intro s
    change (Finset.univ.filter (fun t : D.Template =>
      D.templateGlobalSpecies t = s)).card = 2 * (D.physicalGlobalPool s).card
    rw [D.card_physicalGlobalPool]
    exact D.doubled_stateGlobalSpecies_count hn s
  · intro f
    change (Finset.univ.filter (fun t : D.Template =>
      D.templateFlagSpecies t = f)).card = 2 * (D.physicalFlagPool f).card
    rw [D.card_physicalFlagPool]
    exact D.doubled_stateFlagSpecies_count f
  · exact D.physicalInventory_indicator_partition

theorem statePoolTemplates_objective (hn : D.graph.n = 2 * D.k)
    (S : ∀ v s, D.LocalState v s) :
    FractionalCover.objective (D.statePoolTemplates hn S).weights = (D.B : ℝ) := by
  rw [(D.statePoolTemplates hn S).objective_weights, D.card_template]
  push_cast
  ring

theorem ofCompetingTrees_physical_witness (G : GraphInput) {d : ℕ}
    (T : CompetingTrees d) (hd : 0 < d) (R k : ℕ) (hn : G.n = 2 * k) :
    ∃ w : IndividualConfiguration (ofCompetingTrees G T R k).packingInstance → ℝ,
      IndividualFeasible (ofCompetingTrees G T R k).packingInstance w ∧
      FractionalCover.objective w = ((ofCompetingTrees G T R k).B : ℝ) := by
  let D := ofCompetingTrees G T R k
  let S : ∀ v s, D.LocalState v s := constructedLocalState G T hd R k
  exact ⟨(D.statePoolTemplates hn S).weights,
    D.statePoolTemplates_feasible hn S, D.statePoolTemplates_objective hn S⟩

theorem ofCompetingTrees_bothLP_eq (G : GraphInput) {d : ℕ}
    (T : CompetingTrees d) (hd : 0 < d) (R k : ℕ) (hn : G.n = 2 * k) :
    individualLP (ofCompetingTrees G T R k).packingInstance =
        ((ofCompetingTrees G T R k).B : ℝ) ∧
      typeLP (ofCompetingTrees G T R k).packingInstance =
        ((ofCompetingTrees G T R k).B : ℝ) := by
  obtain ⟨w, hw, hobj⟩ := ofCompetingTrees_physical_witness G T hd R k hn
  exact bothLP_eq_of_physical_witness _ _
    ((ofCompetingTrees G T R k).packingInstance_n (by change k ≤ G.n; omega))
    (fun i => ((ofCompetingTrees G T R k).packingInstance_size_mem_interval i).1)
    w hw hobj

end BinPackingGap.InventoryData

end

namespace BinPackingGap

theorem reduction_bothLP_eq (c : ℕ) (rho : ℝ) (G : GraphInput) (k : ℕ)
    (hn : G.n = 2 * k) :
    individualLP (reductionInstance c rho G k) =
        (reductionBinBound c rho G k : ℝ) ∧
      typeLP (reductionInstance c rho G k) =
        (reductionBinBound c rho G k : ℝ) :=
  InventoryData.ofCompetingTrees_bothLP_eq G (reductionTrees c rho)
    (depthDemand_pos c rho) _ k hn

end BinPackingGap

end OAI
