import OAI.Computability.BinPacking.Inventory.IntegralSpeciesCounts
import OAI.Computability.BinPacking.Inventory.SpeciesAllocation
import OAI.Computability.BinPacking.Packing.ConstructLocalState
import OAI.Computability.BinPacking.Packing.ExtractedCover
import OAI.Computability.BinPacking.Packing.LocalTemplateBases
import OAI.Computability.BinPacking.Packing.PhysicalRolePacking

namespace OAI

noncomputable section

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

def integralGlobalAllocation (C : Finset D.Vertex) (hC : C.card = D.k) :
    D.PhysicalBins ≃ D.GlobalCopy := by
  classical
  exact SpeciesAllocation.allocation (D.integralGlobalSpecies C) D.globalStock
    (fun s => by rw [Fintype.card_subtype]; exact D.card_integralGlobalSpecies C hC s)

def integralFlagAllocation : D.PhysicalBins ≃ D.FlagCopy := by
  classical
  exact SpeciesAllocation.allocation D.integralFlagSpecies D.flagStock
    (fun s => by rw [Fintype.card_subtype]; exact D.card_integralFlagSpecies s)

@[simp] theorem integralGlobalAllocation_species (C : Finset D.Vertex)
    (hC : C.card = D.k) (b : D.PhysicalBins) :
    (D.integralGlobalAllocation C hC b).1 = D.integralGlobalSpecies C b :=
  SpeciesAllocation.allocation_species _ _ _ b

@[simp] theorem integralFlagAllocation_species (b : D.PhysicalBins) :
    (D.integralFlagAllocation b).1 = D.integralFlagSpecies b :=
  SpeciesAllocation.allocation_species _ _ _ b

def integralRoleEquiv (C : Finset D.Vertex) (hC : C.card = D.k)
    (S : ∀ v, D.LocalState v (D.coverSelected C v)) :
    ∀ r : Role, D.PhysicalBins ≃ D.RoleCopies r
  | .x => Equiv.sigmaCongrRight fun v => D.stateRowEquiv v (D.coverSelected C v)
  | .anchor => Equiv.sigmaCongrRight fun v => (S v).anchorAtEquiv
  | .«global» => D.integralGlobalAllocation C hC
  | .«local» => Equiv.sigmaCongrRight fun v => (S v).localAtEquiv
  | .flag => D.integralFlagAllocation

theorem integralRoleEquiv_capacity (C : Finset D.Vertex)
    (hC : C.card = D.k) (hcover : D.graph.IsCover C)
    (S : ∀ v, D.LocalState v (D.coverSelected C v)) (bin : D.PhysicalBins) :
    (∑ r : Role, D.itemSize ⟨r, D.integralRoleEquiv C hC S r bin⟩) ≤ 1 := by
  rcases bin with ⟨v, b | j⟩
  · change (∑ r, D.itemSize (D.localTemplateItems
      (D.stateMainRow v (D.coverSelected C v) b)
      (.inl ((S v).anchorEquiv b))
      (D.integralGlobalAllocation C hC ⟨v, .inl b⟩)
      (.inl ((S v).localEquiv b))
      (D.integralFlagAllocation ⟨v, .inl b⟩) r)) ≤ 1
    exact (D.stateMainTemplate_feasible_iff (D.coverSelected C v) b
      ((S v).anchorEquiv b) ((S v).localEquiv b) _ _
      (D.integralGlobalAllocation_species C hC ⟨v, .inl b⟩)
      (D.integralFlagAllocation_species ⟨v, .inl b⟩)).mpr
        ((S v).completion_le_deadline b)
  · change (∑ r, D.itemSize (D.localTemplateItems
      (.inr (D.coverSelected C v, j)) (.inr j)
      (D.integralGlobalAllocation C hC ⟨v, .inr j⟩) (.inr j)
      (D.integralFlagAllocation ⟨v, .inr j⟩) r)) ≤ 1
    apply (D.edgeTemplate_feasible_iff (D.coverSelected C v)
      (D.integralPermit C j.1.1.val.1 j.1.1.val.2) j _ _
      (D.integralGlobalAllocation_species C hC ⟨v, .inr j⟩)
      (D.integralFlagAllocation_species ⟨v, .inr j⟩)).mpr
    cases hs : D.coverSelected C v
    · exact Or.inr (D.integral_edge_permit_of_unselected C hcover j hs)
    · exact Or.inl rfl

theorem hasPacking_of_localStates (C : Finset D.Vertex) (hC : C.card = D.k)
    (hcover : D.graph.IsCover C)
    (S : ∀ v, D.LocalState v (D.coverSelected C v)) :
    HasPacking D.packingInstance D.B := by
  have p := D.packingOfRoleEquivs (D.integralRoleEquiv C hC S)
    (D.integralRoleEquiv_capacity C hC hcover S)
  simpa only [HasPacking, D.card_physicalBins] using (Nonempty.intro p)

theorem ofCompetingTrees_hasPacking (G : GraphInput) {d : ℕ}
    (T : CompetingTrees d) (hd : 0 < d) (R k : ℕ)
    (hk : k ≤ G.n) (hcover : G.CoverAtMost k) :
    HasPacking (ofCompetingTrees G T R k).packingInstance
      (ofCompetingTrees G T R k).B := by
  obtain ⟨C, hcover, hC⟩ := hcover.exists_exact hk
  exact (ofCompetingTrees G T R k).hasPacking_of_localStates C hC hcover
    (fun v => constructedLocalState G T hd R k v _)

end BinPackingGap.InventoryData

end

namespace BinPackingGap

theorem cover_hasPacking_reduction (c : ℕ) (rho : ℝ) (G : GraphInput) (k : ℕ)
    (hk : k ≤ G.n) (hcover : G.CoverAtMost k) :
    HasPacking (reductionInstance c rho G k) (reductionBinBound c rho G k) :=
  InventoryData.ofCompetingTrees_hasPacking G (reductionTrees c rho)
    (depthDemand_pos c rho) _ k hk hcover

end BinPackingGap

end OAI
