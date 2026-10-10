import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Sum
import OAI.Computability.BinPacking.Configurations.CoverageSoundness
import OAI.Computability.BinPacking.Trees.CompetingTrees

namespace OAI

noncomputable section

namespace BinPackingGap.SideChoice

open UniformTree

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
theorem card_le_of_unique_hit [DecidableEq α] [DecidableEq β]
    (tuples : Finset α) (nodes : Finset β)
    (hits : α → β → Prop)
    (hcover : ∀ v ∈ nodes, ∃ t ∈ tuples, hits t v)
    (hunique : ∀ t ∈ tuples, ∀ v w, hits t v → hits t w → v = w) :
    nodes.card ≤ tuples.card := by
  classical
  let f : nodes → tuples := fun v =>
    ⟨Classical.choose (hcover v.val v.property),
      (Classical.choose_spec (hcover v.val v.property)).1⟩
  have hf : ∀ v : nodes, hits (f v).val v.val := fun v =>
    (Classical.choose_spec (hcover v.val v.property)).2
  apply Finset.card_le_card_of_injective (f := f)
  intro v w hvw
  apply Subtype.ext
  have ht : (f v).val = (f w).val := congrArg Subtype.val hvw
  apply hunique (f v).val (f v).property v.val w.val (hf v)
  rw [ht]
  exact hf w

omit [DecidableEq α] [DecidableEq β] in
theorem level_card_le_resources [DecidableEq α] [DecidableEq β]
    (selected : Finset α) (level : α → ℕ)
    (resource : α → β) (stock : Finset β) (ℓ q : ℕ)
    (hmap : ∀ t ∈ selected, level t = ℓ → resource t ∈ stock)
    (hinj : Set.InjOn resource (selected.filter fun t => level t = ℓ))
    (hstock : stock.card ≤ q) :
    (selected.filter fun t => level t = ℓ).card ≤ q := by
  apply (Finset.card_le_card_of_injOn resource ?_ hinj).trans hstock
  intro t ht
  exact hmap t (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp ht).2

variable {d : ℕ} (T : CompetingTrees d)

def taggedDepth : T.plus.Node ⊕ T.minus.Node → ℕ := Sum.elim depth depth

def marksPlus (selected : Finset α)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop) : Finset T.plus.Node := by
  classical
  exact Finset.univ.filter fun v => ∃ t ∈ selected, hits t (.inl v)

def marksMinus (selected : Finset α)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop) : Finset T.minus.Node := by
  classical
  exact Finset.univ.filter fun v => ∃ t ∈ selected, hits t (.inr v)

omit [DecidableEq α] in
@[simp] theorem mem_marksPlus [DecidableEq α] (selected : Finset α)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop) (v : T.plus.Node) :
    v ∈ marksPlus T selected hits ↔ ∃ t ∈ selected, hits t (.inl v) := by
  classical
  simp [marksPlus]

omit [DecidableEq α] in
@[simp] theorem mem_marksMinus [DecidableEq α] (selected : Finset α)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop) (v : T.minus.Node) :
    v ∈ marksMinus T selected hits ↔ ∃ t ∈ selected, hits t (.inr v) := by
  classical
  simp [marksMinus]

theorem roots_not_marked (selected : Finset α) (level : α → ℕ)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop)
    (hpositive : ∀ t ∈ selected, 0 < level t)
    (hdepth : ∀ t ∈ selected, ∀ v, hits t v → taggedDepth T v = level t) :
    T.plus.root ∉ marksPlus T selected hits ∧
      T.minus.root ∉ marksMinus T selected hits := by
  constructor
  · intro hroot
    obtain ⟨t, ht, hhit⟩ := (mem_marksPlus T selected hits _).mp hroot
    have hh : 0 = level t := hdepth t ht (.inl T.plus.root) hhit
    have hp := hpositive t ht
    omega
  · intro hroot
    obtain ⟨t, ht, hhit⟩ := (mem_marksMinus T selected hits _).mp hroot
    have hh : 0 = level t := hdepth t ht (.inr T.minus.root) hhit
    have hp := hpositive t ht
    omega

theorem marked_level_card_le (selected : Finset α) (level : α → ℕ)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop)
    (hdepth : ∀ t ∈ selected, ∀ v, hits t v → taggedDepth T v = level t)
    (hunique : ∀ t ∈ selected, ∀ v w, hits t v → hits t w → v = w)
    (ℓ : ℕ) :
    ((marksPlus T selected hits).filter fun v => depth v = ℓ).card +
      ((marksMinus T selected hits).filter fun v => depth v = ℓ).card ≤
      (selected.filter fun t => level t = ℓ).card := by
  classical
  rw [← Finset.card_disjSum]
  apply card_le_of_unique_hit _ _ hits
  · intro v hv
    cases v with
    | inl v =>
      have hv' := Finset.mem_filter.mp (Finset.inl_mem_disjSum.mp hv)
      obtain ⟨t, ht, hhit⟩ := (mem_marksPlus T selected hits v).mp hv'.1
      refine ⟨t, Finset.mem_filter.mpr ⟨ht, ?_⟩, hhit⟩
      have hh : depth v = level t := hdepth t ht (.inl v) hhit
      exact hh.symm.trans hv'.2
    | inr v =>
      have hv' := Finset.mem_filter.mp (Finset.inr_mem_disjSum.mp hv)
      obtain ⟨t, ht, hhit⟩ := (mem_marksMinus T selected hits v).mp hv'.1
      refine ⟨t, Finset.mem_filter.mpr ⟨ht, ?_⟩, hhit⟩
      have hh : depth v = level t := hdepth t ht (.inr v) hhit
      exact hh.symm.trans hv'.2
  · intro t ht v w hv hw
    exact hunique t (Finset.mem_filter.mp ht).1 v w hv hw

theorem exists_unhit_leaf (selected : Finset α) (level : α → ℕ)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop)
    (hpositive : ∀ t ∈ selected, 0 < level t)
    (hdepth : ∀ t ∈ selected, ∀ v, hits t v → taggedDepth T v = level t)
    (hunique : ∀ t ∈ selected, ∀ v w, hits t v → hits t w → v = w)
    (hstock : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ T.height →
      (selected.filter fun t => level t = ℓ).card ≤ T.quota ℓ) :
    (∃ l : T.plus.Node, leaf l ∧
      ∀ t ∈ selected, ∀ v, hits t (.inl v) → ¬ ancestor v l) ∨
    (∃ l : T.minus.Node, leaf l ∧
      ∀ t ∈ selected, ∀ v, hits t (.inr v) → ¬ ancestor v l) := by
  have hroots := roots_not_marked T selected level hits hpositive hdepth
  have hquota : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ T.height →
      ((marksPlus T selected hits).filter fun v => depth v = ℓ).card +
        ((marksMinus T selected hits).filter fun v => depth v = ℓ).card ≤ T.quota ℓ := by
    intro ℓ hlo hhi
    exact (marked_level_card_le T selected level hits hdepth hunique ℓ).trans
      (hstock ℓ hlo hhi)
  rcases T.shared_obstruction (marksPlus T selected hits) (marksMinus T selected hits)
    hroots.1 hroots.2 hquota with ⟨l, hl, havoid⟩ | ⟨l, hl, havoid⟩
  · left
    refine ⟨l, hl, ?_⟩
    intro t ht v hhit
    exact havoid v ((mem_marksPlus T selected hits v).mpr ⟨t, ht, hhit⟩)
  · right
    refine ⟨l, hl, ?_⟩
    intro t ht v hhit
    exact havoid v ((mem_marksMinus T selected hits v).mpr ⟨t, ht, hhit⟩)

theorem exists_leaf_coverage_le_funded (selected : Finset α) (level : α → ℕ)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop)
    (fundPlus fundMinus : Finset α)
    (coverPlus : T.plus.Node → Finset α) (coverMinus : T.minus.Node → Finset α)
    (hpositive : ∀ t ∈ selected, 0 < level t)
    (hdepth : ∀ t ∈ selected, ∀ v, hits t v → taggedDepth T v = level t)
    (hunique : ∀ t ∈ selected, ∀ v w, hits t v → hits t w → v = w)
    (hstock : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ T.height →
      (selected.filter fun t => level t = ℓ).card ≤ T.quota ℓ)
    (hcoverPlus : ∀ l, leaf l → ∀ t ∈ coverPlus l,
      t ∈ fundPlus ∨ t ∈ selected ∧ ∃ v, hits t (.inl v) ∧ ancestor v l)
    (hcoverMinus : ∀ l, leaf l → ∀ t ∈ coverMinus l,
      t ∈ fundMinus ∨ t ∈ selected ∧ ∃ v, hits t (.inr v) ∧ ancestor v l) :
    (∃ l : T.plus.Node, leaf l ∧ (coverPlus l).card ≤ fundPlus.card) ∨
    (∃ l : T.minus.Node, leaf l ∧ (coverMinus l).card ≤ fundMinus.card) := by
  rcases exists_unhit_leaf T selected level hits hpositive hdepth hunique hstock with
    ⟨l, hl, havoid⟩ | ⟨l, hl, havoid⟩
  · left
    refine ⟨l, hl, Finset.card_le_card ?_⟩
    intro t ht
    rcases hcoverPlus l hl t ht with hfund | ⟨hselected, v, hhit, hancestor⟩
    · exact hfund
    · exact (havoid t hselected v hhit hancestor).elim
  · right
    refine ⟨l, hl, Finset.card_le_card ?_⟩
    intro t ht
    rcases hcoverMinus l hl t ht with hfund | ⟨hselected, v, hhit, hancestor⟩
    · exact hfund
    · exact (havoid t hselected v hhit hancestor).elim

theorem side_choice (selected : Finset α) (level : α → ℕ)
    (hits : α → (T.plus.Node ⊕ T.minus.Node) → Prop)
    (fundPlus fundMinus : Finset α)
    (coverPlus : T.plus.Node → Finset α) (coverMinus : T.minus.Node → Finset α)
    (K : ℕ)
    (hpositive : ∀ t ∈ selected, 0 < level t)
    (hdepth : ∀ t ∈ selected, ∀ v, hits t v → taggedDepth T v = level t)
    (hunique : ∀ t ∈ selected, ∀ v w, hits t v → hits t w → v = w)
    (hstock : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ T.height →
      (selected.filter fun t => level t = ℓ).card ≤ T.quota ℓ)
    (hcoverPlus : ∀ l, leaf l → ∀ t ∈ coverPlus l,
      t ∈ fundPlus ∨ t ∈ selected ∧ ∃ v, hits t (.inl v) ∧ ancestor v l)
    (hcoverMinus : ∀ l, leaf l → ∀ t ∈ coverMinus l,
      t ∈ fundMinus ∨ t ∈ selected ∧ ∃ v, hits t (.inr v) ∧ ancestor v l)
    (hlowerPlus : ∀ l, leaf l → d ≤ (coverPlus l).card + 6 * K)
    (hlowerMinus : ∀ l, leaf l → d ≤ (coverMinus l).card + 6 * K) :
    d ≤ fundPlus.card + 6 * K ∨ d ≤ fundMinus.card + 6 * K := by
  rcases exists_leaf_coverage_le_funded T selected level hits fundPlus fundMinus
    coverPlus coverMinus hpositive hdepth hunique hstock hcoverPlus hcoverMinus with
    ⟨l, hl, hle⟩ | ⟨l, hl, hle⟩
  · exact Or.inl ((hlowerPlus l hl).trans (Nat.add_le_add_right hle _))
  · exact Or.inr ((hlowerMinus l hl).trans (Nat.add_le_add_right hle _))

end BinPackingGap.SideChoice

namespace BinPackingGap

section

def reductionTrees (c : ℕ) (ρ : ℝ) : CompetingTrees (depthDemand c ρ) :=
  competingTrees (depthDemand c ρ) (depthDemand_pos c ρ)

def reductionInventory (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) : InventoryData :=
  InventoryData.ofCompetingTrees G (reductionTrees c ρ)
    (repetitions (reductionTrees c ρ).quotaTotal G.n (lossAllowance c)) k

def reductionInstance (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) : Instance :=
  (reductionInventory c ρ G k).packingInstance

def reductionBinBound (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) : ℕ :=
  (reductionInventory c ρ G k).B

@[simp] theorem reductionInventory_graph (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    (reductionInventory c ρ G k).graph = G := rfl

@[simp] theorem reductionInventory_d (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    (reductionInventory c ρ G k).d = depthDemand c ρ := rfl

@[simp] theorem reductionInventory_k (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    (reductionInventory c ρ G k).k = k := rfl

@[simp] theorem reductionInventory_P (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    (reductionInventory c ρ G k).P = (reductionTrees c ρ).quotaTotal := rfl

theorem reductionInventory_R (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    (reductionInventory c ρ G k).R =
      repetitions (reductionInventory c ρ G k).P G.n (lossAllowance c) := rfl

theorem reductionInventory_R_pos (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    0 < (reductionInventory c ρ G k).R := repetitions_pos _ _ _

theorem reductionInventory_height_pos (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    0 < (reductionInventory c ρ G k).L := (reductionTrees c ρ).height_pos

theorem reductionInventory_plus_height (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    (reductionInventory c ρ G k).plus.height = (reductionInventory c ρ G k).L :=
  (reductionTrees c ρ).plus_height

theorem reductionInventory_minus_height (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) :
    (reductionInventory c ρ G k).minus.height = (reductionInventory c ρ G k).L :=
  (reductionTrees c ρ).minus_height

theorem reductionInstance_count (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ)
    (hk : k ≤ G.n) :
    (reductionInstance c ρ G k).n = 5 * reductionBinBound c ρ G k :=
  (reductionInventory c ρ G k).packingInstance_n hk

theorem reductionInstance_size_bounds (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ)
    (i : (reductionInstance c ρ G k).Item) :
    (1 / 6 : ℚ) < (reductionInstance c ρ G k).size i ∧
      (reductionInstance c ρ G k).size i < 1 :=
  (reductionInventory c ρ G k).packingInstance_size_mem_interval i

namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

private theorem selected_inventory_subclass (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (r : Role) :
    D.itemSubclass ⟨r, roleCopy p e t r⟩ =
      patternSubclass (p.tablePattern (subclass e) t) r := by
  have h := p.itemAtRole_subclass (subclass e) t r
  rw [← roleCopy_item p e t r] at h
  simpa only [subclass, Function.comp_apply, Equiv.symm_apply_apply] using h

private theorem selected_row_subclass (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) :
    D.rowSubclass (rowCopy p e t).2 =
      patternSubclass (p.tablePattern (subclass e) t) .x := by
  have h := selected_inventory_subclass p e t .x
  change D.itemSubclass ⟨.x, rowCopy p e t⟩ = _ at h
  rcases hc : rowCopy p e t with ⟨v, r⟩
  simpa only [hc, InventoryData.itemSubclass] using h

private theorem unit_global_species (u : D.GlobalCopy) (hu : D.globalUnit u = true) :
    u.1 = .up true ∨ u.1 = .um true := by
  rcases u with ⟨s, i⟩
  cases s with
  | up one => cases one <;> simp_all [InventoryData.globalUnit]
  | um one => cases one <;> simp_all [InventoryData.globalUnit]
  | edge edge permit => simp [InventoryData.globalUnit] at hu

private theorem selected_row_tm_of_um (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) {one : Bool}
    (hs : (globalCopy p e t).1 = .um one) :
    D.rowSubclass (rowCopy p e t).2 = .tm := by
  have hg := selected_inventory_subclass p e t .«global»
  have hclass : D.itemSubclass ⟨.«global», globalCopy p e t⟩ = .um := by
    rcases hc : globalCopy p e t with ⟨s, i⟩
    have hs' : s = .um one := by simpa only [hc] using hs
    subst s
    rfl
  rw [hclass] at hg
  have hx := selected_row_subclass p e t
  cases hp : p.tablePattern (subclass e) t <;> simp_all [patternSubclass]

private theorem selected_row_not_tm_of_up (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) {one : Bool}
    (hs : (globalCopy p e t).1 = .up one) :
    D.rowSubclass (rowCopy p e t).2 ≠ .tm := by
  have hg := selected_inventory_subclass p e t .«global»
  have hclass : D.itemSubclass ⟨.«global», globalCopy p e t⟩ = .up := by
    rcases hc : globalCopy p e t with ⟨s, i⟩
    have hs' : s = .up one := by simpa only [hc] using hs
    subst s
    rfl
  rw [hclass] at hg
  have hx := selected_row_subclass p e t
  cases hp : p.tablePattern (subclass e) t <;> simp_all [patternSubclass]

private theorem selected_global_resource (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) :
    p.itemAtRole (subclass e) t .«global» ∈
      globalResources e (globalCopy p e t).1 := by
  apply (mem_globalResources e _ _).mpr
  refine ⟨(globalCopy p e t).2, ?_⟩
  exact roleCopy_item p e t .«global»

private theorem funded_of_species (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v)
    {s : GlobalSpecies D.graph} (hs : (globalCopy p e t).1 = s) :
    t ∈ fundedTuples p e s v := by
  apply (mem_fundedTuples p e s v t).mpr
  refine ⟨ht, ?_⟩
  have hr := selected_global_resource p e t
  rwa [hs] at hr

theorem covering_plus_unit_funded (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v)
    (leaf : D.PlusLeaf) {a : ℚ}
    (ha : a ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .plus leaf.val)
    (hu : D.globalUnit (globalCopy p e t) = true)
    (hc : tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t) :
    t ∈ fundedTuples p e (.up true) v := by
  rcases unit_global_species (globalCopy p e t) hu with hup | hum
  · exact funded_of_species p e v t ht hup
  · have hrow := selected_row_tm_of_um p e t hum
    have hfinish : 1 < tupleFinish p e t :=
      D.minus_row_completion_gt_one (rowCopy p e t).2 (globalCopy p e t)
        (localCopy p e t).2 hrow
    have hroot := TreeGeometry.nodeCell_subset_root D.graph.edges.length D.R
      D.geometryBound .plus D.plus_branch_le_geometryBound leaf.val ha
    have ha1 : a ≤ 1 := by
      simpa only [TreeGeometry.rootOffset, zero_add] using hroot.2
    exact False.elim (by linarith only [hfinish, ha1, hc.1])

theorem covering_minus_unit_funded (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v)
    (leaf : D.MinusLeaf) {a : ℚ}
    (ha : a ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .minus leaf.val)
    (hu : D.globalUnit (globalCopy p e t) = true)
    (hc : tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t) :
    t ∈ fundedTuples p e (.um true) v := by
  rcases unit_global_species (globalCopy p e t) hu with hup | hum
  · have hrow := selected_row_not_tm_of_up p e t hup
    have hbase : tupleBaseline p e t ≤ 1 :=
      D.rowBaseline_le_one_of_not_tm (rowCopy p e t).2 hrow
    have hroot := TreeGeometry.nodeCell_subset_root D.graph.edges.length D.R
      D.geometryBound .minus D.minus_branch_le_geometryBound leaf.val ha
    have ha4 : 4 ≤ a := hroot.1
    exact False.elim (by linarith only [hbase, ha4, hc.2])
  · exact funded_of_species p e v t ht hum

theorem zero_lengths_cover_jobCell (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) {a : ℚ}
    (hu : D.globalUnit (globalCopy p e t) = false)
    (hl : tupleLocalLength p e t = 0)
    (hc : tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t) :
    ∃ j : D.JobCopy (rowCopy p e t).1,
      a ∈ D.testCell (.inr (.inr j.1) : D.TestAt (rowCopy p e t).1) := by
  have hg := tupleGlobalLength_eq_of_unit_false p e t hu
  have hmem : a ∈ completionInterval (tupleBaseline p e t) (tupleShort p e t) 0 0
      (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) := by
    change completion (tupleBaseline p e t) (tupleShort p e t) 0 0 _ ≤ a ∧
      a < tupleBaseline p e t
    simpa only [tupleFinish, hg, hl] using hc
  change a ∈ completionInterval (D.rowBaseline (rowCopy p e t).2)
    (D.rowShort (rowCopy p e t).2) 0 0
    (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) at hmem
  by_cases hs : D.rowShort (rowCopy p e t).2 = true
  · obtain ⟨j, _, _, hj⟩ := D.row_zero_resources_job (rowCopy p e t).2 hs
    rw [hj] at hmem
    refine ⟨j, ?_⟩
    change a ∈ Geometry.closedJobCell D.graph.edges.length D.R D.geometryBound D.L
      (D.jobPosition j)
    exact ⟨hmem.1, hmem.2.le⟩
  · have hsfalse : D.rowShort (rowCopy p e t).2 = false := by
      cases hh : D.rowShort (rowCopy p e t).2 <;> simp_all
    rw [D.row_zero_resources_empty (rowCopy p e t).2 hsfalse] at hmem
    cases hmem

theorem zero_lengths_not_cover_plus_leaf (p : Packing I b) (e : D.Item ≃ I.Item)
    (hplusheight : D.plus.height = D.L) (hminusheight : D.minus.height = D.L)
    (hL : 1 ≤ D.L) (t : p.TableBin (subclass e)) (leaf : D.PlusLeaf) {a : ℚ}
    (ha : a ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .plus leaf.val)
    (hu : D.globalUnit (globalCopy p e t) = false)
    (hl : tupleLocalLength p e t = 0) :
    ¬ (tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t) := by
  intro hc
  obtain ⟨j, hj⟩ := zero_lengths_cover_jobCell p e t hu hl hc
  have hleaf : a ∈ D.testCell (.inl leaf : D.TestAt (rowCopy p e t).1) := ha
  have hdis := D.testCell_disjoint hplusheight hminusheight hL
    (show (.inl leaf : D.TestAt (rowCopy p e t).1) ≠ .inr (.inr j.1) by
      intro h; cases h)
  exact Set.disjoint_left.mp hdis hleaf hj

theorem zero_lengths_not_cover_minus_leaf (p : Packing I b) (e : D.Item ≃ I.Item)
    (hplusheight : D.plus.height = D.L) (hminusheight : D.minus.height = D.L)
    (hL : 1 ≤ D.L) (t : p.TableBin (subclass e)) (leaf : D.MinusLeaf) {a : ℚ}
    (ha : a ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .minus leaf.val)
    (hu : D.globalUnit (globalCopy p e t) = false)
    (hl : tupleLocalLength p e t = 0) :
    ¬ (tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t) := by
  intro hc
  obtain ⟨j, hj⟩ := zero_lengths_cover_jobCell p e t hu hl hc
  have hleaf : a ∈ D.testCell (.inr (.inl leaf) : D.TestAt (rowCopy p e t).1) := ha
  have hdis := D.testCell_disjoint hplusheight hminusheight hL
    (show (.inr (.inl leaf) : D.TestAt (rowCopy p e t).1) ≠ .inr (.inr j.1) by
      intro h; cases h)
  exact Set.disjoint_left.mp hdis hleaf hj

end PackingCounts

open UniformTree

namespace InventoryData

variable (D : InventoryData)

def plusPoint (v : D.plus.Node) : ℚ :=
  (TreeGeometry.left D.graph.edges.length D.R D.geometryBound .plus v.val +
    TreeGeometry.right D.graph.edges.length D.R D.geometryBound .plus v.val) / 2

def minusPoint (v : D.minus.Node) : ℚ :=
  (TreeGeometry.left D.graph.edges.length D.R D.geometryBound .minus v.val +
    TreeGeometry.right D.graph.edges.length D.R D.geometryBound .minus v.val) / 2

theorem plusPoint_mem_Ico (v : D.plus.Node) :
    D.plusPoint v ∈ Set.Ico
      (TreeGeometry.left D.graph.edges.length D.R D.geometryBound .plus v.val)
      (TreeGeometry.right D.graph.edges.length D.R D.geometryBound .plus v.val) := by
  have h := TreeGeometry.left_lt_right D.graph.edges.length D.R D.geometryBound .plus v.val
  dsimp only [plusPoint, Set.mem_Ico]
  constructor <;> linarith

theorem minusPoint_mem_Ico (v : D.minus.Node) :
    D.minusPoint v ∈ Set.Ico
      (TreeGeometry.left D.graph.edges.length D.R D.geometryBound .minus v.val)
      (TreeGeometry.right D.graph.edges.length D.R D.geometryBound .minus v.val) := by
  have h := TreeGeometry.left_lt_right D.graph.edges.length D.R D.geometryBound .minus v.val
  dsimp only [minusPoint, Set.mem_Ico]
  constructor <;> linarith

theorem plusPoint_mem_cell (v : D.plus.Node) :
    D.plusPoint v ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .plus v :=
  ⟨(D.plusPoint_mem_Ico v).1, (D.plusPoint_mem_Ico v).2.le⟩

theorem minusPoint_mem_cell (v : D.minus.Node) :
    D.minusPoint v ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .minus v :=
  ⟨(D.minusPoint_mem_Ico v).1, (D.minusPoint_mem_Ico v).2.le⟩

def taggedAddress : D.plus.Node ⊕ D.minus.Node → TreeGeometry.Side × List ℕ
  | .inl v => (.plus, v.val)
  | .inr v => (.minus, v.val)

theorem taggedAddress_injective : Function.Injective D.taggedAddress := by
  intro u v h
  cases u with
  | inl u =>
    cases v with
    | inl v => exact congrArg Sum.inl (Subtype.ext (congrArg Prod.snd h))
    | inr v => have hs := congrArg Prod.fst h; cases hs
  | inr u =>
    cases v with
    | inl v => have hs := congrArg Prod.fst h; cases hs
    | inr v => exact congrArg Sum.inr (Subtype.ext (congrArg Prod.snd h))

def taggedNodeDepth (v : D.plus.Node ⊕ D.minus.Node) : ℕ :=
  (D.taggedAddress v).2.length

def taggedNodeCell (v : D.plus.Node ⊕ D.minus.Node) : Set ℚ :=
  TreeGeometry.cell D.graph.edges.length D.R D.geometryBound
    (D.taggedAddress v).1 (D.taggedAddress v).2

theorem taggedAddress_bounded (v : D.plus.Node ⊕ D.minus.Node) :
    TreeGeometry.BoundedAddress D.geometryBound (D.taggedAddress v).2 := by
  cases v with
  | inl v => exact TreeGeometry.boundedAddress_node v D.plus_branch_le_geometryBound
  | inr v => exact TreeGeometry.boundedAddress_node v D.minus_branch_le_geometryBound

end InventoryData

namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

def tupleHits (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (v : D.plus.Node ⊕ D.minus.Node) : Prop :=
  D.taggedNodeDepth v = tupleLocalDepth p e t ∧
    (tupleClosedInterval p e t ∩ D.taggedNodeCell v).Nonempty

theorem selected_hits_unique (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ zeroPositiveTuples p e v)
    (u w : D.plus.Node ⊕ D.minus.Node)
    (hu : tupleHits p e t u) (hw : tupleHits p e t w) : u = w := by
  apply D.taggedAddress_injective
  exact TreeGeometry.eq_of_short_intersections D.graph.edges.length D.R D.geometryBound
    (Finset.mem_Icc.mp (selected_depth_mem p e v t ht)).2
    hu.1 hw.1 (D.taggedAddress_bounded u) (D.taggedAddress_bounded w)
    (selected_interval_length p e v t ht) hu.2 hw.2

theorem main_local_nonzero_positive (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v)
    (hlocal : tupleLocalLength p e t ≠ 0) :
    p.itemAtRole (subclass e) t .«local» ∈ positiveLocalResources e v := by
  have hlabel := good_local_vertex p e v t
    (Coverage.mainTuplesAt_subset_good p (subclass e) (label e) v ht)
  cases hcopy : localCopy p e t with
  | mk w l =>
    have hwv : w = v := by simpa only [hcopy] using hlabel
    subst w
    rcases l with ((i | z) | j)
    · apply (mem_positiveLocalResources e v _).mpr
      refine ⟨i, ?_⟩
      rw [← roleCopy_item p e t .«local»]
      exact congrArg (fun x : (Σ w : D.Vertex, D.LocalAt w) => e ⟨.«local», x⟩)
        hcopy.symm
    · exact (hlocal (congrArg
        (fun x : (Σ w : D.Vertex, D.LocalAt w) => D.localLength x.2) hcopy)).elim
    · exact (hlocal (congrArg
        (fun x : (Σ w : D.Vertex, D.LocalAt w) => D.localLength x.2) hcopy)).elim

theorem selected_hits_plus_ancestor (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ zeroPositiveTuples p e v) (hheight : D.plus.height = D.L)
    (l : D.plus.Node) (hl : leaf l) {a : ℚ}
    (ha : a ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .plus l)
    (hcover : tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t) :
    ∃ u : D.plus.Node, tupleHits p e t (.inl u) ∧ ancestor u l := by
  let ell := tupleLocalDepth p e t
  have hell : ell ≤ depth l := by
    rw [(leaf_iff_depth_eq_height l).mp hl, hheight]
    exact (Finset.mem_Icc.mp (selected_depth_mem p e v t ht)).2
  refine ⟨ancestorAt l ell, ⟨depth_ancestorAt l hell, ?_⟩, ancestorAt_ancestor l ell⟩
  refine ⟨a, ⟨hcover.1, hcover.2.le⟩, ?_⟩
  exact TreeGeometry.mem_ancestor_cell D.graph.edges.length D.R D.geometryBound .plus
    D.plus_branch_le_geometryBound l ell ha

theorem selected_hits_minus_ancestor (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ zeroPositiveTuples p e v) (hheight : D.minus.height = D.L)
    (l : D.minus.Node) (hl : leaf l) {a : ℚ}
    (ha : a ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .minus l)
    (hcover : tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t) :
    ∃ u : D.minus.Node, tupleHits p e t (.inr u) ∧ ancestor u l := by
  let ell := tupleLocalDepth p e t
  have hell : ell ≤ depth l := by
    rw [(leaf_iff_depth_eq_height l).mp hl, hheight]
    exact (Finset.mem_Icc.mp (selected_depth_mem p e v t ht)).2
  refine ⟨ancestorAt l ell, ⟨depth_ancestorAt l hell, ?_⟩, ancestorAt_ancestor l ell⟩
  refine ⟨a, ⟨hcover.1, hcover.2.le⟩, ?_⟩
  exact TreeGeometry.mem_ancestor_cell D.graph.edges.length D.R D.geometryBound .minus
    D.minus_branch_le_geometryBound l ell ha

theorem covering_plus_classification (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (hplusheight : D.plus.height = D.L) (hminusheight : D.minus.height = D.L)
    (hL : 1 ≤ D.L) (l : D.plus.Node) (hl : leaf l) {a : ℚ}
    (ha : a ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .plus l)
    (ht : t ∈ tupleCovering p e v a) :
    t ∈ fundedTuples p e (.up true) v ∨
      t ∈ zeroPositiveTuples p e v ∧
        ∃ u : D.plus.Node, tupleHits p e t (.inl u) ∧ ancestor u l := by
  obtain ⟨hmain, hcover⟩ := (mem_tupleCovering p e v a t).mp ht
  cases hu : D.globalUnit (globalCopy p e t) with
  | false =>
    have hlocal : tupleLocalLength p e t ≠ 0 := by
      intro hz
      exact zero_lengths_not_cover_plus_leaf p e hplusheight hminusheight hL t
        ⟨l, hl⟩ ha hu hz hcover
    have hselected : t ∈ zeroPositiveTuples p e v :=
      (mem_zeroPositiveTuples p e v t).mpr
        ⟨hmain, hu, main_local_nonzero_positive p e v t hmain hlocal⟩
    exact Or.inr ⟨hselected,
      selected_hits_plus_ancestor p e v t hselected hplusheight l hl ha hcover⟩
  | true =>
    exact Or.inl (covering_plus_unit_funded p e v t hmain ⟨l, hl⟩ ha hu hcover)

theorem covering_minus_classification (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (hplusheight : D.plus.height = D.L) (hminusheight : D.minus.height = D.L)
    (hL : 1 ≤ D.L) (l : D.minus.Node) (hl : leaf l) {a : ℚ}
    (ha : a ∈ TreeGeometry.nodeCell D.graph.edges.length D.R D.geometryBound .minus l)
    (ht : t ∈ tupleCovering p e v a) :
    t ∈ fundedTuples p e (.um true) v ∨
      t ∈ zeroPositiveTuples p e v ∧
        ∃ u : D.minus.Node, tupleHits p e t (.inr u) ∧ ancestor u l := by
  obtain ⟨hmain, hcover⟩ := (mem_tupleCovering p e v a t).mp ht
  cases hu : D.globalUnit (globalCopy p e t) with
  | false =>
    have hlocal : tupleLocalLength p e t ≠ 0 := by
      intro hz
      exact zero_lengths_not_cover_minus_leaf p e hplusheight hminusheight hL t
        ⟨l, hl⟩ ha hu hz hcover
    have hselected : t ∈ zeroPositiveTuples p e v :=
      (mem_zeroPositiveTuples p e v t).mpr
        ⟨hmain, hu, main_local_nonzero_positive p e v t hmain hlocal⟩
    exact Or.inr ⟨hselected,
      selected_hits_minus_ancestor p e v t hselected hminusheight l hl ha hcover⟩
  | true =>
    exact Or.inl (covering_minus_unit_funded p e v t hmain ⟨l, hl⟩ ha hu hcover)

theorem side_choice_of_competingTrees (G : GraphInput) {d : ℕ}
    (T : CompetingTrees d) (R k : ℕ) (p : Packing I b)
    (e : (InventoryData.ofCompetingTrees G T R k).Item ≃ I.Item)
    (v : G.Vertex) (K : ℕ)
    (hlowerPlus : ∀ l : T.plus.Node, leaf l →
      d ≤ (tupleCovering p e v ((InventoryData.ofCompetingTrees G T R k).plusPoint l)).card +
        6 * K)
    (hlowerMinus : ∀ l : T.minus.Node, leaf l →
      d ≤ (tupleCovering p e v ((InventoryData.ofCompetingTrees G T R k).minusPoint l)).card +
        6 * K) :
    d ≤ xplus p e v + 6 * K ∨ d ≤ xminus p e v + 6 * K := by
  classical
  let D := InventoryData.ofCompetingTrees G T R k
  change d ≤ (fundedTuples p e (.up true) v).card + 6 * K ∨
    d ≤ (fundedTuples p e (.um true) v).card + 6 * K
  apply SideChoice.side_choice T (zeroPositiveTuples p e v) (tupleLocalDepth p e)
    (tupleHits p e) (fundedTuples p e (.up true) v) (fundedTuples p e (.um true) v)
    (fun l => tupleCovering p e v (D.plusPoint l))
    (fun l => tupleCovering p e v (D.minusPoint l)) K
  · intro t ht
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one
      (Finset.mem_Icc.mp (selected_depth_mem p e v t ht)).1
  · intro t _ w hhit
    cases w <;> exact hhit.1
  · intro t ht u w hu hw
    exact selected_hits_unique p e v t ht u w hu hw
  · intro ell hlo hhi
    exact zeroPositiveTuples_depth_card_le p e v
      ⟨ell, Finset.mem_Icc.mpr ⟨hlo, hhi⟩⟩
  · intro l hl t ht
    exact covering_plus_classification p e v t T.plus_height T.minus_height
      (Nat.succ_le_of_lt T.height_pos) l hl (D.plusPoint_mem_cell l) ht
  · intro l hl t ht
    exact covering_minus_classification p e v t T.plus_height T.minus_height
      (Nat.succ_le_of_lt T.height_pos) l hl (D.minusPoint_mem_cell l) ht
  · exact hlowerPlus
  · exact hlowerMinus

theorem side_choice_of_test_coverage (G : GraphInput) {d : ℕ}
    (T : CompetingTrees d) (R k : ℕ) (p : Packing I b)
    (e : (InventoryData.ofCompetingTrees G T R k).Item ≃ I.Item)
    (v : G.Vertex) (K : ℕ)
    (hcoverage : ∀ q : (InventoryData.ofCompetingTrees G T R k).TestAt v, ∀ a : ℚ,
      a ∈ (InventoryData.ofCompetingTrees G T R k).testInterval q →
        d ≤ (tupleCovering p e v a).card + 6 * K) :
    d ≤ xplus p e v + 6 * K ∨ d ≤ xminus p e v + 6 * K := by
  apply side_choice_of_competingTrees G T R k p e v K
  · intro l hl
    exact hcoverage (.inl ⟨l, hl⟩) _
      ((InventoryData.ofCompetingTrees G T R k).plusPoint_mem_Ico l)
  · intro l hl
    exact hcoverage (.inr (.inl ⟨l, hl⟩)) _
      ((InventoryData.ofCompetingTrees G T R k).minusPoint_mem_Ico l)

end PackingCounts

end

def extractedCover (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ) {b : ℕ}
    (p : Packing (reductionInstance c ρ G k) b) : Finset G.Vertex :=
  thresholdCover (depthDemand c ρ)
    (PackingCounts.xplus p (reductionInventory c ρ G k).itemEquiv)

theorem reduction_side_choice (c : ℕ) (ρ : ℝ) (G : GraphInput) (k : ℕ)
    (hk : k ≤ G.n) {b : ℕ} (p : Packing (reductionInstance c ρ G k) b)
    (hb : b ≤ reductionBinBound c ρ G k + c) (v : G.Vertex) :
    depthDemand c ρ ≤ PackingCounts.xplus p (reductionInventory c ρ G k).itemEquiv v +
      6 * lossAllowance c ∨
    depthDemand c ρ ≤ PackingCounts.xminus p (reductionInventory c ρ G k).itemEquiv v +
      6 * lossAllowance c := by
  let D := reductionInventory c ρ G k
  apply PackingCounts.side_choice_of_test_coverage G (reductionTrees c ρ)
    D.R k p D.itemEquiv v (lossAllowance c)
  intro q a ha
  exact D.test_coverage (reductionInventory_plus_height c ρ G k)
    (reductionInventory_minus_height c ρ G k)
    (Nat.succ_le_of_lt (reductionInventory_height_pos c ρ G k)) hk p hb v q a ha

theorem extractedCover_card_le (c : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (G : GraphInput) (k : ℕ) (hk : k ≤ G.n) {b : ℕ}
    (p : Packing (reductionInstance c ρ G k) b)
    (hb : b ≤ reductionBinBound c ρ G k + c) :
    ((extractedCover c ρ G k p).card : ℝ) ≤ (k : ℝ) + ρ * G.n := by
  let D := reductionInventory c ρ G k
  apply thresholdCover_card_le_graph G
    (PackingCounts.xplus p D.itemEquiv) (PackingCounts.xminus p D.itemEquiv)
    (depthDemand_pos c ρ) (depthDemand_ge_72 c ρ) hk hρ (depthDemand_ge_120_div c ρ)
  · exact PackingCounts.xplus_budget p D.itemEquiv
  · exact PackingCounts.total_budget p D.itemEquiv hk
  · exact reduction_side_choice c ρ G k hk p hb

end BinPackingGap

end

end OAI
