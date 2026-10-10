import OAI.Computability.BinPacking.Inventory.InventoryPrefixConservation

namespace OAI

namespace BinPackingGap

open scoped BigOperators

theorem encoded_pattern_role_sum {n : ℕ} (p : Pattern) (v : Fin n) (w : Role → ℚ) :
    (∑ r, encodedSize (patternSubclass p r) (tableRoleLabel v v v r) (w r)) =
      1 + nu n * ∑ r, w r := by
  have hp : (∑ r, primaryScore (patternSubclass p r)) = 0 :=
    sum_primaryScore_eq_zero_of_coefficients _ (pattern_primaryCoeff_sum p)
  have hq : (∑ r, secondaryScore (patternSubclass p r) (tableRoleLabel v v v r)) = 0 := by
    rw [Role.sum_univ]
    cases p <;>
      simp [secondaryScore, patternSubclass, Subclass.role, tableRoleLabel] <;> ring
  have hpQ : (∑ r, (primaryScore (patternSubclass p r) : ℚ)) = 0 := by
    exact_mod_cast hp
  have hqQ : (∑ r, (secondaryScore (patternSubclass p r)
      (tableRoleLabel v v v r) : ℚ)) = 0 := by
    exact_mod_cast hq
  calc
    _ = (∑ _r : Role, (1 / 5 : ℚ)) +
        gamma * (∑ r, (primaryScore (patternSubclass p r) : ℚ)) +
        mu n * (∑ r, (secondaryScore (patternSubclass p r)
          (tableRoleLabel v v v r) : ℚ)) + nu n * ∑ r, w r := by
      simp only [encodedSize, Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [hpQ, hqQ]; norm_num

namespace InventoryData

variable (D : InventoryData)

def localTemplateItems {v : D.Vertex} (row : D.RowAt v) (anchor : D.AnchorAt v)
    (u : D.GlobalCopy) (l : D.LocalAt v) (flag : D.FlagCopy) : Role → D.Item
  | .x => ⟨.x, ⟨v, row⟩⟩
  | .anchor => ⟨.anchor, ⟨v, anchor⟩⟩
  | .«global» => ⟨.«global», u⟩
  | .«local» => ⟨.«local», ⟨v, l⟩⟩
  | .flag => ⟨.flag, flag⟩

@[simp] theorem localTemplateItems_role {v : D.Vertex}
    (row : D.RowAt v) (anchor : D.AnchorAt v) (u : D.GlobalCopy)
    (l : D.LocalAt v) (flag : D.FlagCopy) (r : Role) :
    D.itemRole (D.localTemplateItems row anchor u l flag r) = r := by
  cases r <;> rfl

theorem localTemplateItems_injective {v : D.Vertex}
    (row : D.RowAt v) (anchor : D.AnchorAt v) (u : D.GlobalCopy)
    (l : D.LocalAt v) (flag : D.FlagCopy) :
    Function.Injective (D.localTemplateItems row anchor u l flag) := by
  intro r s h
  simpa only [localTemplateItems_role] using congrArg D.itemRole h

@[simp] theorem localTemplateItems_label {v : D.Vertex}
    (row : D.RowAt v) (anchor : D.AnchorAt v) (u : D.GlobalCopy)
    (l : D.LocalAt v) (flag : D.FlagCopy) (r : Role) :
    D.itemLabel (D.localTemplateItems row anchor u l flag r) =
      tableRoleLabel v v v r := by
  cases r <;> rfl

theorem localTemplate_coordinate_sum {v : D.Vertex}
    (row : D.RowAt v) (anchor : D.AnchorAt v) (u : D.GlobalCopy)
    (l : D.LocalAt v) (flag : D.FlagCopy) :
    (∑ r, D.itemCoordinate (D.localTemplateItems row anchor u l flag r)) =
      D.rowCoordinate row + D.anchorCoordinate anchor + D.globalCoordinate u -
        D.localLength l := by
  rw [Role.sum_univ]
  simp only [localTemplateItems, itemCoordinate, localCoordinate, add_zero]
  ring

theorem localTemplate_size_sum {v : D.Vertex}
    (row : D.RowAt v) (anchor : D.AnchorAt v) (u : D.GlobalCopy)
    (l : D.LocalAt v) (flag : D.FlagCopy) (p : Pattern)
    (hpattern : ∀ r, D.itemSubclass (D.localTemplateItems row anchor u l flag r) =
      patternSubclass p r) :
    (∑ r, D.itemSize (D.localTemplateItems row anchor u l flag r)) =
      1 + nu D.graph.n * ∑ r,
        D.itemCoordinate (D.localTemplateItems row anchor u l flag r) := by
  simp only [itemSize, hpattern, localTemplateItems_label]
  exact encoded_pattern_role_sum p v _

def stateMainPattern {v : D.Vertex} : D.MBase v → Pattern
  | .inl (.inl _) => .plusTree
  | .inl (.inr (.inl _)) => .minusTree
  | .inl (.inr (.inr _)) => .plusTree
  | .inr _ => .mainJob

theorem stateMainTemplate_pattern {v : D.Vertex} (selected : Bool)
    (b z : D.MBase v) (l : D.DMAt v) (u : D.GlobalCopy) (f : D.FlagCopy)
    (hu : u.1 = D.stateMainGlobalSpecies selected b)
    (hf : f.1 = D.stateFlagSpecies (.inl b)) (r : Role) :
    D.itemSubclass (D.localTemplateItems (D.stateMainRow v selected b)
      (.inl z) u (.inl l) f r) = patternSubclass (D.stateMainPattern b) r := by
  rcases u with ⟨us, ui⟩
  rcases f with ⟨fs, fi⟩
  change us = D.stateMainGlobalSpecies selected b at hu
  change fs = D.stateFlagSpecies (.inl b) at hf
  subst us
  subst fs
  rcases b with (⟨node, copy⟩ | (⟨node, copy⟩ | padding)) | job
  all_goals cases r <;> rfl

theorem stateMainGlobal_coordinate {v : D.Vertex} (selected : Bool)
    (b : D.MBase v) (u : D.GlobalCopy)
    (hu : u.1 = D.stateMainGlobalSpecies selected b) :
    D.globalCoordinate u = -D.stateMainLength selected b := by
  rcases u with ⟨us, ui⟩
  change us = D.stateMainGlobalSpecies selected b at hu
  subst us
  rcases b with (⟨node, copy⟩ | (⟨node, copy⟩ | padding)) | job <;> rfl

theorem stateMainTemplate_size_eq {v : D.Vertex} (selected : Bool)
    (b z : D.MBase v) (l : D.DMAt v) (u : D.GlobalCopy) (f : D.FlagCopy)
    (hu : u.1 = D.stateMainGlobalSpecies selected b)
    (hf : f.1 = D.stateFlagSpecies (.inl b)) :
    (∑ r, D.itemSize (D.localTemplateItems (D.stateMainRow v selected b)
      (.inl z) u (.inl l) f r)) =
      1 + nu D.graph.n * (D.rowCoordinate (D.stateMainRow v selected b) -
        D.stateMainLength selected b - D.localLength (.inl l) - D.deadline z) := by
  rw [D.localTemplate_size_sum _ _ _ _ _ (D.stateMainPattern b)
    (D.stateMainTemplate_pattern selected b z l u f hu hf)]
  rw [D.localTemplate_coordinate_sum, D.stateMainGlobal_coordinate selected b u hu]
  simp only [anchorCoordinate]
  ring

theorem stateMainTemplate_feasible_iff {v : D.Vertex} (selected : Bool)
    (b z : D.MBase v) (l : D.DMAt v) (u : D.GlobalCopy) (f : D.FlagCopy)
    (hu : u.1 = D.stateMainGlobalSpecies selected b)
    (hf : f.1 = D.stateFlagSpecies (.inl b)) :
    ((∑ r, D.itemSize (D.localTemplateItems (D.stateMainRow v selected b)
      (.inl z) u (.inl l) f r)) ≤ 1) ↔
      D.rowCoordinate (D.stateMainRow v selected b) - D.stateMainLength selected b -
        D.localLength (.inl l) ≤ D.deadline z := by
  rw [D.stateMainTemplate_size_eq selected b z l u f hu hf]
  have hnu := nu_pos D.graph.n
  constructor
  · intro h
    have hmul : nu D.graph.n *
        (D.rowCoordinate (D.stateMainRow v selected b) - D.stateMainLength selected b -
          D.localLength (.inl l) - D.deadline z) ≤ nu D.graph.n * 0 := by linarith
    exact sub_nonpos.mp (le_of_mul_le_mul_left hmul hnu)
  · intro h
    have hmul := mul_nonpos_of_nonneg_of_nonpos hnu.le (sub_nonpos.mpr h)
    linarith

theorem edgeTemplate_size_eq {v : D.Vertex} (short permit : Bool)
    (j : D.JobCopy v) (u : D.GlobalCopy) (f : D.FlagCopy)
    (hu : u.1 = .edge (D.jobPosition j).1 permit) (hf : f.1 = .edge) :
    (∑ r, D.itemSize (D.localTemplateItems (.inr (short, j))
      (.inr j) u (.inr j) f r)) =
      1 + nu D.graph.n *
        ((if permit then 0 else Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) -
          (if short then Geometry.delta D.graph.edges.length D.R D.geometryBound D.L else 0)) := by
  rcases u with ⟨us, ui⟩
  rcases f with ⟨fs, fi⟩
  change us = .edge (D.jobPosition j).1 permit at hu
  change fs = .edge at hf
  subst us
  subst fs
  rw [D.localTemplate_size_sum _ _ _ _ _ .edgeJob (by intro r; cases r <;> rfl)]
  rw [D.localTemplate_coordinate_sum]
  simp only [rowCoordinate, rowBaseline, rowShort, anchorCoordinate,
    globalCoordinate, localLength]
  cases short <;> cases permit <;> simp <;> ring_nf <;> simp

theorem edgeTemplate_feasible_iff {v : D.Vertex} (short permit : Bool)
    (j : D.JobCopy v) (u : D.GlobalCopy) (f : D.FlagCopy)
    (hu : u.1 = .edge (D.jobPosition j).1 permit) (hf : f.1 = .edge) :
    ((∑ r, D.itemSize (D.localTemplateItems (.inr (short, j))
      (.inr j) u (.inr j) f r)) ≤ 1) ↔ short = true ∨ permit = true := by
  rw [D.edgeTemplate_size_eq short permit j u f hu hf]
  have hnu := nu_pos D.graph.n
  have hdelta := Geometry.delta_pos D.graph.edges.length D.R D.geometryBound D.L
  have hproduct := mul_pos hnu hdelta
  cases short <;> cases permit <;> simp <;> nlinarith

theorem edgeTemplate_short_feasible {v : D.Vertex} (permit : Bool)
    (j : D.JobCopy v) (u : D.GlobalCopy) (f : D.FlagCopy)
    (hu : u.1 = .edge (D.jobPosition j).1 permit) (hf : f.1 = .edge) :
    (∑ r, D.itemSize (D.localTemplateItems (.inr (true, j))
      (.inr j) u (.inr j) f r)) ≤ 1 :=
  (D.edgeTemplate_feasible_iff true permit j u f hu hf).mpr (Or.inl rfl)

theorem edgeTemplate_long_feasible_iff {v : D.Vertex} (permit : Bool)
    (j : D.JobCopy v) (u : D.GlobalCopy) (f : D.FlagCopy)
    (hu : u.1 = .edge (D.jobPosition j).1 permit) (hf : f.1 = .edge) :
    ((∑ r, D.itemSize (D.localTemplateItems (.inr (false, j))
      (.inr j) u (.inr j) f r)) ≤ 1) ↔ permit = true := by
  simpa using D.edgeTemplate_feasible_iff false permit j u f hu hf

theorem stateEdgeTemplate_size_eq_one {v : D.Vertex} (selected : Bool)
    (j : D.JobCopy v) (u : D.GlobalCopy) (f : D.FlagCopy)
    (hu : u.1 = .edge (D.jobPosition j).1 (!selected)) (hf : f.1 = .edge) :
    (∑ r, D.itemSize (D.localTemplateItems (.inr (selected, j))
      (.inr j) u (.inr j) f r)) = 1 := by
  rw [D.edgeTemplate_size_eq selected (!selected) j u f hu hf]
  cases selected <;> simp

end InventoryData

end BinPackingGap

noncomputable section

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

abbrev Template := Σ v : D.Vertex, Bool × D.LocalBin v

def templateGlobalSpecies (t : D.Template) : GlobalSpecies D.graph :=
  D.stateGlobalSpecies t.2.1 t.2.2

def templateFlagSpecies (t : D.Template) : FlagSpecies :=
  D.stateFlagSpecies t.2.2

def templateRowCopy (t : D.Template) : Σ v : D.Vertex, D.RowAt v :=
  ⟨t.1, D.stateRowEquiv t.1 t.2.1 t.2.2⟩

def templateAnchorCopy (S : ∀ v s, D.LocalState v s) (t : D.Template) :
    Σ v : D.Vertex, D.AnchorAt v :=
  ⟨t.1, (S t.1 t.2.1).anchorAtEquiv t.2.2⟩

def templateLocalCopy (S : ∀ v s, D.LocalState v s) (t : D.Template) :
    Σ v : D.Vertex, D.LocalAt v :=
  ⟨t.1, (S t.1 t.2.1).localAtEquiv t.2.2⟩

def templateBase (S : ∀ v s, D.LocalState v s) (t : D.Template) :
    Finset D.packingInstance.Item :=
  {D.itemEquiv ⟨.x, D.templateRowCopy t⟩,
   D.itemEquiv ⟨.anchor, D.templateAnchorCopy S t⟩,
   D.itemEquiv ⟨.«local», D.templateLocalCopy S t⟩}

theorem templateBase_subset_labeledItems (S : ∀ v s, D.LocalState v s)
    (t : D.Template) : D.templateBase S t ⊆ D.labeledItems := by
  intro i hi
  simp only [templateBase, Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl <;> simp

private theorem templateTagged_ne {r s : Role} (hrs : r ≠ s)
    (a : D.RoleCopies r) (b : D.RoleCopies s) :
    D.itemEquiv ⟨r, a⟩ ≠ D.itemEquiv ⟨s, b⟩ := by
  intro h
  exact hrs (congrArg (fun i : D.Item => i.1) (D.itemEquiv.injective h))

private theorem templateTagged_eq_iff (r : Role) (a b : D.RoleCopies r) :
    D.itemEquiv ⟨r, a⟩ = D.itemEquiv ⟨r, b⟩ ↔ a = b := by
  constructor
  · intro h
    exact sigma_mk_injective (β := D.RoleCopies) (i := r) (D.itemEquiv.injective h)
  · rintro rfl
    rfl

theorem card_templateBase (S : ∀ v s, D.LocalState v s) (t : D.Template) :
    (D.templateBase S t).card = 3 := by
  unfold templateBase
  apply Finset.card_triple_eq_three_iff.mpr
  exact ⟨D.templateTagged_ne (by decide : Role.x ≠ .anchor) _ _,
    D.templateTagged_ne (by decide : Role.x ≠ .«local») _ _,
    D.templateTagged_ne (by decide : Role.anchor ≠ .«local») _ _⟩

def templateCopyEquiv {C : D.Vertex → Type*}
    (e : ∀ v (_s : Bool), D.LocalBin v ≃ C v) : D.Template ≃ Bool × (Σ v, C v) where
  toFun t := (t.2.1, ⟨t.1, e t.1 t.2.1 t.2.2⟩)
  invFun t := ⟨t.2.1, t.1, (e t.2.1 t.1).symm t.2.2⟩
  left_inv := by
    rintro ⟨v, s, b⟩
    simp only [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨s, v, c⟩
    simp only [Equiv.apply_symm_apply]

@[simp] theorem templateCopyEquiv_apply {C : D.Vertex → Type*}
    (e : ∀ v (_s : Bool), D.LocalBin v ≃ C v) (t : D.Template) :
    D.templateCopyEquiv e t = (t.2.1, ⟨t.1, e t.1 t.2.1 t.2.2⟩) := rfl

private def templateFiberBoolEquiv {T C : Type*} (e : T ≃ Bool × C) (c : C) :
    {t : T // (e t).2 = c} ≃ Bool where
  toFun x := (e x.1).1
  invFun b := ⟨e.symm (b, c), by simp only [Equiv.apply_symm_apply]⟩
  left_inv := by
    intro x
    apply Subtype.ext
    apply e.injective
    change e (e.symm ((e x.1).1, c)) = e x.1
    rw [e.apply_symm_apply]
    exact Prod.ext rfl x.2.symm
  right_inv := by
    intro b
    simp only [Equiv.apply_symm_apply]

theorem card_templateCopy_fiber {C : D.Vertex → Type*}
    [DecidableEq (Σ v, C v)]
    (e : ∀ v (_s : Bool), D.LocalBin v ≃ C v) (c : Σ v, C v) :
    ((Finset.univ : Finset D.Template).filter
      (fun t => (D.templateCopyEquiv e t).2 = c)).card = 2 := by
  classical
  rw [← Fintype.card_subtype (fun t : D.Template => (D.templateCopyEquiv e t).2 = c)]
  exact (Fintype.card_congr (templateFiberBoolEquiv (D.templateCopyEquiv e) c)).trans
    Fintype.card_bool

private theorem card_templatePredicate {C : Type*}
    (e : D.Template ≃ Bool × C) (c : C) (p : D.Template → Prop) [DecidablePred p]
    (hp : ∀ t, p t ↔ (e t).2 = c) :
    ((Finset.univ : Finset D.Template).filter p).card = 2 := by
  rw [← Fintype.card_subtype p]
  exact (Fintype.card_congr
    ((Equiv.subtypeEquivRight hp).trans (templateFiberBoolEquiv e c))).trans
      Fintype.card_bool

@[simp] theorem itemEquiv_x_mem_templateBase (S : ∀ v s, D.LocalState v s)
    (t : D.Template) (c : D.RoleCopies .x) :
    D.itemEquiv ⟨.x, c⟩ ∈ D.templateBase S t ↔ D.templateRowCopy t = c := by
  have hxa := D.templateTagged_ne (by decide : Role.x ≠ .anchor) c
    (D.templateAnchorCopy S t)
  have hxl := D.templateTagged_ne (by decide : Role.x ≠ .«local») c
    (D.templateLocalCopy S t)
  simp only [templateBase, Finset.mem_insert, Finset.mem_singleton, hxa, hxl, or_false]
  exact (D.templateTagged_eq_iff .x c (D.templateRowCopy t)).trans eq_comm

@[simp] theorem itemEquiv_anchor_mem_templateBase (S : ∀ v s, D.LocalState v s)
    (t : D.Template) (c : D.RoleCopies .anchor) :
    D.itemEquiv ⟨.anchor, c⟩ ∈ D.templateBase S t ↔ D.templateAnchorCopy S t = c := by
  have hax := D.templateTagged_ne (by decide : Role.anchor ≠ .x) c
    (D.templateRowCopy t)
  have hal := D.templateTagged_ne (by decide : Role.anchor ≠ .«local») c
    (D.templateLocalCopy S t)
  simp only [templateBase, Finset.mem_insert, Finset.mem_singleton, hax, hal,
    false_or, or_false]
  exact (D.templateTagged_eq_iff .anchor c (D.templateAnchorCopy S t)).trans eq_comm

@[simp] theorem itemEquiv_local_mem_templateBase (S : ∀ v s, D.LocalState v s)
    (t : D.Template) (c : D.RoleCopies .«local») :
    D.itemEquiv ⟨.«local», c⟩ ∈ D.templateBase S t ↔ D.templateLocalCopy S t = c := by
  have hlx := D.templateTagged_ne (by decide : Role.«local» ≠ .x) c
    (D.templateRowCopy t)
  have hla := D.templateTagged_ne (by decide : Role.«local» ≠ .anchor) c
    (D.templateAnchorCopy S t)
  simp only [templateBase, Finset.mem_insert, Finset.mem_singleton, hlx, hla, false_or]
  exact (D.templateTagged_eq_iff .«local» c (D.templateLocalCopy S t)).trans eq_comm

@[simp] theorem itemEquiv_global_not_mem_templateBase (S : ∀ v s, D.LocalState v s)
    (t : D.Template) (c : D.RoleCopies .«global») :
    D.itemEquiv ⟨.«global», c⟩ ∉ D.templateBase S t := by
  simp only [templateBase, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨D.templateTagged_ne (by decide : Role.«global» ≠ .x) _ _,
    D.templateTagged_ne (by decide : Role.«global» ≠ .anchor) _ _,
    D.templateTagged_ne (by decide : Role.«global» ≠ .«local») _ _⟩

@[simp] theorem itemEquiv_flag_not_mem_templateBase (S : ∀ v s, D.LocalState v s)
    (t : D.Template) (c : D.RoleCopies .flag) :
    D.itemEquiv ⟨.flag, c⟩ ∉ D.templateBase S t := by
  simp only [templateBase, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨D.templateTagged_ne (by decide : Role.flag ≠ .x) _ _,
    D.templateTagged_ne (by decide : Role.flag ≠ .anchor) _ _,
    D.templateTagged_ne (by decide : Role.flag ≠ .«local») _ _⟩

theorem templateBase_appearance_count (S : ∀ v s, D.LocalState v s)
    (i : D.packingInstance.Item) :
    ((Finset.univ : Finset D.Template).filter (fun t => i ∈ D.templateBase S t)).card =
      if i ∈ D.labeledItems then 2 else 0 := by
  classical
  obtain ⟨⟨r, c⟩, rfl⟩ := D.itemEquiv.surjective i
  cases r with
  | x =>
    rw [ite_eq_left (by simp)]
    apply D.card_templatePredicate (D.templateCopyEquiv (fun v s => D.stateRowEquiv v s)) c
      (fun t => D.itemEquiv ⟨.x, c⟩ ∈ D.templateBase S t)
    intro t
    simpa only [templateCopyEquiv_apply, templateRowCopy] using
      D.itemEquiv_x_mem_templateBase S t c
  | anchor =>
    rw [ite_eq_left (by simp)]
    apply D.card_templatePredicate
      (D.templateCopyEquiv (fun v s => (S v s).anchorAtEquiv)) c
      (fun t => D.itemEquiv ⟨.anchor, c⟩ ∈ D.templateBase S t)
    intro t
    simpa only [templateCopyEquiv_apply, templateAnchorCopy] using
      D.itemEquiv_anchor_mem_templateBase S t c
  | «global» => simp
  | «local» =>
    rw [ite_eq_left (by simp)]
    apply D.card_templatePredicate
      (D.templateCopyEquiv (fun v s => (S v s).localAtEquiv)) c
      (fun t => D.itemEquiv ⟨.«local», c⟩ ∈ D.templateBase S t)
    intro t
    simpa only [templateCopyEquiv_apply, templateLocalCopy] using
      D.itemEquiv_local_mem_templateBase S t c
  | flag => simp

@[simp] theorem packingInstance_size_itemEquiv (i : D.Item) :
    D.packingInstance.size (D.itemEquiv i) = D.itemSize i := by
  change D.itemSize (D.itemEquiv.symm (D.itemEquiv i)) = D.itemSize i
  rw [Equiv.symm_apply_apply]

theorem templateBase_complete_eq_image (S : ∀ v s, D.LocalState v s)
    (t : D.Template) (u : D.GlobalCopy) (f : D.FlagCopy) :
    D.templateBase S t ∪ {D.itemEquiv ⟨.«global», u⟩, D.itemEquiv ⟨.flag, f⟩} =
      Finset.univ.image (fun r => D.itemEquiv
        (D.localTemplateItems (D.stateRowEquiv t.1 t.2.1 t.2.2)
          ((S t.1 t.2.1).anchorAtEquiv t.2.2) u
          ((S t.1 t.2.1).localAtEquiv t.2.2) f r)) := by
  apply Finset.ext
  intro i
  constructor
  · intro hi
    simp only [Finset.mem_union, templateBase, Finset.mem_insert,
      Finset.mem_singleton] at hi
    rcases hi with (rfl | rfl | rfl) | (rfl | rfl)
    · exact Finset.mem_image.mpr ⟨.x, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.anchor, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.«local», Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.«global», Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨.flag, Finset.mem_univ _, rfl⟩
  · intro hi
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hi
    cases r with
    | x =>
      apply Finset.mem_union_left
      exact Finset.mem_insert_self _ _
    | anchor =>
      apply Finset.mem_union_left
      apply Finset.mem_insert_of_mem
      exact Finset.mem_insert_self _ _
    | «global» =>
      apply Finset.mem_union_right
      exact Finset.mem_insert_self _ _
    | «local» =>
      apply Finset.mem_union_left
      apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      exact Finset.mem_singleton_self _
    | flag =>
      apply Finset.mem_union_right
      apply Finset.mem_insert_of_mem
      exact Finset.mem_singleton_self _

theorem templateBase_size_sum (S : ∀ v s, D.LocalState v s)
    (t : D.Template) (u : D.GlobalCopy) (f : D.FlagCopy) :
    (∑ i ∈ D.templateBase S t ∪
      {D.itemEquiv ⟨.«global», u⟩, D.itemEquiv ⟨.flag, f⟩}, D.packingInstance.size i) =
    ∑ r, D.itemSize (D.localTemplateItems (D.stateRowEquiv t.1 t.2.1 t.2.2)
      ((S t.1 t.2.1).anchorAtEquiv t.2.2) u
      ((S t.1 t.2.1).localAtEquiv t.2.2) f r) := by
  rw [D.templateBase_complete_eq_image S t u f, Finset.sum_image]
  · simp only [packingInstance_size_itemEquiv]
  · intro r _ r' _ h
    exact D.localTemplateItems_injective _ _ _ _ _ (D.itemEquiv.injective h)

theorem templateBase_capacity (S : ∀ v s, D.LocalState v s)
    (t : D.Template) (u : D.GlobalCopy) (f : D.FlagCopy)
    (hu : u.1 = D.templateGlobalSpecies t) (hf : f.1 = D.templateFlagSpecies t) :
    (∑ i ∈ D.templateBase S t ∪
      {D.itemEquiv ⟨.«global», u⟩, D.itemEquiv ⟨.flag, f⟩}, D.packingInstance.size i) ≤ 1 := by
  rw [D.templateBase_size_sum S t u f]
  rcases t with ⟨v, selected, b⟩
  rcases b with b | j
  · exact (D.stateMainTemplate_feasible_iff selected b ((S v selected).anchorEquiv b)
      ((S v selected).localEquiv b) u f hu hf).mpr
        ((S v selected).completion_le_deadline b)
  · exact (D.stateEdgeTemplate_size_eq_one selected j u f hu hf).le

end BinPackingGap.InventoryData

end

end OAI
