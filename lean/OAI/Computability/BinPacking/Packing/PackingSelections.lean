import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import OAI.Computability.BinPacking.Inventory.CurrentMatches
import OAI.Computability.BinPacking.Inventory.InventoryScores

namespace OAI

noncomputable section

section
open scoped BigOperators

namespace BinPackingGap
namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

def subclass (e : D.Item ≃ I.Item) : I.Item → Subclass :=
  D.itemSubclass ∘ e.symm

def label (e : D.Item ≃ I.Item) : I.Item → Option D.Vertex :=
  D.itemLabel ∘ e.symm

def globalResources (e : D.Item ≃ I.Item) (s : GlobalSpecies D.graph) :
    Finset I.Item := by
  classical
  exact Finset.univ.image fun i : Fin (D.globalStock s) => e ⟨.«global», ⟨s, i⟩⟩

theorem globalCopy_injective (e : D.Item ≃ I.Item) (s : GlobalSpecies D.graph) :
    Function.Injective (fun i : Fin (D.globalStock s) => e ⟨.«global», ⟨s, i⟩⟩) := by
  intro i j hij
  have h := e.injective hij
  have hg := @sigma_mk_injective Role D.RoleCopies .«global» _ _ h
  exact @sigma_mk_injective (GlobalSpecies D.graph)
    (fun s => Fin (D.globalStock s)) s i j hg

@[simp] theorem globalResources_card (e : D.Item ≃ I.Item)
    (s : GlobalSpecies D.graph) :
    (globalResources e s).card = D.globalStock s := by
  classical
  simp only [globalResources, Finset.card_image_of_injective _ (globalCopy_injective e s),
    Finset.card_univ, Fintype.card_fin]

@[simp] theorem mem_globalResources (e : D.Item ≃ I.Item)
    (s : GlobalSpecies D.graph) (x : I.Item) :
    x ∈ globalResources e s ↔
      ∃ i : Fin (D.globalStock s), e ⟨.«global», ⟨s, i⟩⟩ = x := by
  classical
  simp [globalResources]

theorem globalResources_disjoint (e : D.Item ≃ I.Item)
    {s t : GlobalSpecies D.graph} (hst : s ≠ t) :
    Disjoint (globalResources e s) (globalResources e t) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, hi⟩ := (mem_globalResources e s x).mp hx
  obtain ⟨j, hj⟩ := (mem_globalResources e t x).mp hy
  have h := e.injective (hi.trans hj.symm)
  have hg : (⟨s, i⟩ : D.GlobalCopy) = ⟨t, j⟩ := by
    exact @sigma_mk_injective Role D.RoleCopies .«global» _ _ h
  exact hst (congrArg Sigma.fst hg)

def fundedTuples (p : Packing I b) (e : D.Item ≃ I.Item)
    (s : GlobalSpecies D.graph) (v : D.Vertex) : Finset (p.TableBin (subclass e)) := by
  classical
  exact (Coverage.mainTuplesAt p (subclass e) (label e) v).filter fun t =>
    p.itemAtRole (subclass e) t .«global» ∈ globalResources e s

@[simp] theorem mem_fundedTuples (p : Packing I b) (e : D.Item ≃ I.Item)
    (s : GlobalSpecies D.graph) (v : D.Vertex) (t : p.TableBin (subclass e)) :
    t ∈ fundedTuples p e s v ↔
      t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v ∧
      p.itemAtRole (subclass e) t .«global» ∈ globalResources e s := by
  classical
  simp [fundedTuples]

theorem fundedTuples_subset_main (p : Packing I b) (e : D.Item ≃ I.Item)
    (s : GlobalSpecies D.graph) (v : D.Vertex) :
    fundedTuples p e s v ⊆ Coverage.mainTuplesAt p (subclass e) (label e) v := by
  classical
  exact Finset.filter_subset _ _

theorem fundedTuples_disjoint_label (p : Packing I b) (e : D.Item ≃ I.Item)
    (s : GlobalSpecies D.graph) {v w : D.Vertex} (hvw : v ≠ w) :
    Disjoint (fundedTuples p e s v) (fundedTuples p e s w) :=
  (Coverage.mainTuplesAt_disjoint_label p (subclass e) (label e) hvw).mono
    (fundedTuples_subset_main p e s v) (fundedTuples_subset_main p e s w)

theorem sum_card_main_subsets_le_resources (p : Packing I b) (e : D.Item ≃ I.Item)
    (S : D.Vertex → Finset (p.TableBin (subclass e)))
    (hS : ∀ v, S v ⊆ Coverage.mainTuplesAt p (subclass e) (label e) v)
    (r : Role) (resources : Finset I.Item)
    (hres : ∀ v t, t ∈ S v → p.itemAtRole (subclass e) t r ∈ resources) :
    (∑ v, (S v).card) ≤ resources.card := by
  classical
  have hdis : ∀ v ∈ (Finset.univ : Finset D.Vertex),
      ∀ w ∈ (Finset.univ : Finset D.Vertex), v ≠ w → Disjoint (S v) (S w) := by
    intro v _ w _ hvw
    exact (Coverage.mainTuplesAt_disjoint_label p (subclass e) (label e) hvw).mono
      (hS v) (hS w)
  calc
    (∑ v, (S v).card) = (Finset.univ.biUnion S).card :=
      (Finset.card_biUnion hdis).symm
    _ ≤ resources.card := by
      apply Coverage.card_le_role_resources p (subclass e) _ r resources
      intro t ht
      obtain ⟨v, _, htv⟩ := Finset.mem_biUnion.mp ht
      exact hres v t htv

theorem fundedTuples_sum_card_le (p : Packing I b) (e : D.Item ≃ I.Item)
    (s : GlobalSpecies D.graph) :
    (∑ v, (fundedTuples p e s v).card) ≤ D.globalStock s := by
  rw [← globalResources_card e s]
  apply sum_card_main_subsets_le_resources p e (fundedTuples p e s)
    (fundedTuples_subset_main p e s) .«global» (globalResources e s)
  intro v t ht
  exact ((mem_fundedTuples p e s v t).mp ht).2

def xplus (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex) : ℕ :=
  (fundedTuples p e (.up true) v).card

def xminus (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex) : ℕ :=
  (fundedTuples p e (.um true) v).card

theorem xplus_budget (p : Packing I b) (e : D.Item ≃ I.Item) :
    (∑ v, xplus p e v) ≤ D.d * D.k :=
  fundedTuples_sum_card_le p e (.up true)

theorem xminus_budget (p : Packing I b) (e : D.Item ≃ I.Item) :
    (∑ v, xminus p e v) ≤ D.d * (D.graph.n - D.k) :=
  fundedTuples_sum_card_le p e (.um true)

theorem total_budget (p : Packing I b) (e : D.Item ≃ I.Item) (hk : D.k ≤ D.graph.n) :
    (∑ v, (xplus p e v + xminus p e v)) ≤ D.d * D.graph.n := by
  rw [Finset.sum_add_distrib]
  calc
    _ ≤ D.d * D.k + D.d * (D.graph.n - D.k) :=
      Nat.add_le_add (xplus_budget p e) (xminus_budget p e)
    _ = D.d * D.graph.n := by
      have hsum : D.k + (D.graph.n - D.k) = D.graph.n := by omega
      rw [← Nat.mul_add, hsum]

def localDepthResources (e : D.Item ≃ I.Item) (v : D.Vertex) (ell : D.Depth) :
    Finset I.Item := by
  classical
  exact Finset.univ.image fun i : Fin (D.quota ell.val) =>
    e ⟨.«local», ⟨v, Sum.inl (Sum.inl ⟨ell, i⟩)⟩⟩

theorem localDepthCopy_injective (e : D.Item ≃ I.Item) (v : D.Vertex) (ell : D.Depth) :
    Function.Injective (fun i : Fin (D.quota ell.val) =>
      e ⟨.«local», ⟨v, Sum.inl (Sum.inl ⟨ell, i⟩)⟩⟩) := by
  intro i j hij
  have h := e.injective hij
  have hl := @sigma_mk_injective Role D.RoleCopies .«local» _ _ h
  have hv := @sigma_mk_injective D.Vertex D.LocalAt v _ _ hl
  have hp : (⟨ell, i⟩ : D.PositiveLocal) = ⟨ell, j⟩ :=
    Sum.inl.inj (Sum.inl.inj hv)
  exact @sigma_mk_injective D.Depth (fun ell => Fin (D.quota ell.val)) ell i j hp

@[simp] theorem localDepthResources_card (e : D.Item ≃ I.Item)
    (v : D.Vertex) (ell : D.Depth) :
    (localDepthResources e v ell).card = D.quota ell.val := by
  classical
  simp only [localDepthResources,
    Finset.card_image_of_injective _ (localDepthCopy_injective e v ell),
    Finset.card_univ, Fintype.card_fin]

theorem card_le_localDepth_stock (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (ell : D.Depth) (S : Finset (p.TableBin (subclass e)))
    (hres : ∀ t ∈ S,
      p.itemAtRole (subclass e) t .«local» ∈ localDepthResources e v ell) :
    S.card ≤ D.quota ell.val := by
  rw [← localDepthResources_card e v ell]
  exact Coverage.card_le_role_resources p (subclass e) S .«local» _ hres

def positiveLocalResources (e : D.Item ≃ I.Item) (v : D.Vertex) : Finset I.Item := by
  classical
  exact Finset.univ.image fun i : D.PositiveLocal =>
    e ⟨.«local», ⟨v, Sum.inl (Sum.inl i)⟩⟩

@[simp] theorem mem_positiveLocalResources (e : D.Item ≃ I.Item)
    (v : D.Vertex) (x : I.Item) :
    x ∈ positiveLocalResources e v ↔
      ∃ i : D.PositiveLocal, e ⟨.«local», ⟨v, Sum.inl (Sum.inl i)⟩⟩ = x := by
  classical
  simp [positiveLocalResources]

theorem positiveLocalCopy_injective (e : D.Item ≃ I.Item) (v : D.Vertex) :
    Function.Injective (fun i : D.PositiveLocal =>
      e ⟨.«local», ⟨v, Sum.inl (Sum.inl i)⟩⟩) := by
  intro i j hij
  have h := e.injective hij
  have hl := @sigma_mk_injective Role D.RoleCopies .«local» _ _ h
  have hv := @sigma_mk_injective D.Vertex D.LocalAt v _ _ hl
  exact Sum.inl.inj (Sum.inl.inj hv)

@[simp] theorem positiveLocalResources_card (e : D.Item ≃ I.Item) (v : D.Vertex) :
    (positiveLocalResources e v).card = D.P := by
  classical
  rw [positiveLocalResources,
    Finset.card_image_of_injective _ (positiveLocalCopy_injective e v),
    Finset.card_univ, D.card_positiveLocal]

theorem card_le_positiveLocal_stock (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (S : Finset (p.TableBin (subclass e)))
    (hres : ∀ t ∈ S,
      p.itemAtRole (subclass e) t .«local» ∈ positiveLocalResources e v) :
    S.card ≤ D.P := by
  rw [← positiveLocalResources_card e v]
  exact Coverage.card_le_role_resources p (subclass e) S .«local» _ hres

end PackingCounts
end BinPackingGap

end

namespace BinPackingGap
namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

private def elementAtRole (i : D.Item) (r : Role) (h : i.1 = r) : D.RoleCopies r :=
  h ▸ i.2

private theorem elementAtRole_mk (i : D.Item) (r : Role) (h : i.1 = r) :
    (⟨r, elementAtRole i r h⟩ : D.Item) = i := by
  rcases i with ⟨s, i⟩
  dsimp at h
  cases h
  rfl

theorem selected_role (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (r : Role) :
    (e.symm (p.itemAtRole (subclass e) t r)).1 = r := by
  change D.itemRole (e.symm (p.itemAtRole (subclass e) t r)) = r
  rw [← D.itemSubclass_role]
  exact p.itemAtRole_role (subclass e) t r

def roleCopy (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (r : Role) : D.RoleCopies r :=
  elementAtRole (e.symm (p.itemAtRole (subclass e) t r)) r (selected_role p e t r)

@[simp] theorem roleCopy_item (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (r : Role) :
    e ⟨r, roleCopy p e t r⟩ = p.itemAtRole (subclass e) t r := by
  rw [roleCopy, elementAtRole_mk, e.apply_symm_apply]

theorem roleCopy_injective (p : Packing I b) (e : D.Item ≃ I.Item) (r : Role) :
    Function.Injective (fun t => roleCopy p e t r) := by
  intro t u h
  change roleCopy p e t r = roleCopy p e u r at h
  apply p.itemAtRole_injective (subclass e) r
  change p.itemAtRole (subclass e) t r = p.itemAtRole (subclass e) u r
  rw [← roleCopy_item p e t r, ← roleCopy_item p e u r, h]

theorem roleCopy_subclass (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (r : Role) :
    D.itemSubclass ⟨r, roleCopy p e t r⟩ = patternSubclass (p.tablePattern (subclass e) t) r := by
  have h := p.itemAtRole_subclass (subclass e) t r
  rw [← roleCopy_item p e t r] at h
  simpa only [subclass, Function.comp_apply, e.symm_apply_apply] using h

abbrev rowCopy (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : Σ v : D.Vertex, D.RowAt v :=
  roleCopy p e t .x

abbrev anchorCopy (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : Σ v : D.Vertex, D.AnchorAt v :=
  roleCopy p e t .anchor

abbrev globalCopy (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : D.GlobalCopy :=
  roleCopy p e t .«global»

abbrev localCopy (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : Σ v : D.Vertex, D.LocalAt v :=
  roleCopy p e t .«local»

theorem selected_global_resource_iff (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (s : GlobalSpecies D.graph) :
    p.itemAtRole (subclass e) t .«global» ∈ globalResources e s ↔
      (globalCopy p e t).1 = s := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := (mem_globalResources e s _).mp h
    rw [← roleCopy_item p e t .«global»] at hi
    have he := e.injective hi
    have hg : (⟨s, i⟩ : D.GlobalCopy) = globalCopy p e t := by
      exact @sigma_mk_injective Role D.RoleCopies .«global» _ _ he
    exact (congrArg Sigma.fst hg).symm
  · intro h
    rcases hg : globalCopy p e t with ⟨s', i⟩
    have hs : s' = s := by simpa only [hg] using h
    subst s'
    apply (mem_globalResources e s _).mpr
    refine ⟨i, ?_⟩
    rw [← roleCopy_item p e t .«global»]
    exact congrArg (fun x : D.GlobalCopy => e ⟨.«global», x⟩) hg.symm

@[simp] theorem selected_row_label (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) :
    label e (p.itemAtRole (subclass e) t .x) = some (rowCopy p e t).1 := by
  change D.itemLabel (e.symm (p.itemAtRole (subclass e) t .x)) =
    some (rowCopy p e t).1
  rw [← roleCopy_item p e t .x, e.symm_apply_apply]
  rfl

@[simp] theorem selected_anchor_label (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) :
    label e (p.itemAtRole (subclass e) t .anchor) = some (anchorCopy p e t).1 := by
  change D.itemLabel (e.symm (p.itemAtRole (subclass e) t .anchor)) =
    some (anchorCopy p e t).1
  rw [← roleCopy_item p e t .anchor, e.symm_apply_apply]
  rfl

@[simp] theorem selected_local_label (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) :
    label e (p.itemAtRole (subclass e) t .«local») = some (localCopy p e t).1 := by
  change D.itemLabel (e.symm (p.itemAtRole (subclass e) t .«local»)) =
    some (localCopy p e t).1
  rw [← roleCopy_item p e t .«local», e.symm_apply_apply]
  rfl

theorem good_row_vertex (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.goodTuplesAt p (subclass e) (label e) v) :
    (rowCopy p e t).1 = v := by
  have ht' := (Coverage.mem_goodTuplesAt p (subclass e) (label e) v t).mp ht
  have h := ht'.1.1.trans ht'.2
  rw [selected_row_label] at h
  exact Option.some.inj h

theorem good_anchor_vertex (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.goodTuplesAt p (subclass e) (label e) v) :
    (anchorCopy p e t).1 = v := by
  have h := ((Coverage.mem_goodTuplesAt p (subclass e) (label e) v t).mp ht).2
  rw [selected_anchor_label] at h
  exact Option.some.inj h

theorem good_local_vertex (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.goodTuplesAt p (subclass e) (label e) v) :
    (localCopy p e t).1 = v := by
  have ht' := (Coverage.mem_goodTuplesAt p (subclass e) (label e) v t).mp ht
  have h := ht'.1.2.trans ht'.2
  rw [selected_local_label] at h
  exact Option.some.inj h

def zeroPositiveTuples (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex) :
    Finset (p.TableBin (subclass e)) := by
  classical
  exact (Coverage.mainTuplesAt p (subclass e) (label e) v).filter fun t =>
    D.globalUnit (globalCopy p e t) = false ∧
      p.itemAtRole (subclass e) t .«local» ∈ positiveLocalResources e v

def tupleLocalDepth (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : ℕ :=
  ((D.localDepth (localCopy p e t).2).map Subtype.val).getD 0

@[simp] theorem mem_zeroPositiveTuples (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e)) :
    t ∈ zeroPositiveTuples p e v ↔
      t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v ∧
        D.globalUnit (globalCopy p e t) = false ∧
          p.itemAtRole (subclass e) t .«local» ∈ positiveLocalResources e v := by
  classical
  simp [zeroPositiveTuples, and_assoc]

theorem zeroPositiveTuples_card_le (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) : (zeroPositiveTuples p e v).card ≤ D.P := by
  apply card_le_positiveLocal_stock p e v
  intro t ht
  exact ((mem_zeroPositiveTuples p e v t).mp ht).2.2

theorem localCopy_eq_of_positive (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (hpos : p.itemAtRole (subclass e) t .«local» ∈ positiveLocalResources e v) :
    ∃ i : D.PositiveLocal, localCopy p e t = ⟨v, Sum.inl (Sum.inl i)⟩ := by
  obtain ⟨i, hi⟩ := (mem_positiveLocalResources e v _).mp hpos
  refine ⟨i, ?_⟩
  rw [← roleCopy_item p e t .«local»] at hi
  have h := e.injective hi
  have h' : (⟨v, Sum.inl (Sum.inl i)⟩ : Σ w : D.Vertex, D.LocalAt w) =
      localCopy p e t := by
    exact @sigma_mk_injective Role D.RoleCopies .«local» _ _ h
  exact h'.symm

theorem selected_depth_mem (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ zeroPositiveTuples p e v) :
    tupleLocalDepth p e t ∈ Finset.Icc 1 D.L := by
  obtain ⟨i, hi⟩ := localCopy_eq_of_positive p e v t
    (((mem_zeroPositiveTuples p e v t).mp ht).2.2)
  have hd : tupleLocalDepth p e t = i.1.val := by
    unfold tupleLocalDepth
    rw [hi]
    rfl
  rw [hd]
  exact i.1.property

theorem selected_localDepth_resource (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (ell : D.Depth) (t : p.TableBin (subclass e))
    (ht : t ∈ zeroPositiveTuples p e v) (hell : tupleLocalDepth p e t = ell.val) :
    p.itemAtRole (subclass e) t .«local» ∈ localDepthResources e v ell := by
  classical
  obtain ⟨⟨depth, i⟩, hi⟩ := localCopy_eq_of_positive p e v t
    (((mem_zeroPositiveTuples p e v t).mp ht).2.2)
  have hd : tupleLocalDepth p e t = depth.val := by
    unfold tupleLocalDepth
    rw [hi]
    rfl
  have hdepth : depth = ell := Subtype.ext (hd.symm.trans hell)
  subst depth
  apply Finset.mem_image.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rw [← roleCopy_item p e t .«local»]
  exact congrArg (fun x : (Σ w : D.Vertex, D.LocalAt w) => e ⟨.«local», x⟩) hi.symm

theorem zeroPositiveTuples_depth_card_le (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (ell : D.Depth) :
    ((zeroPositiveTuples p e v).filter (fun t => tupleLocalDepth p e t = ell.val)).card ≤
      D.quota ell.val := by
  classical
  apply card_le_localDepth_stock p e v ell
  intro t ht
  obtain ⟨ht, he⟩ := Finset.mem_filter.mp ht
  exact selected_localDepth_resource p e v ell t ht he

end PackingCounts
end BinPackingGap

end

end OAI
