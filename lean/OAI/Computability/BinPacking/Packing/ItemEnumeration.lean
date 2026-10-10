import Mathlib.Data.List.FinRange
import Mathlib.Data.List.NodupEquivFin
import OAI.Computability.BinPacking.Inventory.InventoryScores

namespace OAI

noncomputable section

namespace BinPackingGap.InventoryData

variable (D : InventoryData)

private theorem length_flatMap_constant {α β : Type*} (l : List α)
    (f : α → List β) (n : ℕ) (hf : ∀ a, (f a).length = n) :
    (l.flatMap f).length = l.length * n := by
  induction l with
  | nil => simp
  | cons a l ih => simp [hf, ih, Nat.add_mul, Nat.add_comm]

def treeRowList : List D.TreeRow :=
  ((Finset.univ : Finset D.plus.Node).toList.flatMap fun v =>
    (List.finRange D.d).map fun j => Sum.inl (v, j)) ++
  ((Finset.univ : Finset D.minus.Node).toList.flatMap fun v =>
    (List.finRange D.d).map fun j => Sum.inr (Sum.inl (v, j))) ++
  (List.finRange D.P).map (fun j => Sum.inr (Sum.inr j))

def positiveLocalList : List D.PositiveLocal :=
  (Finset.univ : Finset D.PositiveLocal).toList

theorem mem_treeRowList (r : D.TreeRow) : r ∈ D.treeRowList := by
  classical
  rcases r with ⟨v, j⟩ | (⟨v, j⟩ | j) <;>
    simp [treeRowList]

theorem mem_positiveLocalList (r : D.PositiveLocal) : r ∈ D.positiveLocalList := by
  classical
  simp [positiveLocalList]

theorem treeRowList_length : D.treeRowList.length = D.t := by
  classical
  have hp := length_flatMap_constant (Finset.univ : Finset D.plus.Node).toList
    (fun v => (List.finRange D.d).map fun j => (Sum.inl (v, j) : D.TreeRow)) D.d
    (fun _ => by simp)
  have hm := length_flatMap_constant (Finset.univ : Finset D.minus.Node).toList
    (fun v => (List.finRange D.d).map fun j =>
      (Sum.inr (Sum.inl (v, j)) : D.TreeRow)) D.d (fun _ => by simp)
  simp only [treeRowList, List.length_append, hp, hm, List.length_map,
    List.length_finRange, Finset.length_toList, Finset.card_univ]
  dsimp [t, tPlus, tMinus]
  ring

theorem positiveLocalList_length : D.positiveLocalList.length = D.P := by
  classical
  simpa only [positiveLocalList, Finset.length_toList, Finset.card_univ] using
    D.card_positiveLocal

def vertexChunk (v : D.Vertex) : List D.Item :=
  (D.treeRowList.map fun r => ⟨.x, ⟨v, .inl r⟩⟩) ++
  (D.treeRowList.map fun r => ⟨.anchor, ⟨v, .inl (.inl r)⟩⟩) ++
  (D.positiveLocalList.map fun r => ⟨.«local», ⟨v, .inl (.inl r)⟩⟩) ++
  ((List.finRange (D.t - D.P)).map fun j =>
    ⟨.«local», ⟨v, .inl (.inr (.inl j))⟩⟩)

def vertexItems : List D.Item :=
  (List.finRange D.graph.n).flatMap D.vertexChunk

def listedJobCopy (e : D.Edge) (j : Fin D.R) (s : Fin 2) (r : Fin D.d) :
    D.JobCopy (D.graph.endpoint e s) :=
  ((⟨(e, s), rfl⟩, j), r)

def jobChunk (e : D.Edge) (j : Fin D.R) (s : Fin 2) : List D.Item :=
  let v := D.graph.endpoint e s
  let copy := D.listedJobCopy e j s
  ((List.finRange D.d).map fun r => ⟨.x, ⟨v, .inr (true, copy r)⟩⟩) ++
  ((List.finRange D.d).map fun r => ⟨.x, ⟨v, .inr (false, copy r)⟩⟩) ++
  ((List.finRange D.d).map fun r => ⟨.anchor, ⟨v, .inl (.inr (copy r))⟩⟩) ++
  ((List.finRange D.d).map fun r => ⟨.anchor, ⟨v, .inr (copy r)⟩⟩) ++
  ((List.finRange D.d).map fun r =>
    ⟨.«local», ⟨v, .inl (.inr (.inr (copy r)))⟩⟩) ++
  ((List.finRange D.d).map fun r => ⟨.«local», ⟨v, .inr (copy r)⟩⟩)

def jobItems : List D.Item :=
  (List.finRange D.graph.edges.length).flatMap fun e =>
    (List.finRange D.R).flatMap fun j =>
      (List.finRange 2).flatMap fun s => D.jobChunk e j s

def globalPool (s : GlobalSpecies D.graph) : List D.Item :=
  (List.finRange (D.globalStock s)).map fun r => ⟨.«global», ⟨s, r⟩⟩

def globalItems : List D.Item :=
  D.globalPool (.up true) ++ D.globalPool (.up false) ++
  D.globalPool (.um true) ++ D.globalPool (.um false) ++
  (List.finRange D.graph.edges.length).flatMap fun e =>
    D.globalPool (.edge e true) ++ D.globalPool (.edge e false)

def flagPool (s : FlagSpecies) : List D.Item :=
  (List.finRange (D.flagStock s)).map fun r => ⟨.flag, ⟨s, r⟩⟩

def flagItems : List D.Item :=
  D.flagPool .tree ++ D.flagPool .main ++ D.flagPool .edge

def itemList : List D.Item :=
  D.vertexItems ++ D.jobItems ++ D.globalItems ++ D.flagItems

theorem vertexChunk_length (v : D.Vertex) : (D.vertexChunk v).length = 3 * D.t := by
  simp only [vertexChunk, List.length_append, List.length_map, D.treeRowList_length,
    D.positiveLocalList_length, List.length_finRange]
  have h := D.P_le_t
  omega

theorem vertexItems_length : D.vertexItems.length = 3 * D.graph.n * D.t := by
  rw [vertexItems, length_flatMap_constant _ _ _ D.vertexChunk_length,
    List.length_finRange]
  ring

theorem jobChunk_length (e : D.Edge) (j : Fin D.R) (s : Fin 2) :
    (D.jobChunk e j s).length = 6 * D.d := by
  simp only [jobChunk, List.length_append, List.length_map, List.length_finRange]
  omega

theorem jobItems_length :
    D.jobItems.length = 12 * D.d * D.graph.edges.length * D.R := by
  have hs (e : D.Edge) (j : Fin D.R) :
      ((List.finRange 2).flatMap fun s => D.jobChunk e j s).length = 2 * (6 * D.d) := by
    rw [length_flatMap_constant _ _ _ (D.jobChunk_length e j), List.length_finRange]
  have hj (e : D.Edge) :
      ((List.finRange D.R).flatMap fun j =>
        (List.finRange 2).flatMap fun s => D.jobChunk e j s).length =
      D.R * (2 * (6 * D.d)) := by
    rw [length_flatMap_constant _ _ _ (hs e), List.length_finRange]
  rw [jobItems, length_flatMap_constant _ _ _ hj, List.length_finRange]
  ring

theorem globalPool_length (s : GlobalSpecies D.graph) :
    (D.globalPool s).length = D.globalStock s := by simp [globalPool]

theorem globalItems_length (hk : D.k ≤ D.graph.n) : D.globalItems.length = D.B := by
  have he (e : D.Edge) :
      (D.globalPool (.edge e true) ++ D.globalPool (.edge e false)).length =
      2 * (D.d * D.R) := by simp [globalPool_length, globalStock, two_mul]
  have hu := D.up_species_total hk
  have hm := D.um_species_total
  have hlen : D.globalItems.length = D.plusSlots + D.minusSlots +
      D.graph.edges.length * (2 * (D.d * D.R)) := by
    simp only [globalItems, List.length_append, D.globalPool_length,
      length_flatMap_constant _ _ _ he, List.length_finRange]
    omega
  rw [hlen, D.plusSlots_eq, D.sum_J, D.B_closed]
  dsimp [minusSlots, t]
  ring

theorem flagPool_length (s : FlagSpecies) :
    (D.flagPool s).length = D.flagStock s := by simp [flagPool]

theorem flagItems_length : D.flagItems.length = D.B := by
  simp only [flagItems, List.length_append, D.flagPool_length, flagStock,
    treeFlags, jobFlags, D.B_eq]
  omega

theorem itemList_length (hk : D.k ≤ D.graph.n) : D.itemList.length = 5 * D.B := by
  simp only [itemList, List.length_append, D.vertexItems_length, D.jobItems_length,
    D.globalItems_length hk, D.flagItems_length]
  rw [D.B_closed]
  ring

private theorem mem_itemList_of_vertex {v : D.Vertex} {i : D.Item}
    (hi : i ∈ D.vertexChunk v) : i ∈ D.itemList := by
  have hv : i ∈ D.vertexItems :=
    List.mem_flatMap.mpr ⟨v, List.mem_finRange v, hi⟩
  simp only [itemList, List.mem_append]
  exact Or.inl (Or.inl (Or.inl hv))

private theorem mem_itemList_of_job {e : D.Edge} {j : Fin D.R} {s : Fin 2} {i : D.Item}
    (hi : i ∈ D.jobChunk e j s) : i ∈ D.itemList := by
  have hj : i ∈ D.jobItems := List.mem_flatMap.mpr ⟨e, List.mem_finRange e,
    List.mem_flatMap.mpr ⟨j, List.mem_finRange j,
      List.mem_flatMap.mpr ⟨s, List.mem_finRange s, hi⟩⟩⟩
  simp only [itemList, List.mem_append]
  exact Or.inl (Or.inl (Or.inr hj))

private theorem mem_globalItems (g : D.GlobalCopy) :
    (⟨.«global», g⟩ : D.Item) ∈ D.globalItems := by
  rcases g with ⟨s, r⟩
  cases s with
  | up b => cases b <;> simp [globalItems, globalPool]
  | um b => cases b <;> simp [globalItems, globalPool]
  | edge e b =>
    have hp : (⟨.«global», ⟨.edge e b, r⟩⟩ : D.Item) ∈
        D.globalPool (.edge e true) ++ D.globalPool (.edge e false) := by
      cases b <;> simp [globalPool]
    have he : (⟨.«global», ⟨.edge e b, r⟩⟩ : D.Item) ∈
        (List.finRange D.graph.edges.length).flatMap
          (fun e => D.globalPool (.edge e true) ++ D.globalPool (.edge e false)) :=
      List.mem_flatMap.mpr ⟨e, List.mem_finRange e, hp⟩
    exact List.mem_append_right _ he

private theorem mem_flagItems (g : D.FlagCopy) : (⟨.flag, g⟩ : D.Item) ∈ D.flagItems := by
  rcases g with ⟨s, r⟩
  cases s <;> simp [flagItems, flagPool]

theorem mem_itemList (i : D.Item) : i ∈ D.itemList := by
  classical
  rcases i with ⟨role, i⟩
  cases role with
  | x =>
    rcases i with ⟨v, tree | ⟨short, job⟩⟩
    · apply D.mem_itemList_of_vertex (v := v)
      simp only [vertexChunk, List.mem_append]
      exact Or.inl (Or.inl (Or.inl
        (List.mem_map.mpr ⟨tree, D.mem_treeRowList tree, rfl⟩)))
    · rcases job with ⟨⟨⟨⟨e, s⟩, hv⟩, j⟩, r⟩
      cases hv
      apply D.mem_itemList_of_job (e := e) (j := j) (s := s)
      cases short <;> simp [jobChunk, listedJobCopy]
  | anchor =>
    rcases i with ⟨v, (tree | job) | job⟩
    · apply D.mem_itemList_of_vertex (v := v)
      simp only [vertexChunk, List.mem_append]
      exact Or.inl (Or.inl (Or.inr
        (List.mem_map.mpr ⟨tree, D.mem_treeRowList tree, rfl⟩)))
    · rcases job with ⟨⟨⟨⟨e, s⟩, hv⟩, j⟩, r⟩
      cases hv
      apply D.mem_itemList_of_job (e := e) (j := j) (s := s)
      simp [jobChunk, listedJobCopy]
    · rcases job with ⟨⟨⟨⟨e, s⟩, hv⟩, j⟩, r⟩
      cases hv
      apply D.mem_itemList_of_job (e := e) (j := j) (s := s)
      simp [jobChunk, listedJobCopy]
  | «global» =>
    simp only [itemList, List.mem_append]
    exact Or.inl (Or.inr (D.mem_globalItems i))
  | «local» =>
    rcases i with ⟨v, (positive | (zero | job)) | job⟩
    · apply D.mem_itemList_of_vertex (v := v)
      simp only [vertexChunk, List.mem_append]
      exact Or.inl (Or.inr
        (List.mem_map.mpr ⟨positive, D.mem_positiveLocalList positive, rfl⟩))
    · apply D.mem_itemList_of_vertex (v := v)
      simp [vertexChunk]
    · rcases job with ⟨⟨⟨⟨e, s⟩, hv⟩, j⟩, r⟩
      cases hv
      apply D.mem_itemList_of_job (e := e) (j := j) (s := s)
      simp [jobChunk, listedJobCopy]
    · rcases job with ⟨⟨⟨⟨e, s⟩, hv⟩, j⟩, r⟩
      cases hv
      apply D.mem_itemList_of_job (e := e) (j := j) (s := s)
      simp [jobChunk, listedJobCopy]
  | flag =>
    simp only [itemList, List.mem_append]
    exact Or.inr (D.mem_flagItems i)

open scoped Classical in
theorem itemList_toFinset : D.itemList.toFinset = Finset.univ := by
  classical
  ext i
  simp [D.mem_itemList i]

theorem itemList_nodup (hk : D.k ≤ D.graph.n) : D.itemList.Nodup := by
  classical
  have hcard : D.itemList.toFinset.card = D.itemList.length := by
    rw [D.itemList_toFinset, Finset.card_univ, D.card_item hk, D.itemList_length hk]
  exact (Multiset.toFinset_card_eq_card_iff_nodup
    (m := (D.itemList : Multiset D.Item))).mp hcard

def itemListEquiv (hk : D.k ≤ D.graph.n) : Fin D.itemList.length ≃ D.Item := by
  classical
  exact List.Nodup.getEquivOfForallMemList D.itemList (D.itemList_nodup hk) D.mem_itemList

@[simp] theorem itemListEquiv_apply (hk : D.k ≤ D.graph.n)
    (i : Fin D.itemList.length) : D.itemListEquiv hk i = D.itemList.get i := rfl

end BinPackingGap.InventoryData

end

end OAI
