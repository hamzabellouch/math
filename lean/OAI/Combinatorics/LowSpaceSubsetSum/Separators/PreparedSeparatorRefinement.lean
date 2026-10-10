import OAI.Combinatorics.LowSpaceSubsetSum.Separators.StoredSeparatorCheck

namespace OAI

/-! # Four prepared stored blocks refine the original encoded checker -/

namespace LowSpaceSubsetSum.PreparedSeparatorRefinement

open StoredSeparatorCheck

variable {n g : ℕ}

private theorem source_ext {α β : Type*} (a b : SeparatorBlocks.Block α β)
    (hs : a.size = b.size) (hl : a.left = b.left) (hr : a.right = b.right) : a = b := by
  cases a
  cases b
  simp_all

private theorem lookup_congr (row : Vector (Fin n) g) (x : StoredEntry n)
    (a b : Array (Array ℕ)) (ha : a.size = 2 ^ g) (hb : b.size = 2 ^ g)
    (h : a = b) :
    (StoredSeparatorQueries.lookup row x a ha).1 =
      (StoredSeparatorQueries.lookup row x b hb).1 := by
  subst b
  rfl

private theorem left_lookup (row : Vector (Fin n) g) (x : StoredEntry n)
    (family : Array (Fin (2 ^ g)))
    (hs : (StoredIncidenceBuild.tables family).1.1.size = 2 ^ g) :
    (StoredSeparatorQueries.lookup row x (StoredIncidenceBuild.tables family).1.1 hs).1 =
      SeparatorIncidenceTable.table (family.map SeparatorStoredMasks.decode)
        (fun D S => decide (D ⊆ S)) (StoredSeparatorQueries.localMask row x) := by
  have ht := congrArg Prod.fst (StoredIncidenceBuild.tables_value family)
  exact (lookup_congr row x _ _ hs (SeparatorStoredMasks.containsStore_size _) ht).trans
    (StoredSeparatorQueries.contains_value row x _)

private theorem right_lookup (row : Vector (Fin n) g) (x : StoredEntry n)
    (family : Array (Fin (2 ^ g)))
    (hs : (StoredIncidenceBuild.tables family).1.2.size = 2 ^ g) :
    (StoredSeparatorQueries.lookup row x (StoredIncidenceBuild.tables family).1.2 hs).1 =
      SeparatorIncidenceTable.table (family.map SeparatorStoredMasks.decode)
        (fun D S => decide (Disjoint D S)) (StoredSeparatorQueries.localMask row x) := by
  have ht := congrArg Prod.snd (StoredIncidenceBuild.tables_value family)
  exact (lookup_congr row x _ _ hs (SeparatorStoredMasks.avoidsStore_size _) ht).trans
    (StoredSeparatorQueries.avoids_value row x _)

def erase (C : TopCoordinates n g) (x : StoredEntry n) : SeparatorCheck.Record g :=
  C.encodeEntry x.semantic

theorem prepareBlock_source (C : TopCoordinates n g) (i : Fin 4)
    (row : Vector (Fin n) g) (hrow : ∀ j, row[j] = C.index (i, j))
    (family : Array (Fin (2 ^ g))) (depth steps : ℕ)
    (hd : depth = Nat.clog 2 family.size) (hs : family.size < 2 ^ steps) :
    (prepareBlock row family depth steps hd hs).1.source =
      SeparatorExecutionMap.block (erase C) (erase C)
        (SeparatorBlocks.ofFamily (family.map SeparatorStoredMasks.decode)
          (fun x => SeparatorCheck.localMask i x.mask)
          (fun x => SeparatorCheck.localMask i x.mask)) := by
  apply source_ext
  · simp only [prepareBlock, Block.source, SeparatorExecutionMap.block,
      SeparatorBlocks.ofFamily, Array.size_map]
  · funext x
    dsimp only [prepareBlock, Block.source, Block.left, SeparatorExecutionMap.block,
      Function.comp_apply, SeparatorBlocks.ofFamily]
    rw [left_lookup, SeparatorStoredMasks.containsList_eq,
      StoredSeparatorQueries.localMask_coordinates C i row hrow x]
    rfl
  · funext x
    dsimp only [prepareBlock, Block.source, Block.right, SeparatorExecutionMap.block,
      Function.comp_apply, SeparatorBlocks.ofFamily]
    rw [right_lookup, SeparatorStoredMasks.avoidsList_eq,
      StoredSeparatorQueries.localMask_coordinates C i row hrow x]
    rfl

theorem prepareFour_source (C : TopCoordinates n g)
    (rows : Fin 4 → Vector (Fin n) g) (hrows : ∀ i j, (rows i)[j] = C.index (i, j))
    (families : Fin 4 → Array (Fin (2 ^ g))) (depths steps : Fin 4 → ℕ)
    (hd : ∀ i, depths i = Nat.clog 2 (families i).size)
    (hs : ∀ i, (families i).size < 2 ^ steps i) :
    ((prepareFour rows families depths steps hd hs).1.map Block.source) =
      (SeparatorCheck.blocks (fun i => (families i).map SeparatorStoredMasks.decode)).map
        (SeparatorExecutionMap.block (erase C) (erase C)) := by
  rw [prepareFour_value]
  simp only [List.map_ofFn, SeparatorCheck.blocks]
  congr 1
  funext i
  exact prepareBlock_source C i (rows i) (hrows i) (families i) (depths i) (steps i) (hd i) (hs i)

theorem source_result (C : TopCoordinates n g)
    (rows : Fin 4 → Vector (Fin n) g) (hrows : ∀ i j, (rows i)[j] = C.index (i, j))
    (families : Fin 4 → Array (Fin (2 ^ g))) (depths steps : Fin 4 → ℕ)
    (hd : ∀ i, depths i = Nat.clog 2 (families i).size)
    (hs : ∀ i, (families i).size < 2 ^ steps i)
    (target : ℤ) (xs ys : List (StoredEntry n)) :
    SeparatorBlocks.check n StoredEntry.value StoredEntry.value target
      ((prepareFour rows families depths steps hd hs).1.map Block.source) xs ys =
      C.check (fun i => (families i).map SeparatorStoredMasks.decode) target
        (xs.map StoredEntry.semantic) (ys.map StoredEntry.semantic) := by
  rw [prepareFour_source C rows hrows families depths steps hd hs]
  have h := SeparatorExecutionMap.blocks_map (erase C) (erase C) Entry.value Entry.value n target
    (SeparatorCheck.blocks (fun i => (families i).map SeparatorStoredMasks.decode)) xs ys
  have hv : Entry.value ∘ erase C = StoredEntry.value := rfl
  rw [hv] at h
  change _ = SeparatorBlocks.check n Entry.value Entry.value target _
    ((xs.map StoredEntry.semantic).map C.encodeEntry)
    ((ys.map StoredEntry.semantic).map C.encodeEntry)
  rw [List.map_map, List.map_map]
  exact h.symm

theorem acceptance (C : TopCoordinates n g)
    (rows : Fin 4 → Vector (Fin n) g) (hrows : ∀ i j, (rows i)[j] = C.index (i, j))
    (families : Fin 4 → Array (Fin (2 ^ g))) (depths steps : Fin 4 → ℕ)
    (hd : ∀ i, depths i = Nat.clog 2 (families i).size)
    (hs : ∀ i, (families i).size < 2 ^ steps i)
    (capacity : ℕ) (hcap : capacity = 2 ^ n) (target : ℤ)
    (xs ys : List (StoredEntry n)) :
    (run capacity target (prepareFour rows families depths steps hd hs).1 xs ys).1 =
      (C.check (fun i => (families i).map SeparatorStoredMasks.decode) target
        (xs.map StoredEntry.semantic) (ys.map StoredEntry.semantic)).accepted := by
  rw [run_value capacity hcap,
    source_result C rows hrows families depths steps hd hs]

end LowSpaceSubsetSum.PreparedSeparatorRefinement

end OAI
