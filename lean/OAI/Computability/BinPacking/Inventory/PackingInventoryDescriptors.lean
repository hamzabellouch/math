import OAI.Computability.BinPacking.Machines.GraphPackingOutput

namespace OAI

noncomputable section

namespace BinPackingGap.PackingInventoryDescriptors

open PackingCoordinateExpression NaturalPackingNumerator IntegerPackingArithmetic

variable (D : InventoryData)

abbrev ItemDescriptor := Subclass × Descriptor D.plus D.minus D.L

def itemDescriptor (i : D.Item) : ItemDescriptor D :=
  (D.itemSubclass i, coordinateDescriptor D i)

def positiveDescriptor (r : D.PositiveLocal) : ItemDescriptor D :=
  (.dm, .localDepth ⟨r.1.val, Nat.lt_succ_of_le (Finset.mem_Icc.mp r.1.property).2⟩)

def vertexDescriptors : List (ItemDescriptor D) :=
  (D.treeRowList.map fun r => (D.treeSubclass r, .treeRow (treeDescriptor D r))) ++
  (D.treeRowList.map fun r => (.z, .treeAnchor (treeDescriptor D r))) ++
  (D.positiveLocalList.map (positiveDescriptor D)) ++
  ((List.finRange (D.t - D.P)).map fun _ => (.dm, .zero))

def jobDescriptors : List (ItemDescriptor D) :=
  ((List.finRange D.d).map fun _ => (.s, .jobRow true)) ++
  ((List.finRange D.d).map fun _ => (.s, .jobRow false)) ++
  ((List.finRange D.d).map fun _ => (.z, .jobAnchor)) ++
  ((List.finRange D.d).map fun _ => (.y, .jobKey)) ++
  ((List.finRange D.d).map fun _ => (.dm, .zero)) ++
  ((List.finRange D.d).map fun _ => (.dg, .zero))

theorem vertexChunk_descriptors (v : D.Vertex) :
    (D.vertexChunk v).map (itemDescriptor D) = vertexDescriptors D := by
  simp [InventoryData.vertexChunk, vertexDescriptors, itemDescriptor,
    List.map_append, List.map_map, Function.comp_def, InventoryData.itemSubclass,
    InventoryData.rowSubclass, coordinateDescriptor, positiveDescriptor]

theorem jobChunk_descriptors (e : D.Edge) (j : Fin D.R) (s : Fin 2) :
    (D.jobChunk e j s).map (itemDescriptor D) = jobDescriptors D := by
  simp [InventoryData.jobChunk, jobDescriptors, itemDescriptor, List.map_append,
    List.map_map, Function.comp_def, InventoryData.itemSubclass, InventoryData.rowSubclass,
    coordinateDescriptor]

theorem vertexDescriptors_length (v : D.Vertex) :
    (vertexDescriptors D).length = 3 * D.t := by
  rw [← vertexChunk_descriptors D v, List.length_map, D.vertexChunk_length]

theorem jobDescriptors_length : (jobDescriptors D).length = 6 * D.d := by
  simp [jobDescriptors]
  omega

def rawOfDescriptor (label : Option D.Vertex) (edge rep : Nat)
    (descriptor : ItemDescriptor D) : Nat × Nat :=
  ((numeratorParts D.coordinateDenominator descriptor.1 label
      ((expression D.geometryBound descriptor.2).eval (registers D edge rep))).toNat,
    sizeDenominator D.graph.n D.coordinateDenominator)

theorem rawOfDescriptor_item (i : D.Item) :
    rawOfDescriptor D (D.itemLabel i) (edgeIndex D i) (repetitionOne D i)
      (itemDescriptor D i) = D.itemRawPair i := by
  unfold rawOfDescriptor itemDescriptor
  rw [← coordinateValues, eval_coordinateDescriptor]
  exact naturalRawItem_eq D i

theorem vertexChunk_raw (v : D.Vertex) :
    (D.vertexChunk v).map D.itemRawPair =
      (vertexDescriptors D).map (rawOfDescriptor D (some v) 0 0) := by
  rw [← vertexChunk_descriptors D v, List.map_map]
  apply List.map_congr_left
  intro i hi
  have hraw := rawOfDescriptor_item D i
  have hlabel : D.itemLabel i = some v := by
    simp only [InventoryData.vertexChunk, List.mem_append, List.mem_map, or_assoc] at hi
    rcases hi with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ <;> rfl
  have hedge : edgeIndex D i = 0 := by
    simp only [InventoryData.vertexChunk, List.mem_append, List.mem_map, or_assoc] at hi
    rcases hi with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ <;> rfl
  have hrep : repetitionOne D i = 0 := by
    simp only [InventoryData.vertexChunk, List.mem_append, List.mem_map, or_assoc] at hi
    rcases hi with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ <;> rfl
  simpa only [Function.comp_apply, hlabel, hedge, hrep] using hraw.symm

theorem jobChunk_raw (e : D.Edge) (j : Fin D.R) (s : Fin 2) :
    (D.jobChunk e j s).map D.itemRawPair =
      (jobDescriptors D).map
        (rawOfDescriptor D (some (D.graph.endpoint e s)) e.val (j.val + 1)) := by
  rw [← jobChunk_descriptors D e j s, List.map_map]
  apply List.map_congr_left
  intro i hi
  simp only [InventoryData.jobChunk, List.mem_append, List.mem_map, or_assoc] at hi
  rcases hi with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ |
    ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
  all_goals
    rw [← naturalRawItem_eq]
    simp [naturalRawItem, inventoryNumerator, inventoryParts,
      rawOfDescriptor, itemDescriptor, InventoryData.itemSubclass,
      InventoryData.rowSubclass, InventoryData.itemLabel, InventoryData.jobPosition,
      InventoryData.listedJobCopy, coordinateDescriptor, expression, coordinateParts,
      rowParts, rowBaselineParts, anchorParts, deadlineParts, localParts,
      InventoryData.rowShort, Parts.eval, Parts.ofExpr, Parts.sub, Parts.negate,
      registers, baselineExpr, betaExpr, baselineParts, betaParts, NatExpressionCompiler.eval,
      NatDifference.ofNat, NatDifference.sub, NatDifference.negate]

def globalDescriptor : GlobalSpecies D.graph → ItemDescriptor D
  | .up one => (.up, .globalUnit one)
  | .um one => (.um, .globalUnit one)
  | .edge _ permit => (.w, .globalEdge permit)

def globalEdgeIndex : GlobalSpecies D.graph → Nat
  | .edge e _ => e.val
  | _ => 0

def flagDescriptor : FlagSpecies → ItemDescriptor D
  | .tree => (.ft, .zero)
  | .main => (.fm, .zero)
  | .edge => (.fg, .zero)

theorem globalPool_raw (species : GlobalSpecies D.graph) :
    (D.globalPool species).map D.itemRawPair =
      (List.finRange (D.globalStock species)).map
        (fun _ => rawOfDescriptor D none (globalEdgeIndex D species) 0
          (globalDescriptor D species)) := by
  unfold InventoryData.globalPool
  rw [List.map_map]
  apply List.map_congr_left
  intro j _
  have h := rawOfDescriptor_item D ⟨.«global», ⟨species, j⟩⟩
  cases species <;> simpa only [itemDescriptor, InventoryData.itemLabel,
    InventoryData.itemSubclass, coordinateDescriptor, edgeIndex, repetitionOne,
    globalDescriptor, globalEdgeIndex, Function.comp_apply] using h.symm

theorem flagPool_raw (species : FlagSpecies) :
    (D.flagPool species).map D.itemRawPair =
      (List.finRange (D.flagStock species)).map
        (fun _ => rawOfDescriptor D none 0 0 (flagDescriptor D species)) := by
  unfold InventoryData.flagPool
  rw [List.map_map]
  apply List.map_congr_left
  intro j _
  have h := rawOfDescriptor_item D ⟨.flag, ⟨species, j⟩⟩
  cases species <;> simpa only [itemDescriptor, InventoryData.itemLabel,
    InventoryData.itemSubclass, coordinateDescriptor, edgeIndex, repetitionOne,
    flagDescriptor, Function.comp_apply] using h.symm

def vertexStream : RawInstance :=
  (List.finRange D.graph.n).flatMap fun v =>
    (vertexDescriptors D).map (rawOfDescriptor D (some v) 0 0)

def jobStream : RawInstance :=
  (List.finRange D.graph.edges.length).flatMap fun e =>
    (List.finRange D.R).flatMap fun j =>
      (List.finRange 2).flatMap fun s =>
        (jobDescriptors D).map
          (rawOfDescriptor D (some (D.graph.endpoint e s)) e.val (j.val + 1))

def globalPoolStream (species : GlobalSpecies D.graph) : RawInstance :=
  (List.finRange (D.globalStock species)).map
    (fun _ => rawOfDescriptor D none (globalEdgeIndex D species) 0
      (globalDescriptor D species))

def globalStream : RawInstance :=
  globalPoolStream D (.up true) ++ globalPoolStream D (.up false) ++
    globalPoolStream D (.um true) ++ globalPoolStream D (.um false) ++
    (List.finRange D.graph.edges.length).flatMap fun e =>
      globalPoolStream D (.edge e true) ++ globalPoolStream D (.edge e false)

def flagPoolStream (species : FlagSpecies) : RawInstance :=
  (List.finRange (D.flagStock species)).map
    (fun _ => rawOfDescriptor D none 0 0 (flagDescriptor D species))

def flagStream : RawInstance :=
  flagPoolStream D .tree ++ flagPoolStream D .main ++ flagPoolStream D .edge

def recipeStream : RawInstance :=
  vertexStream D ++ jobStream D ++ globalStream D ++ flagStream D

theorem recipeStream_eq_rawItemList : recipeStream D = D.rawItemList := by
  simp only [InventoryData.rawItemList, InventoryData.itemList, List.map_append,
    InventoryData.vertexItems, InventoryData.jobItems, InventoryData.globalItems,
    InventoryData.flagItems, List.map_flatMap, vertexChunk_raw, jobChunk_raw,
    globalPool_raw, flagPool_raw, recipeStream, vertexStream, jobStream, globalStream,
    flagStream, globalPoolStream, flagPoolStream]

end BinPackingGap.PackingInventoryDescriptors

end

end OAI
