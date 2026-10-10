import OAI.Computability.BinPacking.Inventory.PackingConstantPool

namespace OAI

noncomputable section

namespace BinPackingGap.GraphPackingStockStreams

open PackingConstantPool PackingInventoryDescriptors PackingDescriptorExpression

theorem repeatRecords_rawRecord (pair : Nat × Nat) (n : Nat) :
    repeatRecords (rawRecord pair) n = rawRecords (List.replicate n pair) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [repeatRecords, List.replicate_succ, rawRecords, List.flatMap_cons] using
        congrArg (fun word => rawRecord pair ++ word) ih

theorem singleton_chunk_records (D : InventoryData) (label : Option D.Vertex)
    (edge rep : Nat) (descriptor : ItemDescriptor D) :
    PackingChunkMachine.records (numerator D) PackingItemExpression.denominator
      (fun _ => values D label edge rep) [descriptor] =
      rawRecord (rawOfDescriptor D label edge rep descriptor) := by
  simp only [PackingChunkMachine.records_cons, PackingChunkMachine.records_nil,
    List.append_nil, record_eq]

theorem globalPoolStream_eq_replicate (D : InventoryData) (species : GlobalSpecies D.graph) :
    globalPoolStream D species =
      List.replicate (D.globalStock species)
        (rawOfDescriptor D none (globalEdgeIndex D species) 0 (globalDescriptor D species)) := by
  simp only [globalPoolStream, List.map_const', List.length_finRange]

theorem flagPoolStream_eq_replicate (D : InventoryData) (species : FlagSpecies) :
    flagPoolStream D species =
      List.replicate (D.flagStock species)
        (rawOfDescriptor D none 0 0 (flagDescriptor D species)) := by
  simp only [flagPoolStream, List.map_const', List.length_finRange]

theorem globalPool_records (D : InventoryData) (species : GlobalSpecies D.graph) :
    repeatRecords
      (PackingItemBlockMachine.record (numerator D (globalDescriptor D species))
        PackingItemExpression.denominator (values D none (globalEdgeIndex D species) 0))
      (D.globalStock species) = rawRecords (globalPoolStream D species) := by
  rw [record_eq, globalPoolStream_eq_replicate, repeatRecords_rawRecord]

theorem flagPool_records (D : InventoryData) (species : FlagSpecies) :
    repeatRecords
      (PackingItemBlockMachine.record (numerator D (flagDescriptor D species))
        PackingItemExpression.denominator (values D none 0 0))
      (D.flagStock species) = rawRecords (flagPoolStream D species) := by
  rw [record_eq, flagPoolStream_eq_replicate, repeatRecords_rawRecord]

theorem globalPool_chunk_records (D : InventoryData) (species : GlobalSpecies D.graph) :
    repeatRecords
      (PackingChunkMachine.records (numerator D) PackingItemExpression.denominator
        (fun _ => values D none (globalEdgeIndex D species) 0) [globalDescriptor D species])
      (D.globalStock species) = rawRecords (globalPoolStream D species) := by
  rw [singleton_chunk_records, globalPoolStream_eq_replicate, repeatRecords_rawRecord]

theorem flagPool_chunk_records (D : InventoryData) (species : FlagSpecies) :
    repeatRecords
      (PackingChunkMachine.records (numerator D) PackingItemExpression.denominator
        (fun _ => values D none 0 0) [flagDescriptor D species])
      (D.flagStock species) = rawRecords (flagPoolStream D species) := by
  rw [singleton_chunk_records, flagPoolStream_eq_replicate, repeatRecords_rawRecord]

end BinPackingGap.GraphPackingStockStreams

end

end OAI
