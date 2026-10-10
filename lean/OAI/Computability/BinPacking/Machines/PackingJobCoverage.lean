import OAI.Computability.BinPacking.Inventory.PackingExclusions
import OAI.Computability.BinPacking.Trees.InventoryRowGeometry

namespace OAI

noncomputable section

namespace BinPackingGap
namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

def shortMainAt (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (r : D.Position) : Finset (p.TableBin (subclass e)) := by
  classical
  exact (Coverage.mainTuplesAt p (subclass e) (label e) v).filter fun t =>
    tupleBaseline p e t = Geometry.baseline D.graph.edges.length D.R r ∧
      tupleShort p e t = true

theorem main_unit_species (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v)
    (hu : D.globalUnit (globalCopy p e t) = true) :
    (globalCopy p e t).1 = .up true ∨ (globalCopy p e t).1 = .um true := by
  rcases hcopy : globalCopy p e t with ⟨s, i⟩
  rw [hcopy] at hu
  change s = .up true ∨ s = .um true
  cases s with
  | up one =>
      change one = true at hu
      exact Or.inl (congrArg GlobalSpecies.up hu)
  | um one =>
      change one = true at hu
      exact Or.inr (congrArg GlobalSpecies.um hu)
  | edge edge permit =>
      have hglobal := roleCopy_subclass p e t .«global»
      change D.itemSubclass ⟨.«global», globalCopy p e t⟩ = _ at hglobal
      rw [hcopy] at hglobal
      have hmain := ((Coverage.mem_mainTuplesAt p (subclass e) (label e) v t).mp ht).2.2
      exfalso
      apply hmain
      cases hpattern : p.tablePattern (subclass e) t <;>
        rw [hpattern] at hglobal <;> cases hglobal

theorem row_minus_of_global_um (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (hu : (globalCopy p e t).1 = .um true) :
    D.rowSubclass (rowCopy p e t).2 = .tm := by
  have hg := roleCopy_subclass p e t .«global»
  have hx := roleCopy_subclass p e t .x
  have hclass : D.itemSubclass ⟨.«global», globalCopy p e t⟩ = .um := by
    rcases hcopy : globalCopy p e t with ⟨s, i⟩
    have hs : s = .um true := by simpa only [hcopy] using hu
    subst s
    rfl
  have hpat : p.tablePattern (subclass e) t = .minusTree := by
    rw [hclass] at hg
    cases hp : p.tablePattern (subclass e) t <;> simp_all [patternSubclass]
  rw [hpat] at hx
  change D.itemSubclass ⟨.x, rowCopy p e t⟩ = .tm at hx
  rcases hc : rowCopy p e t with ⟨w, r⟩
  rw [hc] at hx
  exact hx

theorem job_covering_global_not_um (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (r : D.Position) (t : p.TableBin (subclass e))
    (ht : t ∈ tupleCovering p e v
      (Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L r)) :
    (globalCopy p e t).1 ≠ .um true := by
  intro hu
  have hrow := row_minus_of_global_um p e t hu
  apply D.minus_row_not_cover_jobInterior (rowCopy p e t).2 (globalCopy p e t)
    (localCopy p e t).2 hrow r
  exact ((mem_tupleCovering p e v _ t).mp ht).2

theorem zero_resources_job_cover (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (r : D.Position) (t : p.TableBin (subclass e))
    (ht : t ∈ tupleCovering p e v
      (Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L r))
    (hg : tupleGlobalLength p e t = 0) (hl : tupleLocalLength p e t = 0) :
    tupleBaseline p e t = Geometry.baseline D.graph.edges.length D.R r ∧
      tupleShort p e t = true := by
  have hmem := ((mem_tupleCovering p e v _ t).mp ht).2
  have hshort : tupleShort p e t = true := by
    cases hs : tupleShort p e t with
    | false =>
        have hfinish : tupleFinish p e t = tupleBaseline p e t := by
          simp [tupleFinish, hs, hg, hl]
        rw [hfinish] at hmem
        exact (not_lt_of_ge hmem.1 hmem.2).elim
    | true => rfl
  obtain ⟨j, hj, _, hinter⟩ := D.row_zero_resources_job (rowCopy p e t).2 hshort
  have hmem' : Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L r ∈
      completionInterval (D.rowBaseline (rowCopy p e t).2)
        (D.rowShort (rowCopy p e t).2) 0 0
        (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L) := by
    change completion _ _ 0 0 _ ≤ _ ∧ _ < _
    simpa only [tupleFinish, hg, hl, tupleBaseline, tupleShort] using hmem
  rw [hinter] at hmem'
  have hpos : D.jobPosition j = r :=
    (Geometry.jobInterior_mem_jobTestInterval_iff D.geometryBound D.L).mp hmem'
  refine ⟨?_, hshort⟩
  simp only [tupleBaseline, hj, InventoryData.rowBaseline, hpos]

theorem nonexcluded_covering_subset (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (r : D.Position) (hr : r ∉ excludedAt p e v) :
    tupleCovering p e v (Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L r) ⊆
      fundedTuples p e (.up true) v ∪ shortMainAt p e v r := by
  classical
  intro t ht
  have hM := ((mem_tupleCovering p e v _ t).mp ht).1
  by_cases hu : D.globalUnit (globalCopy p e t) = true
  · have hspec := main_unit_species p e v t hM hu
    rcases hspec with hp | hm
    · exact Finset.mem_union_left _ ((mem_fundedTuples p e (.up true) v t).mpr
        ⟨hM, (selected_global_resource_iff p e t (.up true)).mpr hp⟩)
    · exact (job_covering_global_not_um p e v r t ht hm).elim
  · have hfalse : D.globalUnit (globalCopy p e t) = false := Bool.eq_false_of_not_eq_true hu
    have hnot := covering_not_selected_of_nonexcluded p e v r hr t ht
    have hnotpos : p.itemAtRole (subclass e) t .«local» ∉ positiveLocalResources e v := by
      intro hp
      exact hnot ((mem_zeroPositiveTuples p e v t).mpr ⟨hM, hfalse, hp⟩)
    have hlocal := tupleLocalLength_eq_zero_of_not_positive p e v t
      (Coverage.mainTuplesAt_subset_good p (subclass e) (label e) v hM) hnotpos
    have hz := zero_resources_job_cover p e v r t ht
      (tupleGlobalLength_eq_of_unit_false p e t hfalse) hlocal
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hM, hz⟩)

theorem nonexcluded_coverage_upper (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (r : D.Position) (hr : r ∉ excludedAt p e v) :
    (tupleCovering p e v
      (Geometry.jobInterior D.graph.edges.length D.R D.geometryBound D.L r)).card ≤
      xplus p e v + (shortMainAt p e v r).card := by
  calc
    _ ≤ (fundedTuples p e (.up true) v ∪ shortMainAt p e v r).card :=
      Finset.card_le_card (nonexcluded_covering_subset p e v r hr)
    _ ≤ _ := Finset.card_union_le _ _

end PackingCounts
end BinPackingGap

end

end OAI
