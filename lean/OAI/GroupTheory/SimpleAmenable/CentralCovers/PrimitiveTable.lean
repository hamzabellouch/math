import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrimitiveWords
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.Sectors

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ActualPrimitiveTable

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {ι : Type*} [Finite ι]

theorem subtypeAlternatingHom_injective {X : Type*} [Fintype X] [DecidableEq X]
    (I : Finset X) : Function.Injective (subtypeAlternatingHom I) := by
  intro s t h
  apply Subtype.ext
  exact Equiv.Perm.ofSubtype_injective (congrArg Subtype.val h)

noncomputable def tableAlphabetHom (I : Finset (Fin (m+1))) {Ω : Type*} :
    (Ω → alternatingGroup I) →* (Ω → alternatingGroup (Fin (m+1))) where
  toFun s ω := subtypeAlternatingHom I (s ω)
  map_one' := by funext ω; exact map_one _
  map_mul' s t := by funext ω; exact map_mul _ _ _

theorem tableAlphabetHom_injective (I : Finset (Fin (m+1))) {Ω : Type*} :
    Function.Injective (tableAlphabetHom (Ω := Ω) I) := by
  intro s t h
  funext ω
  exact subtypeAlternatingHom_injective I (congrFun h ω)

noncomputable def actualAlphabetTableHom (I : Finset (Fin (m+1)))
    (U : ι → polygonAlgebra a) :
    (Set.range (polygonAssignment U) → alternatingGroup I) →* polygonAlternatingGroup a (m+1) :=
  (actualPolygonTableHom U).comp (tableAlphabetHom I)

theorem actualAlphabetTableHom_injective (I : Finset (Fin (m+1)))
    (U : ι → polygonAlgebra a) : Function.Injective (actualAlphabetTableHom I U) :=
  (actualPolygonTableHom_injective U).comp (tableAlphabetHom_injective I)

noncomputable def actualTestMask (U : ι → polygonAlgebra a) (i : ι) :
    Set (Set.range (polygonAssignment U)) := {ω | ω.val i = true}

omit [Finite ι] in
theorem actualTestMask_separates (U : ι → polygonAlgebra a)
    (ω ν : Set.range (polygonAssignment U))
    (h : ∀ i, ω ∈ actualTestMask U i ↔ ν ∈ actualTestMask U i) : ω = ν := by
  apply Subtype.ext
  funext i
  apply Bool.eq_iff_iff.mpr
  exact h i

theorem tableAlphabetHom_mask (I : Finset (Fin (m+1))) {Ω : Type*}
    (V : Set Ω) (s : alternatingGroup I) :
    tableAlphabetHom I (sectorMask V s) = sectorMask V (subtypeAlternatingHom I s) := by
  classical
  funext ω
  by_cases h : ω ∈ V <;> simp [tableAlphabetHom,sectorMask,h]

theorem actualPolygonTableHom_whole (U : ι → polygonAlgebra a)
    (s : alternatingGroup (Fin (m+1))) :
    actualPolygonTableHom U (sectorMask Set.univ s) =
      conditionalAlternatingHom (wholePolygon a) s := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro p
  rw [actualPolygonTableHom_apply]
  simp only [sectorMask_of_mem Set.univ s _ (Set.mem_univ _)]
  change (s.val p.1,p.2) = conditionalPerm (wholePolygon a) s.val p
  rw [conditionalPerm_apply]
  simp only [wholePolygon,Set.mem_univ,ite_true]

theorem actualAlphabetTableHom_masks (I : Finset (Fin (m+1)))
    (U : ι → polygonAlgebra a) (i : Option ι) :
    (actualAlphabetTableHom I U).comp (maskFamily (actualTestMask U) i) =
      (conditionalAlternatingHom (match i with
        | none => wholePolygon a
        | some j => U j)).comp (subtypeAlternatingHom I) := by
  apply MonoidHom.ext
  intro s
  cases i with
  | none =>
    change actualPolygonTableHom U (tableAlphabetHom I (sectorMask Set.univ s)) = _
    rw [tableAlphabetHom_mask,actualPolygonTableHom_whole]
    rfl
  | some j =>
    change actualPolygonTableHom U (tableAlphabetHom I (sectorMask (actualTestMask U j) s)) = _
    rw [tableAlphabetHom_mask]
    exact actualPolygonTableHom_input U j (subtypeAlternatingHom I s)

namespace InitialCoverSystem

variable (B : InitialCoverSystem a r m hm M)

noncomputable def primitiveTests (P : ι → Fin 5 × (CutRing × CutRing)) :
    ι → polygonAlgebra a := fun i => primitiveFamilyTests (r := r) P (some i)

omit [Finite ι] in
theorem primitiveFamily_aligned (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing)) :
    (copyFamilyEval (B.primitiveFamily I b hb P)).range ≤
      sourceAlignedGroup a r m hm M B.t I := by
  rw [copyFamilyEval_range]
  apply iSup_le
  intro i s hs
  obtain ⟨t,rfl⟩ := hs
  cases i with
  | none => exact B.initialAlphabet_aligned I 0 t
  | some j => exact B.primitiveCopy_aligned I b hb (P j) t

noncomputable def primitiveTable (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) :
    ActualLawfulTable (coverMap M (alternatingGenerator a r m hm))
      (actualAlphabetTableHom I (primitiveTests (a := a) (r := r) P)) :=
  actualFamilyTable (actualTestMask (primitiveTests (a := a) (r := r) P)) (B.primitiveFamily I b hb P)
    (coverMap M (alternatingGenerator a r m hm)) (actualAlphabetTableHom I (primitiveTests (a := a) (r := r) P))
    (actualAlphabetTableHom_injective I (primitiveTests (a := a) (r := r) P))
    (fun i => by
      rw [B.primitiveFamily_projection,actualAlphabetTableHom_masks]
      cases i <;> rfl)
    (actualTestMask_separates (primitiveTests (a := a) (r := r) P)) h

theorem primitiveTable_sector_aligned (I : Finset (Fin (m+1)))
    [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P)
    (V : Set (Set.range (polygonAssignment (primitiveTests (a := a) (r := r) P))))
    (s : UniversalExtension (alternatingGroup I)) :
    (B.primitiveTable I b hb P h).sector V s ∈ sourceAlignedGroup a r m hm M B.t I :=
  B.primitiveFamily_aligned I b hb P ((B.primitiveTable I b hb P h).sector_mem V s)

end InitialCoverSystem
end ActualPrimitiveTable

end SimpleAmenable
end
end

end OAI
