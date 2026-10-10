import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ConcurrentGeometry
import OAI.GroupTheory.SimpleAmenable.CentralCovers.IndividualGridSplits
import OAI.GroupTheory.SimpleAmenable.CentralCovers.GridFormalPatching
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ConcurrentCellSlopeAction
import OAI.GroupTheory.SimpleAmenable.CentralCovers.CrossingCellActions
import OAI.GroupTheory.SimpleAmenable.CentralCovers.ConstantCellTemplates

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section GridPrimitiveInputs
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι κ : Type*} [Finite κ]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_small_input (hlarge : 15 < m+1)
    (P : κ → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (R : ι → Fin 5 × (CutRing × CutRing)) (k : κ) (i : ι) (he : P k=R i)
    (I : FiveAlphabet (Fin (m+1))) :
    (B.fullGeometricSector hlarge P h (primitiveTests (a := a) (r := r) R i)).comp
      (universalMap (subtypeAlternatingHom I.val)) =
      (B.smallPrimitiveInputs hlarge R I (some i)).comp (universalProjection (alternatingGroup I.val)) := by
  let b := smallAlphabetBalance hlarge I.val (by rw [I.property.2]; omega)
  have hb := smallAlphabetBalance_notMem hlarge I.val (by rw [I.property.2]; omega)
  have hR : primitiveTests (a := a) (r := r) R i=primitiveTests (a := a) (r := r) P k := by
    simp only [primitiveTests,primitiveFamilyTests,he]
  rw [hR,B.fullGeometricSector_inclusion hlarge P h I.val (by rw [I.property.2]) b hb
    (h I.val (by rw [I.property.2]; omega) b hb) _ (resolved_test _ k),B.geometricSector_input]
  change (B.primitiveCopy I.val b hb (P k)).comp _ = (B.primitiveCopy I.val b hb (R i)).comp _
  rw [he]

theorem fullGeometricSector_small_whole (hlarge : 15 < m+1)
    (P : κ → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (R : ι → Fin 5 × (CutRing × CutRing)) (I : FiveAlphabet (Fin (m+1))) :
    (B.fullGeometricSector hlarge P h (wholePolygon a)).comp
      (universalMap (subtypeAlternatingHom I.val)) =
      (B.smallPrimitiveInputs hlarge R I none).comp (universalProjection (alternatingGroup I.val)) := by
  rw [B.fullGeometricSector_whole]
  change (B.c.comp (universalProjection (alternatingGroup (Fin (m+1))))).comp _ =
    (B.initialAlphabet I.val 0).comp _
  rw [MonoidHom.comp_assoc,universalMap_spec,← MonoidHom.comp_assoc,B.initialAlphabet_zero]

end InitialCoverSystem
end GridPrimitiveInputs

section SlopeCoordinateFormalLaw
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (A : B.PatchAtlas)

include A in

theorem slope_coordinate_formal_law (hlarge : 25 ≤ m+1)
    (hr : 0<ordinary r ∧ ordinary r<1/2) (ha : 0<a)
    (d j : Fin 2) (v : CutRing × CutRing) :
    HasCentralLaw (smallFamilyModel (fun i : Fin 2 => {σ : Fin 2 → Bool | σ i=true}))
      (smallFamilyEval (B.smallPrimitiveInputs (by omega)
        ![(slopeTestIndex d,0),(coordinateTestIndex j,v)])).rangeRestrict := by
  classical
  let n := A.geometry.mesh
  let q := symmetricWindowStart r
  let κ := Sum (Fin 5) (Fin 2 × Fin (n-1))
  let R : Fin 2 → Fin 5 × (CutRing × CutRing) := ![(slopeTestIndex d,0),(coordinateTestIndex j,v)]
  let P : κ → Fin 5 × (CutRing × CutRing) := initialPatchPrimitives r n
  let Q : κ → Fin 5 × (CutRing × CutRing) :=
    Sum.elim (fun _ : Fin 5 => (coordinateTestIndex j,v)) (coordinateWindowPrimitives n q)
  let O : Option (Fin 2) → κ → Fin 5 × (CutRing × CutRing) :=
    fun i => if i=some 0 then P else Q
  have hP : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P := by
    intro I _ b hb
    have hz : translatedTemplate (initialPatchPrimitives r A.geometry.mesh) 0=P := by
      funext i
      exact Prod.ext rfl (zero_add _)
    simpa only [hz] using A.initial 0 I b hb
  have hQ : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb Q := by
    intro I _ b hb
    have hz : (fun i : κ =>
        (coordinateTestIndex (Sum.elim (fun _ : Fin 5 => j) Prod.fst i),
         Sum.elim (fun _ : Fin 5 => v) (fun z => (coordinateWindowPrimitives n q z).2) i))=Q := by
      funext i
      cases i <;> rfl
    rw [← hz]
    exact B.coordinateFamilyLaw_all A.rectangles.rectangles
      (Sum.elim (fun _ : Fin 5 => j) Prod.fst)
      (Sum.elim (fun _ : Fin 5 => v) (fun z => (coordinateWindowPrimitives n q z).2)) I b hb
  have h : ∀ i I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb (O i) := by
    intro i
    dsimp [O]
    split <;> assumption
  let U : Option (Fin 2) → polygonAlgebra a := fun i =>
    match i with
    | none => wholePolygon a
    | some i => primitiveTests (a := a) (r := r) R i
  let W := windowRectangle a n q
  have hn : 201 ≤ n := A.geometry.mesh_large
  have hcoord : ∀ i z, O i (Sum.inr z)=translatedTemplate (coordinateWindowPrimitives n q) 0 z := by
    intro i z
    dsimp [O]
    split <;> simp only [P,Q,initialPatchPrimitives,Sum.elim_inr,translatedTemplate,zero_add]
    rfl
  have hW : ∀ i cell, ResolvedBy (fun k => (primitiveTests (a := a) (r := r) (O i) k).val) (W cell).val := by
    intro i cell x y hh
    apply windowRectangle_resolved n (by omega) q cell x y
    intro z
    have hz := hh (Sum.inr z)
    simpa only [primitiveTests,primitiveFamilyTests,hcoord,translatedTemplate,zero_add] using hz
  have he : ∀ i cell, B.fullGeometricSector (by omega) (O i) (h i) (W cell)=
      B.windowSector (by omega) n (A.rectangles.rectangles n) q (W cell) := by
    intro i cell
    have hh := B.templateWindowSector_eq (by omega) n q 0 (A.rectangles.rectangles n)
      (O i) (h i) Sum.inr (hcoord i) (W cell) (windowRectangle_resolved n (by omega) q cell)
    simpa only [pointLabel_zero,zero_add,spatialTranslate_zero] using hh
  have hinput : ∀ i : Fin 2, ∃ k : κ, O (some i) k=R i := by
    intro i
    fin_cases i
    · exact ⟨Sum.inl (slopeTestIndex d), rfl⟩
    · exact ⟨Sum.inl 0, by simp [O,Q,R]⟩
  have hU : ∀ i, ResolvedBy (fun k => (primitiveTests (a := a) (r := r) (O i) k).val) (U i).val := by
    intro i
    cases i with
    | none => exact fun _ _ _ => Iff.rfl
    | some i =>
      obtain ⟨k,hk⟩ := hinput i
      intro x y hh
      have hx := hh k
      simpa only [U,primitiveTests,primitiveFamilyTests,hk] using hx
  refine B.grid_formal_patching_templates hlarge O h U W hU hW
    (fun i cell => (he i cell).trans (he none cell).symm)
    (windowRectangle_pairwise_disjoint n hn q) (windowRectangle_cover n hn q)
    (B.smallPrimitiveInputs (by omega) R) ?_ rfl ?_
  · intro I i
    cases i with
    | none => exact B.fullGeometricSector_small_whole (by omega) (O none) (h none) R I
    | some i =>
      obtain ⟨k,hk⟩ := hinput i
      exact B.fullGeometricSector_small_input (by omega) (O (some i)) (h (some i)) R k i hk I
  · intro cell
    have hclip := A.geometry.clipping
    have hb : ∀ k, q k≤endpointLabel (-r) ∧ endpointLabel (-r)<q k+n := by
      intro k
      have hh := (symmetricWindow_labels r k).1
      constructor
      · exact hh.1
      · dsimp [n,q] at *; omega
    have hu : ∀ k, q k≤endpointLabel r ∧ endpointLabel r<q k+n := by
      intro k
      have hh := (symmetricWindow_labels r k).2.2
      constructor
      · exact hh.1
      · dsimp [n,q] at *; omega
    refine A.slope_coordinate_cell_template (by omega) hr ha d j v
      (fun i => O (some i)) (fun i => h (some i))
      (Sum.inl (slopeTestIndex d)) (Sum.inl 0) rfl (by simp [O,Q])
      (B.gridInput (by omega) O h U) (B.gridPiece (by omega) O h U W cell) ?_ q cell hb hu
      (fun i => hW (some i) cell) (fun i => he (some i) cell)
      (B.gridPiece_supported (by omega) O h U W hU hW cell) ?_
    · intro i
      fin_cases i <;> simp [gridInput,U,R,primitiveTests,primitiveFamilyTests,
        initialTest_slope,initialTest_coordinate,spatialTranslate_zero]
    · intro i
      rw [← he i cell]
      exact B.gridPiece_control (by omega) O h U W cell i

end InitialCoverSystem.PatchAtlas
end SlopeCoordinateFormalLaw

end SimpleAmenable
end
end

end OAI
