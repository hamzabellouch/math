import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.ConcurrentGeometry
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FormalPairSplits
import OAI.GroupTheory.SimpleAmenable.CentralCovers.GridFormalPatching
import OAI.GroupTheory.SimpleAmenable.CentralCovers.GridPrimitiveInputs
import OAI.GroupTheory.SimpleAmenable.Simplicial.FormalLawReindex
import OAI.GroupTheory.SimpleAmenable.RandomFields.FormalLawCovariance

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ActualFormalLaws
variable {a : ℕ} {α ι : Type*} [Fintype α] [DecidableEq α]

theorem smallActualModel_pullback (U : ι → polygonAlgebra a) :
    smallFamilyModel (α := α) (actualTestMask U)=
      (assignmentPullback (fun σ : Set.range (polygonAssignment U) => σ.val)).comp
        (smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true})) := by
  apply FreeGroup.ext_hom
  rintro ⟨I,i,s⟩
  ext σ
  simp only [MonoidHom.comp_apply,smallFamilyModel,smallFamilyEval_of]
  cases i <;> simp [maskFamily,sectorMask,assignmentPullback,actualTestMask]
  rfl

namespace InitialCoverSystem
variable {m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) [Finite ι]

theorem smallPrimitive_formal_of_actual (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card≤15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P) :
    HasCentralLaw (smallFamilyModel (fun i : ι => {σ : ι → Bool | σ i=true}))
      (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).rangeRestrict := by
  rw [hasCentralLaw_iff]
  intro w hw
  apply B.fullPrimitiveFamily_central hlarge P h
  change coverMap M (alternatingGenerator a r m hm)
    (smallFamilyEval (B.smallPrimitiveInputs hlarge P) w)=1
  have he := DFunLike.congr_fun (B.fullPrimitiveProjection hlarge P) w
  simp only [MonoidHom.comp_apply] at he
  rw [he,smallActualModel_pullback,MonoidHom.comp_apply,hw,map_one,map_one]

end InitialCoverSystem
end ActualFormalLaws

section CanonicalPrimitiveStars
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)
    {ι : Type*}

noncomputable def primitiveStar (hlarge : 15 < m+1) (p : Fin 5 × (CutRing × CutRing)) :
    TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.fullGeometricSector hlarge (translatedTemplate (initialPatchPrimitives r A.geometry.mesh) p.2)
    (fun I _ b hb => A.initial p.2 I b hb)
    (spatialTranslate p.2 (initialTest a r p.1))

noncomputable def starFamily (hlarge : 15 < m+1) (P : ι → Fin 5 × (CutRing × CutRing)) :
    Option ι → TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm)
  | none => B.c.comp (universalProjection (alternatingGroup (Fin (m+1))))
  | some i => A.primitiveStar hlarge (P i)

theorem starFamily_small (hlarge : 15 < m+1) (P : ι → Fin 5 × (CutRing × CutRing))
    (I : FiveAlphabet (Fin (m+1))) (i : Option ι) :
    (A.starFamily hlarge P i).comp (universalMap (subtypeAlternatingHom I.val))=
      (B.smallPrimitiveInputs hlarge P I i).comp (universalProjection (alternatingGroup I.val)) := by
  cases i with
  | none =>
    change (B.c.comp _).comp _=(B.initialAlphabet I.val 0).comp _
    rw [MonoidHom.comp_assoc,universalMap_spec,← MonoidHom.comp_assoc,B.initialAlphabet_zero]
  | some i =>
    apply B.fullGeometricSector_small_input hlarge _ _ P (Sum.inl (P i).1) i _ I
    simp [translatedTemplate,initialPatchPrimitives]

theorem starFamily_supported (hlarge : 15 < m+1) (P : ι → Fin 5 × (CutRing × CutRing))
    (i : Option ι) :
    SmallSupported (sourceAlignedGroup a r m hm M B.t) (A.starFamily hlarge P i) := by
  cases i with
  | none => exact B.constant_small_supported
  | some i =>
    apply B.fullGeometricSector_supported
    have he : spatialTranslate (P i).2 (initialTest a r (P i).1)=
        primitiveTests (a := a) (r := r)
          (translatedTemplate (initialPatchPrimitives r A.geometry.mesh) (P i).2) (Sum.inl (P i).1) := by
      simp [primitiveTests,primitiveFamilyTests,translatedTemplate,initialPatchPrimitives]
    rw [he]
    exact resolved_test _ _

end InitialCoverSystem.PatchAtlas
end CanonicalPrimitiveStars

section OneSlopeFormalTable
noncomputable def oneSlopeCoordinates {ι : Type*} (d : Fin 2) (u : CutRing × CutRing)
    (j : ι → Fin 2) (v : ι → CutRing × CutRing) : Option ι → Fin 5 × (CutRing × CutRing)
  | none => (slopeTestIndex d,u)
  | some i => (coordinateTestIndex (j i),v i)

namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)
    {ι : Type*}

omit [Group.IsPerfect (alternatingGroup (Fin (m+1)))] in
include A in
theorem primitive_self_formal_law (hlarge : 15 < m+1) (p : Fin 5 × (CutRing × CutRing)) :
    HasCentralLaw (smallFamilyModel (fun i : Bool => {σ : Bool → Bool | σ i=true}))
      (smallFamilyEval (B.smallPrimitiveInputs hlarge (fun _ : Bool => p))).rangeRestrict := by
  apply B.smallPrimitive_formal_of_actual
  intro I hI b hb
  have hh := PrimitiveFamilyLaw.reindex B I b hb
    (translatedTemplate (initialPatchPrimitives r A.geometry.mesh) p.2)
    (A.initial p.2 I b hb) (fun _ : Bool => Sum.inl p.1)
  have he : (translatedTemplate (initialPatchPrimitives r A.geometry.mesh) p.2) ∘
      (fun _ : Bool => Sum.inl p.1)=(fun _ : Bool => p) := by
    funext i
    simp [translatedTemplate,initialPatchPrimitives]
  rwa [he] at hh

include A in

theorem oneSlope_pairs_formal_law [Finite ι] (hlarge : 25 ≤ m+1)
    (hr : 0<ordinary r ∧ ordinary r<1/2) (ha : 0<a)
    (d : Fin 2) (u : CutRing × CutRing) (j : ι → Fin 2) (v : ι → CutRing × CutRing)
    (i k : Option ι) :
    HasCentralLaw (smallFamilyModel (fun b : Bool => {σ : Bool → Bool | σ b=true}))
      (smallFamilyEval (B.smallPrimitiveInputs (by omega)
        (primitivePair (oneSlopeCoordinates d u j v) i k))).rangeRestrict := by
  cases i with
  | none =>
    cases k with
    | none =>
      have he : primitivePair (oneSlopeCoordinates d u j v) none none=(fun _ : Bool => (slopeTestIndex d,u)) := by
        funext b; cases b <;> rfl
      rw [he]
      exact A.primitive_self_formal_law (by omega) (slopeTestIndex d,u)
    | some k =>
      have hh := B.smallPrimitive_formal_reindex (by omega) _
        (A.translated_slope_coordinate_formal_law hlarge hr ha d (j k) u (v k))
        (fun b : Bool => if b then (1 : Fin 2) else 0)
      have he : ![(slopeTestIndex d,u),(coordinateTestIndex (j k),v k)] ∘
          (fun b : Bool => if b then (1 : Fin 2) else 0)=
          primitivePair (oneSlopeCoordinates d u j v) none (some k) := by
        funext b; cases b <;> rfl
      rwa [he] at hh
  | some i =>
    cases k with
    | none =>
      have hh := B.smallPrimitive_formal_reindex (by omega) _
        (A.translated_slope_coordinate_formal_law hlarge hr ha d (j i) u (v i))
        (fun b : Bool => if b then (0 : Fin 2) else 1)
      have he : ![(slopeTestIndex d,u),(coordinateTestIndex (j i),v i)] ∘
          (fun b : Bool => if b then (0 : Fin 2) else 1)=
          primitivePair (oneSlopeCoordinates d u j v) (some i) none := by
        funext b; cases b <;> rfl
      rwa [he] at hh
    | some k =>
      have he : primitivePair (oneSlopeCoordinates d u j v) (some i) (some k)=
          fun b : Bool => (coordinateTestIndex (if b then j k else j i),if b then v k else v i) := by
        funext b; cases b <;> rfl
      rw [he]
      exact B.smallPrimitive_formal_of_actual (by omega) _
        (fun I _ b hb => B.coordinateFamilyLaw_all A.rectangles.rectangles _ _ I b hb)

theorem starFamily_formal_table [Fintype ι] (hlarge : 20 ≤ m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (hpair : ∀ i j, HasCentralLaw (smallFamilyModel (fun b : Bool => {σ : Bool → Bool | σ b=true}))
      (smallFamilyEval (B.smallPrimitiveInputs (by omega) (primitivePair P i j))).rangeRestrict) :
    Nonempty (FormalStarTable (A.starFamily (by omega) P)) := by
  classical
  have ht (i j : ι) : Nonempty (FormalStarTable (starPair (A.starFamily (by omega) P) i j)) := by
    have he : starPair (A.starFamily (by omega) P) i j=A.starFamily (by omega) (primitivePair P i j) := by
      funext k
      cases k with
      | none => rfl
      | some b => cases b <;> rfl
    rw [he]
    exact formalStarTable_of_small (by simpa using (by omega : 5 ≤ m+1)) _ _
      (A.starFamily_small (by omega) _) (hpair i j)
  exact formal_pairs_assemble (by simpa using hlarge)
    (sourceAlignedGroup a r m hm M B.t) B.c B.constant_aligned B.disjoint_aligned _
    (A.starFamily_supported (by omega) P) rfl (fun i j => Classical.choice (ht i j))

theorem oneSlope_formal_table [Fintype ι] (hlarge : 25 ≤ m+1)
    (hr : 0<ordinary r ∧ ordinary r<1/2) (ha : 0<a)
    (d : Fin 2) (u : CutRing × CutRing) (j : ι → Fin 2) (v : ι → CutRing × CutRing) :
    Nonempty (FormalStarTable (A.starFamily (by omega) (oneSlopeCoordinates d u j v))) :=
  A.starFamily_formal_table (by omega) _ (A.oneSlope_pairs_formal_law hlarge hr ha d u j v)

end InitialCoverSystem.PatchAtlas
end OneSlopeFormalTable

end SimpleAmenable
end
end

end OAI
