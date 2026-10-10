import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.FullAlphabetGeneration

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FullSectorCompatibility
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem fullGeometricSector_mem (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V : polygonAlgebra a) (s : UniversalExtension (alternatingGroup (Fin (m+1)))) :
    B.fullGeometricSector hlarge P h V s ∈
      (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range :=
  (B.fullPrimitiveTable hlarge P h).sector_mem _ s

theorem fullGeometricSector_inclusion (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (I : Finset (Fin (m+1))) (hI : 5 ≤ I.card) [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (g : B.PrimitiveFamilyLaw I b hb P)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val) :
    (B.fullGeometricSector hlarge P h V).comp (universalMap (subtypeAlternatingHom I)) =
      B.geometricSector I b hb P g V := by
  apply CentralOn.lift_unique (coverMap M (alternatingGenerator a r m hm))
    (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range
    (B.fullPrimitiveFamily_central hlarge P h)
  · rintro x ⟨s,rfl⟩
    exact B.fullGeometricSector_mem hlarge P h V _
  · rintro x ⟨s,rfl⟩
    exact B.primitiveFamily_range_full hlarge P I hI b hb
      (B.geometricSector_mem I b hb P g V s)
  · rw [← MonoidHom.comp_assoc,B.fullGeometricSector_projection hlarge P h V hV,
      B.geometricSector_projection I b hb P g V hV,MonoidHom.comp_assoc,universalMap_spec,
      MonoidHom.comp_assoc]

theorem fullGeometricSector_whole (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P) :
    B.fullGeometricSector hlarge P h (wholePolygon a) =
      B.c.comp (universalProjection (alternatingGroup (Fin (m+1)))) := by
  apply CentralOn.lift_unique (coverMap M (alternatingGenerator a r m hm))
    (smallFamilyEval (B.smallPrimitiveInputs hlarge P)).range
    (B.fullPrimitiveFamily_central hlarge P h)
  · rintro x ⟨s,rfl⟩
    exact B.fullGeometricSector_mem hlarge P h _ s
  · rintro x ⟨s,rfl⟩
    exact B.constant_range_full hlarge P ⟨universalProjection _ s,rfl⟩
  · rw [B.fullGeometricSector_projection hlarge P h _
      (show ResolvedBy _ (wholePolygon a).val from fun x y he => Iff.rfl),
      ← MonoidHom.comp_assoc,B.c_projection]

theorem fullGeometricSector_control (hlarge : 15 < m+1)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (h : ∀ I, I.card ≤ 15 → ∀ b hb, B.PrimitiveFamilyLaw I b hb P)
    (V W : polygonAlgebra a) (hVW : V ≤ W) :
    SameActionOn (B.fullGeometricSector hlarge P h W)
      (B.c.comp (universalProjection (alternatingGroup (Fin (m+1)))))
      (B.fullGeometricSector hlarge P h V).range := by
  rw [← B.fullGeometricSector_whole hlarge P h]
  unfold fullGeometricSector
  change SameActionOn _ ((B.fullPrimitiveTable hlarge P h).sector
    (resolvedPolygonMask (primitiveTests (a := a) (r := r) P) Set.univ)) _
  rw [resolvedPolygonMask_univ]
  exact (B.fullPrimitiveTable hlarge P h).sector_control (resolvedPolygonMask_mono _ hVW)

end InitialCoverSystem
end FullSectorCompatibility

end SimpleAmenable
end
end

end OAI
