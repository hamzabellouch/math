import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.FinitePrimitiveResolution
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.TangentChartTemplates
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrimitiveCentralLaws

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section CanonicalPolygonCovariance
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem geometricSector_translate {ι : Type*} [Finite ι]
    (I : Finset (Fin (m+1))) [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw I b hb P) (u : CutRing × CutRing)
    (F : CommonFrame a r m hm I u)
    (g : B.PrimitiveFamilyLaw I b hb (translatedTemplate P u))
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val) :
    (MulAut.conj (B.t F.k)).toMonoidHom.comp (B.geometricSector I b hb P h V) =
      B.geometricSector I b hb (translatedTemplate P u) g (spatialTranslate u V) := by
  apply CentralOn.lift_unique (coverMap M (alternatingGenerator a r m hm))
    (copyFamilyEval (B.primitiveFamily I b hb (translatedTemplate P u))).range g
  · rintro x ⟨s,rfl⟩
    change ∃ w, copyFamilyEval (B.primitiveFamily I b hb (translatedTemplate P u)) w =
      (MulAut.conj (B.t F.k)).toMonoidHom (B.geometricSector I b hb P h V s)
    change ∃ w, copyFamilyEval (B.primitiveFamily I b hb (fun i => ((P i).1,u+(P i).2))) w = _
    rw [B.primitiveFamily_conjugate I b hb P u F,copyFamilyEval_comp]
    obtain ⟨w,hw⟩ := B.geometricSector_mem I b hb P h V s
    exact ⟨w,congrArg (MulAut.conj (B.t F.k)).toMonoidHom hw⟩
  · rintro x ⟨s,rfl⟩
    exact B.geometricSector_mem I b hb _ g _ s
  · ext s : 1
    change coverMap M (alternatingGenerator a r m hm)
      (B.t F.k * B.geometricSector I b hb P h V s * (B.t F.k)⁻¹) =
      coverMap M (alternatingGenerator a r m hm)
        (B.geometricSector I b hb (translatedTemplate P u) g (spatialTranslate u V) s)
    rw [map_mul,map_mul,map_inv,
      show coverMap M (alternatingGenerator a r m hm) (B.t F.k) =
        sourceLatticeMap a r m hm F.k from DFunLike.congr_fun B.t_projection F.k,
      show coverMap M (alternatingGenerator a r m hm) (B.geometricSector I b hb P h V s) =
        conditionalAlternatingHom V (subtypeAlternatingHom I (universalProjection _ s)) from
        DFunLike.congr_fun (B.geometricSector_projection I b hb P h V hV) s,
      show coverMap M (alternatingGenerator a r m hm)
          (B.geometricSector I b hb (translatedTemplate P u) g (spatialTranslate u V) s) =
        conditionalAlternatingHom (spatialTranslate u V)
          (subtypeAlternatingHom I (universalProjection _ s)) from
        DFunLike.congr_fun (B.geometricSector_projection I b hb _ g _
          (translatedTemplate_resolved P V hV u)) s]
    exact F.conditional_projection V _

variable [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem polygonStar_common_translate
    (I : Finset (Fin (m+1))) (hI : 5 ≤ I.card) [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (u : CutRing × CutRing)
    (F : CommonFrame a r m hm I u) (V : polygonAlgebra a) :
    (MulAut.conj (B.t F.k)).toMonoidHom.comp
        ((B.polygonStar hlarge h hr V).comp (universalMap (subtypeAlternatingHom I))) =
      (B.polygonStar hlarge h hr (spatialTranslate u V)).comp (universalMap (subtypeAlternatingHom I)) := by
  obtain ⟨S,hS⟩ := polygon_finite_primitive_resolution r hr V
  let P : S → Fin 5 × (CutRing × CutRing) := fun p => p.val
  have hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val := hS
  rw [B.polygonStar_eq hlarge h hr P V hV,
    B.polygonStar_eq hlarge h hr (translatedTemplate P u) (spatialTranslate u V)
      (translatedTemplate_resolved P V hV u),
    B.fullGeometricSector_inclusion hlarge P _ I hI b hb (h S P I b hb) V hV,
    B.fullGeometricSector_inclusion hlarge (translatedTemplate P u) _ I hI b hb
      (h S (translatedTemplate P u) I b hb) (spatialTranslate u V)
      (translatedTemplate_resolved P V hV u)]
  exact B.geometricSector_translate I b hb P _ u F _ V hV

theorem polygonStar_frame_zero_commute
    (I : Finset (Fin (m+1))) (hI : 5 ≤ I.card) [Group.IsPerfect (alternatingGroup I)]
    (b : Fin (m+1)) (hb : b ∉ I) (F : CommonFrame a r m hm I 0)
    (V : polygonAlgebra a) (s : UniversalExtension (alternatingGroup I)) :
    Commute (B.t F.k) (B.polygonStar hlarge h hr V (universalMap (subtypeAlternatingHom I) s)) := by
  have he := DFunLike.congr_fun (B.polygonStar_common_translate hlarge h hr I hI b hb 0 F V) s
  have hz : spatialTranslate (0 : CutRing × CutRing) V = V := by
    apply Subtype.ext
    ext p
    simp [spatialTranslate,translate_zero]
  rw [hz] at he
  change B.t F.k * B.polygonStar hlarge h hr V (universalMap (subtypeAlternatingHom I) s) *
    (B.t F.k)⁻¹ = B.polygonStar hlarge h hr V (universalMap (subtypeAlternatingHom I) s) at he
  have hh := congrArg (fun x => x * B.t F.k) he
  exact show _*_ = _*_ from by simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh

end InitialCoverSystem
end CanonicalPolygonCovariance

end SimpleAmenable
end
end

end OAI
