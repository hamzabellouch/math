import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrimitiveCentralLaws
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.CommonTranslatedCopies
import OAI.GroupTheory.SimpleAmenable.RandomFields.CanonicalPolygonCovariance

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

structure OffsetFrame (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)
    (I : Finset (Fin (m+1))) (u : Fin (m+1) → CutRing × CutRing) where
  k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))
  d : Fin (m+1) → CutRing × CutRing
  projection : sourceLatticeFullMap a r m hm k = trackTranslation d
  prescribed : ∀ i ∈ I, d i = u i

noncomputable def balancedOffsetFrame (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)
    (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I)
    (u : Fin (m+1) → CutRing × CutRing) : OffsetFrame a r m hm I u := by
  let h := sourceLatticeFullMap_prescribed a r m hm I b hb u
  exact ⟨h.choose,h.choose_spec.choose,h.choose_spec.choose_spec.1,h.choose_spec.choose_spec.2⟩

namespace OffsetFrame
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m} {I : Finset (Fin (m+1))}
    {u v : Fin (m+1) → CutRing × CutRing}

def difference (F : OffsetFrame a r m hm I u) (G : OffsetFrame a r m hm I v)
    (huv : ∀ i ∈ I, u i = v i) : CommonFrame a r m hm I 0 where
  k := F.k⁻¹ * G.k
  d := -F.d + G.d
  projection := by rw [map_mul,map_inv,F.projection,G.projection,trackTranslation_add,trackTranslation_neg]
  common := by intro i hi; simp only [Pi.add_apply,Pi.neg_apply,F.prescribed i hi,G.prescribed i hi,huv i hi,neg_add_cancel]

end OffsetFrame

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

noncomputable def frameStar (I : Finset (Fin (m+1))) [Group.IsPerfect (alternatingGroup I)]
    (u : Fin (m+1) → CutRing × CutRing) (F : OffsetFrame a r m hm I u)
    (V : polygonAlgebra a) :
    UniversalExtension (alternatingGroup I) →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  (MulAut.conj (B.t F.k)).toMonoidHom.comp
    ((B.polygonStar hlarge h hr V).comp (universalMap (subtypeAlternatingHom I)))

theorem frameStar_independent (I : Finset (Fin (m+1))) (hI : 5 ≤ I.card)
    [Group.IsPerfect (alternatingGroup I)] (b : Fin (m+1)) (hb : b ∉ I)
    (u v : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm I u) (G : OffsetFrame a r m hm I v)
    (huv : ∀ i ∈ I, u i = v i) (V : polygonAlgebra a) :
    B.frameStar hlarge h hr I u F V = B.frameStar hlarge h hr I v G V := by
  ext s : 1
  let x := B.polygonStar hlarge h hr V (universalMap (subtypeAlternatingHom I) s)
  have hc := B.polygonStar_frame_zero_commute hlarge h hr I hI b hb (F.difference G huv) V s
  change Commute (B.t (F.k⁻¹ * G.k)) x at hc
  have he : B.t (F.k⁻¹ * G.k) * x * (B.t (F.k⁻¹ * G.k))⁻¹ = x := by
    rw [hc.eq,mul_assoc,mul_inv_cancel,mul_one]
  change B.t F.k * x * (B.t F.k)⁻¹ = B.t G.k * x * (B.t G.k)⁻¹
  calc
    B.t F.k * x * (B.t F.k)⁻¹ =
        B.t F.k * (B.t (F.k⁻¹ * G.k) * x * (B.t (F.k⁻¹ * G.k))⁻¹) * (B.t F.k)⁻¹ := by rw [he]
    _ = B.t G.k * x * (B.t G.k)⁻¹ := by simp [map_mul,map_inv,mul_assoc]

theorem frameStar_projection (I : Finset (Fin (m+1))) [Group.IsPerfect (alternatingGroup I)]
    (u : Fin (m+1) → CutRing × CutRing) (F : OffsetFrame a r m hm I u)
    (V : polygonAlgebra a) (s : UniversalExtension (alternatingGroup I)) :
    coverMap M (alternatingGenerator a r m hm) (B.frameStar hlarge h hr I u F V s) =
      sourceLatticeMap a r m hm F.k *
        conditionalAlternatingHom V (subtypeAlternatingHom I (universalProjection _ s)) *
        (sourceLatticeMap a r m hm F.k)⁻¹ := by
  change coverMap M (alternatingGenerator a r m hm)
    (B.t F.k * B.polygonStar hlarge h hr V (universalMap (subtypeAlternatingHom I) s) * (B.t F.k)⁻¹) = _
  rw [map_mul,map_mul,map_inv,
    show coverMap M (alternatingGenerator a r m hm) (B.t F.k) = sourceLatticeMap a r m hm F.k from DFunLike.congr_fun B.t_projection F.k]
  have he := DFunLike.congr_fun (B.polygonStar_projection hlarge h hr V)
    (universalMap (subtypeAlternatingHom I) s)
  rw [show coverMap M (alternatingGenerator a r m hm)
    (B.polygonStar hlarge h hr V (universalMap (subtypeAlternatingHom I) s)) =
      conditionalAlternatingHom V (universalProjection _ (universalMap (subtypeAlternatingHom I) s)) from he]
  rw [show universalProjection _ (universalMap (subtypeAlternatingHom I) s) =
    subtypeAlternatingHom I (universalProjection _ s) from DFunLike.congr_fun (universalMap_spec _) s]

end InitialCoverSystem

end SimpleAmenable

end OAI
