import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.OffsetFrames

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FrameCompatibility

namespace OffsetFrame
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m} {I : Finset (Fin (m+1))}
    {u : Fin (m+1) → CutRing × CutRing}

def shift (F : OffsetFrame a r m hm I u)
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (d : Fin (m+1) → CutRing × CutRing)
    (hd : sourceLatticeFullMap a r m hm k = trackTranslation d) :
    OffsetFrame a r m hm I (d+u) where
  k := k*F.k
  d := d+F.d
  projection := by rw [map_mul,hd,F.projection,trackTranslation_add]
  prescribed := by intro i hi; simp only [Pi.add_apply,F.prescribed i hi]

end OffsetFrame

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem frameStar_shift (I : Finset (Fin (m+1))) [Group.IsPerfect (alternatingGroup I)]
    (u : Fin (m+1) → CutRing × CutRing) (F : OffsetFrame a r m hm I u)
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (d : Fin (m+1) → CutRing × CutRing)
    (hd : sourceLatticeFullMap a r m hm k = trackTranslation d) (V : polygonAlgebra a) :
    B.frameStar hlarge h hr I (d+u) (F.shift k d hd) V =
      (MulAut.conj (B.t k)).toMonoidHom.comp (B.frameStar hlarge h hr I u F V) := by
  ext s : 1
  change B.t (k*F.k) * B.polygonStar hlarge h hr V (universalMap (subtypeAlternatingHom I) s) *
    (B.t (k*F.k))⁻¹ = B.t k *
      (B.t F.k * B.polygonStar hlarge h hr V (universalMap (subtypeAlternatingHom I) s) * (B.t F.k)⁻¹) * (B.t k)⁻¹
  simp only [map_mul,mul_inv_rev,mul_assoc]

theorem frameStar_reparameterize (I : Finset (Fin (m+1))) (hI : 5 ≤ I.card)
    [Group.IsPerfect (alternatingGroup I)] (b : Fin (m+1)) (hb : b ∉ I)
    (u : Fin (m+1) → CutRing × CutRing) (v : CutRing × CutRing)
    (F : OffsetFrame a r m hm I u)
    (G : OffsetFrame a r m hm I (fun i => u i-v)) (V : polygonAlgebra a) :
    B.frameStar hlarge h hr I u F V =
      B.frameStar hlarge h hr I (fun i => u i-v) G (spatialTranslate v V) := by
  let T := commonFrame a r m hm I b hb v
  let K : OffsetFrame a r m hm I u := {
    k := G.k*T.k
    d := G.d+T.d
    projection := by rw [map_mul,G.projection,T.projection,trackTranslation_add]
    prescribed := by
      intro i hi
      simp only [Pi.add_apply,G.prescribed i hi,T.common i hi,sub_add_cancel] }
  rw [B.frameStar_independent hlarge h hr I hI b hb u u F K (fun _ _ => rfl) V]
  ext s : 1
  have he := DFunLike.congr_fun (B.polygonStar_common_translate hlarge h hr I hI b hb v T V) s
  change B.t T.k * B.polygonStar hlarge h hr V (universalMap (subtypeAlternatingHom I) s) * (B.t T.k)⁻¹ =
    B.polygonStar hlarge h hr (spatialTranslate v V) (universalMap (subtypeAlternatingHom I) s) at he
  change B.t (G.k*T.k) * B.polygonStar hlarge h hr V (universalMap (subtypeAlternatingHom I) s) *
    (B.t (G.k*T.k))⁻¹ = B.t G.k *
      B.polygonStar hlarge h hr (spatialTranslate v V) (universalMap (subtypeAlternatingHom I) s) * (B.t G.k)⁻¹
  rw [← he]
  simp only [map_mul,mul_inv_rev,mul_assoc]

end InitialCoverSystem
end FrameCompatibility

end SimpleAmenable
end
end

end OAI
