import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.ReserveAtom
import OAI.GroupTheory.SimpleAmenable.CentralCovers.InitialCoverSystem
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrimitiveCopies

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section CommonTranslatedCopies

structure CommonFrame (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)
    (I : Finset (Fin (m+1))) (u : CutRing × CutRing) where
  k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))
  d : Fin (m+1) → CutRing × CutRing
  projection : sourceLatticeFullMap a r m hm k = trackTranslation d
  common : ∀ i ∈ I, d i = u

noncomputable def commonFrame (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)
    (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I) (u : CutRing × CutRing) :
    CommonFrame a r m hm I u := by
  let h := sourceLatticeFullMap_prescribed a r m hm I b hb (fun _ => u)
  exact {
    k := h.choose
    d := h.choose_spec.choose
    projection := h.choose_spec.choose_spec.1
    common := h.choose_spec.choose_spec.2 }

noncomputable def spatialTranslate {a : ℕ} (u : CutRing × CutRing)
    (U : polygonAlgebra a) : polygonAlgebra a :=
  ⟨translate a (-u) ⁻¹' U.val,polygon_preimage_translate (-u) U.property⟩

namespace CommonFrame

variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {I : Finset (Fin (m+1))} {u : CutRing × CutRing}
    (F : CommonFrame a r m hm I u)

theorem conditional_projection (U : polygonAlgebra a) (s : alternatingGroup I) :
    sourceLatticeMap a r m hm F.k * conditionalAlternatingHom U (subtypeAlternatingHom I s) *
        (sourceLatticeMap a r m hm F.k)⁻¹ =
      conditionalAlternatingHom (spatialTranslate u U) (subtypeAlternatingHom I s) := by
  apply Subtype.ext
  change sourceLatticeFullMap a r m hm F.k * conditionalHom U (subtypeAlternatingHom I s).val *
    (sourceLatticeFullMap a r m hm F.k)⁻¹ = _
  rw [F.projection]
  apply (conditional_translation_conjugate U (subtypeAlternatingHom I s).val F.d u ?_).symm
  intro i hi
  exact F.common i ((Equiv.Perm.mem_range_ofSubtype_iff.mp ⟨s.val,rfl⟩)
    (Equiv.Perm.mem_support.mpr hi))

end CommonFrame

namespace InitialCoverSystem

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

theorem commonTranslatedAlphabet_projection {I : Finset (Fin (m+1))}
    {u : CutRing × CutRing} (F : CommonFrame a r m hm I u) (j : Fin 5) :
    (coverMap M (alternatingGenerator a r m hm)).comp (B.translatedAlphabet I j F.k) =
      (conditionalAlternatingHom (spatialTranslate u (initialTest a r j))).comp
        (subtypeAlternatingHom I) := by
  apply MonoidHom.ext
  intro s
  change coverMap M (alternatingGenerator a r m hm)
    (B.t F.k * B.initialConditional j (subtypeAlternatingHom I s) * (B.t F.k)⁻¹) = _
  rw [map_mul,map_mul,map_inv]
  rw [show coverMap M (alternatingGenerator a r m hm) (B.t F.k) =
    sourceLatticeMap a r m hm F.k from DFunLike.congr_fun B.t_projection F.k]
  rw [show coverMap M (alternatingGenerator a r m hm)
    (B.initialConditional j (subtypeAlternatingHom I s)) =
    conditionalAlternatingHom (initialTest a r j) (subtypeAlternatingHom I s) from
      DFunLike.congr_fun (B.initialConditional_projection j) (subtypeAlternatingHom I s)]
  exact F.conditional_projection _ s

theorem commonTranslatedAlphabet_independent {I : Finset (Fin (m+1))}
    {u v : CutRing × CutRing} (F : CommonFrame a r m hm I u)
    (G : CommonFrame a r m hm I v) (j : Fin 5)
    (huv : spatialTranslate u (initialTest a r j) = spatialTranslate v (initialTest a r j)) :
    B.translatedAlphabet I j F.k = B.translatedAlphabet I j G.k := by
  apply B.initialAlphabet_orbit_independent
  intro s
  rw [F.conditional_projection,G.conditional_projection,huv]

noncomputable def primitiveCopy (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (p : Fin 5 × (CutRing × CutRing)) :
    alternatingGroup I →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.translatedAlphabet I p.1 (commonFrame a r m hm I b hb p.2).k

theorem primitiveCopy_projection (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (p : Fin 5 × (CutRing × CutRing)) :
    (coverMap M (alternatingGenerator a r m hm)).comp (B.primitiveCopy I b hb p) =
      (conditionalAlternatingHom (spatialTranslate p.2 (initialTest a r p.1))).comp
        (subtypeAlternatingHom I) :=
  B.commonTranslatedAlphabet_projection (commonFrame a r m hm I b hb p.2) p.1

theorem primitiveCopy_aligned (I : Finset (Fin (m+1)))
    (b : Fin (m+1)) (hb : b ∉ I) (p : Fin 5 × (CutRing × CutRing)) (s : alternatingGroup I) :
    B.primitiveCopy I b hb p s ∈ sourceAlignedGroup a r m hm M B.t I :=
  B.translatedAlphabet_aligned I p.1 _ s

end InitialCoverSystem
end CommonTranslatedCopies

end SimpleAmenable
end
end

end OAI
