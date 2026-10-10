import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.ReserveAtom
import OAI.GroupTheory.SimpleAmenable.CentralCovers.InitialCoverSystem

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PrimitiveCopies

namespace InitialCoverSystem

variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)

noncomputable def initialConditional (j : Fin 5) :
    alternatingGroup (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  B.initialTable.comp (polygonTableInput (initialTest a r) j)

@[simp] theorem initialConditional_input (j : Fin 5)
    (s : alternatingGroup (Fin (m+1))) (hs : s.val.support.card ≤ 5) :
    B.initialConditional j s = PresentedGroup.of (sourceConditionalLabel m (j,⟨s.val,s.property,hs⟩)) :=
  B.initialTable_input (j,⟨s.val,s.property,hs⟩)

theorem initialConditional_projection (j : Fin 5) :
    (coverMap M (alternatingGenerator a r m hm)).comp (B.initialConditional j) =
    conditionalAlternatingHom (initialTest a r j) := by
  rw [initialConditional,← MonoidHom.comp_assoc,B.initialTable_projection]
  apply MonoidHom.ext
  intro s
  exact actualPolygonTableHom_input (initialTest a r) j s

theorem initialConditional_zero : B.initialConditional 0 = B.c :=
  B.initialTable_constant

noncomputable def initialAlphabet (I : Finset (Fin (m+1))) (j : Fin 5) :
    alternatingGroup I →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  (B.initialConditional j).comp (subtypeAlternatingHom I)

theorem initialAlphabet_aligned (I : Finset (Fin (m+1))) (j : Fin 5)
    (s : alternatingGroup I) :
    B.initialAlphabet I j s ∈ sourceAlignedGroup a r m hm M B.t I := by
  have hle : Subgroup.closure {g : alternatingGroup I | Equiv.Perm.IsThreeCycle g.val} ≤
      (sourceAlignedGroup a r m hm M B.t I).comap (B.initialAlphabet I j) := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    change B.initialConditional j (subtypeAlternatingHom I g) ∈
      sourceAlignedGroup a r m hm M B.t I
    have hc : (subtypeAlternatingHom I g).val.support.card ≤ 5 := by
      change (Equiv.Perm.ofSubtype g.val).support.card ≤ 5
      have hI : (Subtype.fintype (fun x : Fin (m+1) => x ∈ I)) =
          (inferInstance : Fintype I) := Subsingleton.elim _ _
      rw [Equiv.Perm.support_ofSubtype, Finset.card_map, hI, hg.card_support]
      decide
    rw [B.initialConditional_input j _ hc]
    exact alignedGroup_input _ _ _
      ((j,⟨(subtypeAlternatingHom I g).val,(subtypeAlternatingHom I g).property,hc⟩) :
        SmallConditional m)
      (Equiv.Perm.mem_range_ofSubtype_iff.mp ⟨g.val,rfl⟩)
  rw [alternatingGroup.closure_isThreeCycles_eq_top] at hle
  exact hle (Subgroup.mem_top s)

noncomputable def translatedAlphabet (I : Finset (Fin (m+1))) (j : Fin 5)
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))) :
    alternatingGroup I →* BoundedRelationCover M (alternatingGenerator a r m hm) :=
  (MulAut.conj (B.t k)).toMonoidHom.comp (B.initialAlphabet I j)

theorem translatedAlphabet_aligned (I : Finset (Fin (m+1))) (j : Fin 5)
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))) (s : alternatingGroup I) :
    B.translatedAlphabet I j k s ∈ sourceAlignedGroup a r m hm M B.t I :=
  alignedGroup_conjugate _ _ _ k (B.initialAlphabet_aligned I j s)

theorem initialAlphabet_orbit_independent (I : Finset (Fin (m+1))) (j : Fin 5)
    (k l : Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hkl : ∀ s : alternatingGroup I,
      sourceLatticeMap a r m hm k * conditionalAlternatingHom (initialTest a r j)
        (subtypeAlternatingHom I s) * (sourceLatticeMap a r m hm k)⁻¹ =
      sourceLatticeMap a r m hm l * conditionalAlternatingHom (initialTest a r j)
        (subtypeAlternatingHom I s) * (sourceLatticeMap a r m hm l)⁻¹) :
    B.translatedAlphabet I j k = B.translatedAlphabet I j l := by
  apply MonoidHom.eq_of_eqOn_dense alternatingGroup.closure_isThreeCycles_eq_top
  intro s hs
  have hc : (subtypeAlternatingHom I s).val.support.card ≤ 5 := by
    change (Equiv.Perm.ofSubtype s.val).support.card ≤ 5
    have hI : (Subtype.fintype (fun x : Fin (m+1) => x ∈ I)) =
        (inferInstance : Fintype I) := Subsingleton.elim _ _
    rw [Equiv.Perm.support_ofSubtype, Finset.card_map, hI, hs.card_support]
    decide
  change B.t k * B.initialConditional j (subtypeAlternatingHom I s) * (B.t k)⁻¹ =
    B.t l * B.initialConditional j (subtypeAlternatingHom I s) * (B.t l)⁻¹
  rw [B.initialConditional_input j _ hc]
  exact lifted_translation_orbit_independent (sourceLatticeMap a r m hm) B.t
    (alternatingGenerator a r m hm (sourceConditionalLabel m
      (j,⟨(subtypeAlternatingHom I s).val,(subtypeAlternatingHom I s).property,hc⟩)))
    _ (B.t_stabilizers _) k l (hkl s)

end InitialCoverSystem
end PrimitiveCopies

end SimpleAmenable
end
end

end OAI
