import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.WindowIntervals

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SmallSectorGeneration

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev FiveSubalphabet (J : Finset α) := {I : Finset α // I ⊆ J ∧ I.card = 5}

instance fiveSubalphabet_perfect (J : Finset α) (I : FiveSubalphabet J) :
    Group.IsPerfect (alternatingGroup I.val) := alphabetPerfect I.val (by rw [I.property.2])

theorem subalphabet_five_generate (J : Finset α) (hJ : 5 ≤ J.card) :
    (⨆ I : FiveSubalphabet J, (subalphabetHom I.property.1).range) = ⊤ := by
  apply top_unique
  rw [← alternatingGroup.closure_isThreeCycles_eq_top]
  apply (Subgroup.closure_le _).mpr
  intro g hg
  let σ := subtypeAlternatingHom J g
  have hs : σ.val.support ⊆ J := (subtypeAlternatingHom_mem_range J σ).mp ⟨g,rfl⟩
  have hc : σ.val.support.card = 3 := by
    change (Equiv.Perm.ofSubtype g.val).support.card = 3
    have hF : (Subtype.fintype (fun x : α => x ∈ J)) = (inferInstance : Fintype J) := Subsingleton.elim _ _
    rw [Equiv.Perm.support_ofSubtype,Finset.card_map,hF,hg.card_support]
  obtain ⟨I,hSI,hIJ,hI⟩ := Finset.exists_subsuperset_card_eq hs (by omega : σ.val.support.card ≤ 5) hJ
  obtain ⟨t,ht⟩ := (subtypeAlternatingHom_mem_range I σ).mpr hSI
  apply le_iSup (fun I : FiveSubalphabet J => (subalphabetHom I.property.1).range) ⟨I,hIJ,hI⟩
  refine ⟨t,?_⟩
  apply subtypeAlternatingHom_injective J
  exact (DFunLike.congr_fun (subtypeAlternatingHom_comp hIJ) t).trans ht

theorem universal_subalphabet_five_generate (J : Finset α) (hJ : 5 ≤ J.card)
    [Group.IsPerfect (alternatingGroup J)] :
    (⨆ I : FiveSubalphabet J, (universalMap (subalphabetHom I.property.1)).range) = ⊤ :=
  universal_generating_ranges (fun I : FiveSubalphabet J => subalphabetHom I.property.1)
    (subalphabet_five_generate J hJ)

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M) {ι : Type*} [Finite ι]

theorem geometricSector_five_generate
    (J : Finset (Fin (m+1))) (hJ : 5 ≤ J.card) [Group.IsPerfect (alternatingGroup J)]
    (b : Fin (m+1)) (hb : b ∉ J) (P : ι → Fin 5 × (CutRing × CutRing))
    (h : B.PrimitiveFamilyLaw J b hb P)
    (g : ∀ I : FiveSubalphabet J, B.PrimitiveFamilyLaw I.val b
      (fun hi => hb (I.property.1 hi)) P)
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val) :
    (B.geometricSector J b hb P h V).range =
      ⨆ I : FiveSubalphabet J, (B.geometricSector I.val b
        (fun hi => hb (I.property.1 hi)) P (g I) V).range := by
  rw [MonoidHom.range_eq_map,← universal_subalphabet_five_generate J hJ,Subgroup.map_iSup]
  apply iSup_congr
  intro I
  rw [← MonoidHom.range_comp]
  congr 1
  exact B.geometricSector_inclusion I.property.1 b b (fun hi => hb (I.property.1 hi)) hb
    P (g I) h V hV

end InitialCoverSystem
end SmallSectorGeneration

end SimpleAmenable
end
end

end OAI
