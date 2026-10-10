import OAI.GroupTheory.PolycyclicRecognition.Algebra.AscendingNilpotentUnion
import OAI.GroupTheory.PolycyclicRecognition.Algebra.VirtualNilpotentStableBase
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicJoinDimension

namespace OAI

/-! # The ascending virtually nilpotent case of the finiteness endgame

The hypotheses describe an actual ascending exhaustion of the kernel, with
conjugation by a chosen lift as the transition automorphism. The construction
produces a solvable subgroup of finite index and finite integral dimension.
It does not assume any finiteness theorem for arbitrary elementary amenable
groups of type FP-infinity.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G : Type} [Group G]

theorem map_subtype_conjNormal (N : Subgroup G) [N.Normal] (t : G) (L : Subgroup N) :
    (L.map N.subtype).map (MulAut.conj t).toMonoidHom =
      (L.map (MulAut.conjNormal (H := N) t).toMonoidHom).map N.subtype := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem exists_finiteIndex_solvable_finiteDimension_of_ascending
    (q : G →* Multiplicative ℤ) (t : G) (ht : q t = Multiplicative.ofAdd 1)
    (B : Subgroup q.ker) [Group.FG B]
    (hB : B.map (MulAut.conjNormal (H := q.ker) t).toMonoidHom ≤ B)
    (hcover : ∀ g : q.ker, ∃ n,
      g ∈ automorphismStage (MulAut.conjNormal (H := q.ker) t) B n)
    (hBnil : Group.IsVirtuallyNilpotent B) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
  let α : MulAut q.ker := MulAut.conjNormal t
  obtain ⟨D, hDindex, hDnil, _, hDstable, d, hd⟩ :=
    exists_endomorphismInvariant_nilpotent_finiteIndex hBnil
  let := hDindex
  let := hDnil
  let := hd
  let K : Subgroup q.ker := D.map B.subtype
  have hKstable : K.map α.toMonoidHom ≤ K :=
    mappedSubgroup_automorphism_stable α B hB D (hDstable _)
  let L : Subgroup q.ker := ⨆ n, automorphismStage α K n
  have hLindex : L.FiniteIndex := finiteIndex_automorphism_iSup_refinement α B hB hcover D
  let := hLindex
  let eDK : D ≃* K := D.equivMapOfInjective B.subtype B.subtype_injective
  let : Group.IsNilpotent K := Group.nilpotent_of_mulEquiv eDK
  have hLnil : Group.IsNilpotent L := nilpotent_automorphism_iSup α K hKstable
  let := hLnil
  have hLdim : HasProjectiveDimensionLE (trivialIntegral L) (d + 1) :=
    dimension_automorphism_iSup_refinement α B hB D (hDstable _) d
  let := hLdim
  have hLinv : L.map α.toMonoidHom = L := automorphism_iSup_invariant α K hKstable
  let A : Subgroup G := L.map q.ker.subtype
  let eLA : L ≃* A := L.equivMapOfInjective q.ker.subtype q.ker.subtype_injective
  let : Group.IsNilpotent A := Group.nilpotent_of_mulEquiv eLA
  have hAdim : HasFiniteIntegralCohomologicalDimension A :=
    ⟨d + 1, cohomologicalDimension_le_of_equiv eLA (d + 1)⟩
  have hAker : A ≤ q.ker := by
    rintro _ ⟨a, _, rfl⟩
    exact a.property
  have hnorm : t ∈ Subgroup.normalizer A := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change (L.map q.ker.subtype).map (MulAut.conj t).toMonoidHom = L.map q.ker.subtype
    rw [map_subtype_conjNormal, hLinv]
  let V : Subgroup G := A ⊔ Subgroup.zpowers t
  have hVindex : V.FiniteIndex := finiteIndex_of_kernel_cover q.ker L V le_sup_left (by
    intro g
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
      (integerQuotient_generator q t ht (QuotientGroup.mk' q.ker g))
    refine ⟨t ^ n, (show Subgroup.zpowers t ≤ V from le_sup_right)
      (Subgroup.zpow_mem_zpowers t n), ?_⟩
    simpa only [map_zpow] using hn)
  exact ⟨V, hVindex, cyclicJoin_solvable q t ht A hAker hnorm,
    cyclicJoin_finiteDimension q t ht A hAker hnorm hAdim⟩

end PolycyclicRecognition

end

end OAI
