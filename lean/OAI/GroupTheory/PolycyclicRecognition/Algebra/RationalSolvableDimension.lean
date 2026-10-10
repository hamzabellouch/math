import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalNilpotentClassBound
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteKernelSubgroupBounds
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentByAbelianReduction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentTorsionQuotientEndgame
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalNilpotentRank
import OAI.GroupTheory.PolycyclicRecognition.Algebra.VirtualSolvableDimension

namespace OAI

/-! # Finite virtual integral dimension modulo the finite normal radical

The nilpotent radical is selected using rational dimension and the bound on
finite subgroup orders. No integral dimension of the ambient group is assumed.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped IsMulCommutative
variable {G : Type} [Group G] [Group.FG G] [Group.IsSolvable G]

omit [Group.FG G] [Group.IsSolvable G] in
theorem nilpotent_normal_torsionFree_of_no_finite_normal
    (hb : HasBoundedFiniteSubgroupOrders G)
    (hfinite : ∀ T : Subgroup G, T.Normal → Finite T → T = ⊥)
    (F : Subgroup G) [F.Normal] [Group.IsNilpotent F] :
    HasNoNontrivialTorsion F := by
  let T := nilpotentTorsionSubgroup (G := F)
  let : Finite T := finite_locallyFinite_normal_subgroup T
    nilpotentTorsionSubgroup_locallyFinite (hb.subgroup F)
  let e := T.equivMapOfInjective F.subtype Subtype.val_injective
  let : Finite (normalNilpotentTorsionSubgroup F) := Finite.of_equiv T e.toEquiv
  have hD := hfinite (normalNilpotentTorsionSubgroup F) inferInstance inferInstance
  intro x n hn hx
  have hxt : x ∈ T := isOfFinOrder_iff_pow_eq_one.mpr
    ⟨n, Nat.pos_of_ne_zero hn, hx⟩
  have hxD : (x : G) ∈ normalNilpotentTorsionSubgroup F := ⟨x, hxt, rfl⟩
  rw [hD] at hxD
  exact Subtype.ext hxD

theorem solvable_rational_virtual_finite_dimension_of_no_finite_normal
    (d : ℕ) (hd : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d)
    (hb : HasBoundedFiniteSubgroupOrders G)
    (hfinite : ∀ T : Subgroup G, T.Normal → Finite T → T = ⊥) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
  let : Countable G := countable_of_group_fg G
  obtain ⟨F, hFn, hF, hmax⟩ :=
    exists_maximal_nilpotent_normal_of_rational_dimension d hd hb
  let := hFn
  let := hF
  have htf := nilpotent_normal_torsionFree_of_no_finite_normal hb hfinite F
  have hFdim : HasFiniteIntegralCohomologicalDimension F :=
    ⟨d + 1, (rationalHomologyDimension_of_rational_representation d
      (RationalQuotient.rational_dimension_subgroup F d hd)).locallyNilpotent_integralDimension
      htf (fun _ _ => inferInstance)⟩
  obtain ⟨H, hHn, hHi, hcomm⟩ :=
    exists_finiteIndex_commutator_le_maximal_nilpotent F hFdim hmax
  let := hHn
  let := hHi
  let N := commutator H
  let f : N →* F := (H.subtype.comp N.subtype).codRestrict F
    (fun x => hcomm ⟨x, x.property, rfl⟩)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : F => (z : G)) hxy
  let : Group.IsNilpotent N := nilpotent_of_injective_hom f hf
  let : Module.Finite ℚ (RationalAbelianSpace (Abelianization N)) :=
    nilpotent_rational_abelianization_finite_of_homology_bound
      (((rationalHomologyDimension_of_rational_representation d hd).subgroup H).subgroup N)
  exact exists_solvable_finiteDimension_of_finiteIndex H
    (nilpotent_abelianization_virtual_finite_dimension N (htf.of_injective f hf))

theorem solvable_rational_mod_finite_radical_dimension
    (d : ℕ) (hd : HasProjectiveDimensionLE (Rep.trivial ℚ G ℚ) d)
    (hb : HasBoundedFiniteSubgroupOrders G) :
    ∃ T : Subgroup G, ∃ hT : T.Normal, letI := hT
      Finite T ∧ (∃ V : Subgroup (G ⧸ T), V.FiniteIndex ∧ Group.IsSolvable V ∧
        HasFiniteIntegralCohomologicalDimension V) := by
  obtain ⟨T, hTc, hTf, hmax⟩ := exists_largest_finite_normal hb
  let := hTc
  let := hTf
  have hq : HasBoundedFiniteSubgroupOrders (G ⧸ T) := by
    let : Finite (QuotientGroup.mk' T).ker := by
      simpa only [QuotientGroup.ker_mk'] using hTf
    exact boundedFiniteSubgroupOrders_of_finite_kernel_quotient
      (QuotientGroup.mk' T) (QuotientGroup.mk'_surjective T) hb
  refine ⟨T, inferInstance, hTf, ?_⟩
  apply solvable_rational_virtual_finite_dimension_of_no_finite_normal d
    (RationalQuotient.rational_dimension_quotient T d hd) hq
  intro S hn hs
  let := hn
  let := hs
  exact finite_normal_quotient_eq_bot T hmax S

end PolycyclicRecognition

end

end OAI
