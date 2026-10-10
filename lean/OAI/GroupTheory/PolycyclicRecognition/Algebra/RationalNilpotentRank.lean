import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalHomologyDimension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentAbelianQuotientRank
import OAI.GroupTheory.PolycyclicRecognition.Lattices.IntegralLatticePowerIndex

namespace OAI

/-! # Nilpotent rational rank from a homology bound

Finite-index torsion-free subgroups of finitely generated nilpotent groups
have a top orientation class. Detecting this class after rationalization
bounds every lattice quotient. Lifting finite independent families then
bounds abelian quotients of arbitrary nilpotent groups, including torsion.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G : Type} [Group G] [Group.IsNilpotent G]

theorem finitelyGenerated_nilpotent_lattice_quotient_rank_le_of_rational_bound
    [Group.FG G] {d : ℕ} (hd : RationalHomologyDimensionLE G d)
    (n : ℕ) (q : G →* IntegralLatticeGroup n) (hq : Function.Surjective q) : n ≤ d := by
  obtain ⟨U, hU, htf⟩ :=
    (isPolycyclic_of_finitelyGenerated_nilpotent G).exists_torsionFree_finiteIndex
  let := hU
  let : Group.FG U := inferInstance
  obtain ⟨m, hm⟩ := nilpotent_poincareDuality_of_finitelyGenerated_torsionFree htf
  have hmd : m ≤ d := hm.dimension_le_of_rational_homology_bound (hd.subgroup U)
  let := hm.cohomologicalDimension
  let P := U.map q
  let : P.FiniteIndex := Subgroup.FiniteIndex.map_of_surjective U hq
  let qU : U →* P := (q.comp U.subtype).codRestrict P (fun u => ⟨u, u.property, rfl⟩)
  have hqU : Function.Surjective qU := by
    rintro ⟨a, u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, rfl⟩
  let : Group.FG P := Group.fg_of_surjective hqU
  have htfP : HasNoNontrivialTorsion P :=
    ((integralLattice_poincareDuality n).finiteCohomologicalDimension _).torsionFree.of_injective
      P.subtype Subtype.val_injective
  obtain ⟨r, ⟨e⟩⟩ := exists_integralLattice_equiv htfP
  have hrm : r ≤ m := (isPolycyclic_of_finitelyGenerated_nilpotent U).lattice_quotient_rank_le
    m r (e.symm.toMonoidHom.comp qU) (e.symm.surjective.comp hqU)
  let := (integralLattice_poincareDuality r).of_equiv e |>.cohomologicalDimension
  let f : IntegralLatticeGroup n →* P :=
    (latticePowerHom n P.index).codRestrict P (fun a => P.pow_index_mem a)
  have hf : Function.Injective f := by
    intro a b h
    exact latticePowerHom_injective n (Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := P)))
      (congrArg Subtype.val h)
  exact (lattice_rank_le_cohomologicalDimension r n f hf).trans (hrm.trans hmd)

theorem nilpotent_abelian_quotient_lattice_rank_le_of_rational_bound
    {A : Type} [CommGroup A] {d : ℕ} (hd : RationalHomologyDimensionLE G d)
    (q : G →* A) (hq : Function.Surjective q) (n : ℕ)
    (i : IntegralLatticeGroup n →* A) (hi : Function.Injective i) : n ≤ d := by
  let P := i.range.comap q
  let qP : P →* i.range :=
    { toFun := fun x => ⟨q x, x.property⟩
      map_one' := Subtype.ext q.map_one
      map_mul' := fun x y => Subtype.ext (q.map_mul x y) }
  have hqP : Function.Surjective qP := by
    intro a
    obtain ⟨g, hg⟩ := hq a
    have hgP : g ∈ P := by change q g ∈ i.range; rw [hg]; exact a.property
    exact ⟨⟨g, hgP⟩, Subtype.ext hg⟩
  let e := MonoidHom.ofInjective hi
  let : Group.FG (IntegralLatticeGroup n) := inferInstance
  let : Group.FG i.range := Group.fg_of_surjective e.surjective
  obtain ⟨H, hH, hsurj⟩ := exists_fg_subgroup_surjective qP hqP
  let : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  exact finitelyGenerated_nilpotent_lattice_quotient_rank_le_of_rational_bound
    ((hd.subgroup P).subgroup H) n
    (e.symm.toMonoidHom.comp (qP.comp H.subtype)) (e.symm.surjective.comp hsurj)

theorem nilpotent_abelian_quotient_rank_le_of_rational_bound
    {A : Type} [CommGroup A] {d : ℕ} (hd : RationalHomologyDimensionLE G d)
    (q : G →* A) (hq : Function.Surjective q) : Module.rank ℤ (Additive A) ≤ d := by
  by_contra h
  have hlt : (d : Cardinal) < Module.rank ℤ (Additive A) := lt_of_not_ge h
  have hle : ((d + 1 : ℕ) : Cardinal) ≤ Module.rank ℤ (Additive A) := by
    rw [Nat.cast_add, Nat.cast_one]
    exact Cardinal.natCast_add_one_le_iff.mpr hlt
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_rank hle
  have hn := nilpotent_abelian_quotient_lattice_rank_le_of_rational_bound hd q hq (d + 1)
    (independentLatticeHom b) (independentLatticeHom_injective hb)
  omega

theorem nilpotent_rational_abelianization_finite_of_homology_bound
    {d : ℕ} (hd : RationalHomologyDimensionLE G d) :
    Module.Finite ℚ (RationalAbelianSpace (Abelianization G)) := by
  apply Module.rank_lt_aleph0_iff.mp
  rw [rationalAbelianSpace_rank]
  exact (nilpotent_abelian_quotient_rank_le_of_rational_bound hd
    (Abelianization.of (G := G)) (QuotientGroup.mk'_surjective (commutator G))).trans_lt
      Cardinal.natCast_lt_aleph0

theorem nilpotent_rational_abelianization_finite_iff_homology_bounded [Countable G] :
    Module.Finite ℚ (RationalAbelianSpace (Abelianization G)) ↔
      ∃ d : ℕ, RationalHomologyDimensionLE G d := by
  constructor
  · intro h
    let := h
    exact nilpotent_rational_homology_bounded_of_abelianization
  · rintro ⟨d, hd⟩
    exact nilpotent_rational_abelianization_finite_of_homology_bound hd

end PolycyclicRecognition

end

end OAI
