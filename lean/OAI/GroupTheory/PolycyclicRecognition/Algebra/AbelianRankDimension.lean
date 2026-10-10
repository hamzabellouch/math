import OAI.GroupTheory.PolycyclicRecognition.Algebra.CountableUnionDimension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TorsionFreeAbelianRank
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.DimensionFromRegularCohomology

namespace OAI

/-! # Finite integral dimension for countable torsion-free abelian groups

The rank bound is used on finitely generated subgroups. Each is an actual
integral lattice, and the countable-union argument adds at most one dimension.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
variable {A : Type} [CommGroup A]

theorem abelian_fg_subgroup_lattice_of_rank (d : ℕ)
    (hrank : Module.rank ℤ (Additive A) ≤ d) (htf : HasNoNontrivialTorsion A)
    (H : Subgroup A) (hH : H.FG) :
    ∃ n ≤ d, Nonempty (IntegralLatticeGroup n ≃* H) := by
  let : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  have htfH : HasNoNontrivialTorsion H := by
    intro a n hn ha
    apply Subtype.ext
    exact htf a n hn (congrArg Subtype.val ha)
  obtain ⟨n, ⟨e⟩⟩ := exists_integralLattice_equiv htfH
  let f : (Fin n → ℤ) →ₗ[ℤ] Additive A :=
    (H.subtype.comp e.toMonoidHom).toAdditive.toIntLinearMap
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have hn : (n : Cardinal) ≤ Module.rank ℤ (Additive A) := by
    simpa using f.rank_le_of_injective hf
  have hnd : n ≤ d := by exact_mod_cast hn.trans hrank
  exact ⟨n, hnd, ⟨e⟩⟩

theorem abelian_fg_subgroup_dimension_of_rank (d : ℕ)
    (hrank : Module.rank ℤ (Additive A) ≤ d) (htf : HasNoNontrivialTorsion A)
    (H : Subgroup A) (hH : H.FG) :
    HasProjectiveDimensionLE (trivialIntegral H) d := by
  obtain ⟨n, hnd, ⟨e⟩⟩ := abelian_fg_subgroup_lattice_of_rank d hrank htf H hH
  let := ((integralLattice_poincareDuality n).of_equiv e).cohomologicalDimension
  exact hasProjectiveDimensionLT_of_ge (trivialIntegral H) (n + 1) (d + 1) (by omega)

theorem abelian_cohomologicalDimension_of_rank [Countable A] (d : ℕ)
    (hrank : Module.rank ℤ (Additive A) ≤ d) (htf : HasNoNontrivialTorsion A) :
    HasProjectiveDimensionLE (trivialIntegral A) (d + 1) :=
  cohomologicalDimension_le_of_fg_subgroups d
    (abelian_fg_subgroup_dimension_of_rank d hrank htf)

end PolycyclicRecognition

end

end OAI
