import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalRootCoreHomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteDimensionHomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.TrivialGroupDuality
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.DimensionFromRegularCohomology

namespace OAI

/-! # Uniform rational homology bounds for nilpotent root extensions

A fixed finitely generated root core bounds rational homology with every
coefficient representation. Torsion is allowed, and no finiteness assumption
on the coefficient representation is needed for vanishing.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

theorem rational_homology_isZero_of_surjective {H : Type} [Group H]
    (A : Rep ℤ G) (B : Rep ℤ H) (i : ℕ)
    (f : (ℚ ⊗[ℤ] groupHomology B i) →ₗ[ℚ] (ℚ ⊗[ℤ] groupHomology A i))
    (hf : Function.Surjective f)
    (hB : IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] groupHomology B i))) :
    IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] groupHomology A i)) := by
  let g : ModuleCat.of ℚ (ℚ ⊗[ℤ] groupHomology B i) ⟶
      ModuleCat.of ℚ (ℚ ⊗[ℤ] groupHomology A i) := ModuleCat.ofHom f
  let : Epi g := (ModuleCat.epi_iff_surjective g).mpr hf
  exact IsZero.of_epi g hB

theorem rational_homology_surjective_of_nilpotent_roots
    [Countable G] [Group.IsNilpotent G]
    (H : Subgroup G) (hH : H.FG)
    (hroot : ∀ g : G, ∃ k : ℕ, 0 < k ∧ g ^ k ∈ H)
    (A : Rep ℤ G) (i : ℕ) :
    Function.Surjective ((subgroupHomologyInclusion H A i).hom.baseChange ℚ) := by
  obtain ⟨T, hT, hTfg, hTcover⟩ := exists_fg_subgroup_exhaustion (G := G)
  let S (n : ℕ) := H ⊔ T n
  have hS : Monotone S := fun _ _ h => sup_le_sup_left (hT h) H
  have hSfg (n : ℕ) : (S n).FG := hH.sup (hTfg n)
  have hScover (g : G) : ∃ n, g ∈ S n := by
    obtain ⟨n, hn⟩ := hTcover g
    exact ⟨n, (show T n ≤ S n from le_sup_right) hn⟩
  have hindex (n : ℕ) : (H.subgroupOf (S n)).FiniteIndex := by
    let : Group.FG (S n) := (Group.fg_iff_subgroup_fg _).mpr (hSfg n)
    apply (isPolycyclic_of_finitelyGenerated_nilpotent (S n)).finiteIndex_of_roots
    intro g
    obtain ⟨k, hk, hg⟩ := hroot g
    exact ⟨k, hk, hg⟩
  exact rational_homology_core_surjective H S hS hScover (fun _ => le_sup_left)
    hindex A i

theorem rational_homology_isZero_of_finiteIndex (H : Subgroup G) [H.FiniteIndex]
    (A : Rep ℤ G) (i : ℕ)
    (hH : IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] groupHomology (Rep.res H.subtype A) i))) :
    IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] groupHomology A i)) :=
  rational_homology_isZero_of_surjective A (Rep.res H.subtype A) i
    ((subgroupHomologyInclusion H A i).hom.baseChange ℚ)
    (rational_finiteIndex_homology_surjective H A i) hH

theorem finitelyGenerated_nilpotent_rational_homology_bounded
    [Group.FG G] [Group.IsNilpotent G] :
    ∃ d : ℕ, ∀ (A : Rep ℤ G) (i : ℕ), d < i →
      IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] groupHomology A i)) := by
  obtain ⟨U, hU, htf⟩ :=
    (isPolycyclic_of_finitelyGenerated_nilpotent G).exists_torsionFree_finiteIndex
  let := hU
  let : Group.FG U := inferInstance
  obtain ⟨d, hPD⟩ := nilpotent_poincareDuality_of_finitelyGenerated_torsionFree htf
  let := hPD.cohomologicalDimension
  refine ⟨d, fun A i hi => rational_homology_isZero_of_finiteIndex U A i ?_⟩
  exact rationalModuleFunctor.map_isZero
    (groupHomology_isZero_above_dimension d (Rep.res U.subtype A) i hi)

theorem nilpotent_rational_homology_bounded_of_rootCore
    [Countable G] [Group.IsNilpotent G]
    (H : Subgroup G) (hH : H.FG)
    (hroot : ∀ g : G, ∃ k : ℕ, 0 < k ∧ g ^ k ∈ H) :
    ∃ d : ℕ, ∀ (A : Rep ℤ G) (i : ℕ), d < i →
      IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] groupHomology A i)) := by
  let : Group.FG H := (Group.fg_iff_subgroup_fg _).mpr hH
  obtain ⟨d, hd⟩ := finitelyGenerated_nilpotent_rational_homology_bounded (G := H)
  refine ⟨d, fun A i hi => ?_⟩
  exact rational_homology_isZero_of_surjective A (Rep.res H.subtype A) i
    ((subgroupHomologyInclusion H A i).hom.baseChange ℚ)
    (rational_homology_surjective_of_nilpotent_roots H hH hroot A i)
    (hd (Rep.res H.subtype A) i hi)

theorem nilpotent_rational_homology_bounded_of_abelianization
    [Countable G] [Group.IsNilpotent G]
    [Module.Finite ℚ (RationalAbelianSpace (Abelianization G))] :
    ∃ d : ℕ, ∀ (A : Rep ℤ G) (i : ℕ), d < i →
      IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] groupHomology A i)) := by
  obtain ⟨H, hH, hroot⟩ := nilpotent_rootCore_of_finite_abelianization (G := G)
  exact nilpotent_rational_homology_bounded_of_rootCore H hH hroot

theorem torsion_nilpotent_rational_homology_isZero
    [Countable G] [Group.IsNilpotent G] (ht : ∀ g : G, IsOfFinOrder g)
    (A : Rep ℤ G) (i : ℕ) (hi : 0 < i) :
    IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] groupHomology A i)) := by
  have hroot : ∀ g : G, ∃ k : ℕ, 0 < k ∧ g ^ k ∈ (⊥ : Subgroup G) := by
    intro g
    obtain ⟨k, hk, hg⟩ := (ht g).exists_pow_eq_one
    exact ⟨k, hk, hg⟩
  let := (poincareDuality_zero_of_subsingleton (⊥ : Subgroup G)).cohomologicalDimension
  exact rational_homology_isZero_of_surjective A (Rep.res (⊥ : Subgroup G).subtype A) i
    ((subgroupHomologyInclusion ⊥ A i).hom.baseChange ℚ)
    (rational_homology_surjective_of_nilpotent_roots ⊥ Subgroup.FG.bot hroot A i)
    (rationalModuleFunctor.map_isZero
      (groupHomology_isZero_above_dimension 0 _ i hi))

end PolycyclicRecognition

end

end OAI
