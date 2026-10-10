import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalFiniteIndexHomology
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentRootExhaustion
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalCoefficientHomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NilpotentFirstHomologyDimension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolycyclicTorsionFree

namespace OAI

/-! # Rational homology is controlled by a finite nilpotent root core

Every class is represented at a finitely generated stage. The core has finite
index in that stage, so rational transfer lifts the class to the fixed core.
No stabilization or injectivity of integral homology maps is assumed.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped TensorProduct
attribute [local instance 2000] Rep.hV2 Rep.instLinear ModuleCat.isModule
attribute [local instance 2300] TensorProduct.instModule
variable {G : Type} [Group G]

theorem rational_homology_core_surjective (H : Subgroup G) (S : ℕ → Subgroup G)
    (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n)
    (hHS : ∀ n, H ≤ S n) (hindex : ∀ n, (H.subgroupOf (S n)).FiniteIndex)
    (A : Rep ℤ G) (i : ℕ) :
    Function.Surjective ((subgroupHomologyInclusion H A i).hom.baseChange ℚ) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  intro x hx
  clear hx
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    obtain ⟨n, z, hz⟩ := exists_homologyClass_in_subgroup S hS hcover A i x
    let := hindex n
    obtain ⟨y, hy⟩ := rational_nestedSubgroup_homology_surjective (hHS n) A i (a ⊗ₜ[ℤ] z)
    refine ⟨y, ?_⟩
    have he := congrArg (fun f => f.hom.baseChange ℚ)
      (subgroupHomologyInclusion_factor (hHS n) A i)
    simp only [ModuleCat.hom_comp, LinearMap.baseChange_comp] at he
    rw [← he, LinearMap.comp_apply, hy, LinearMap.baseChange_tmul, hz]
  | add x y hx hy => exact Submodule.add_mem _ hx hy

theorem rational_homology_finite_of_core (H : Subgroup G) (S : ℕ → Subgroup G)
    (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n)
    (hHS : ∀ n, H ≤ S n) (hindex : ∀ n, (H.subgroupOf (S n)).FiniteIndex)
    (A : Rep ℤ G) (i : ℕ)
    [Module.Finite ℚ (ℚ ⊗[ℤ] groupHomology (Rep.res H.subtype A) i)] :
    Module.Finite ℚ (ℚ ⊗[ℤ] groupHomology A i) :=
  Module.Finite.of_surjective _
    (rational_homology_core_surjective H S hS hcover hHS hindex A i)

theorem finitelyGenerated_nilpotent_rational_homology_finite
    [Group.FG G] [Group.IsNilpotent G]
    (A : Rep ℤ G) [Module.Finite ℚ (ℚ ⊗[ℤ] A)] (i : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] groupHomology A i) := by
  obtain ⟨U, hU, htf⟩ :=
    (isPolycyclic_of_finitelyGenerated_nilpotent G).exists_torsionFree_finiteIndex
  let := hU
  let : Group.FG U := inferInstance
  obtain ⟨d, hPD⟩ := nilpotent_poincareDuality_of_finitelyGenerated_torsionFree htf
  let : Module.Finite ℚ (ℚ ⊗[ℤ] groupHomology (Rep.res U.subtype A) i) :=
    (hPD.typeFPInfinity U i).rational_homology_finite (Rep.res U.subtype A)
  exact Module.Finite.of_surjective ((subgroupHomologyInclusion U A i).hom.baseChange ℚ)
    (rational_finiteIndex_homology_surjective U A i)

theorem nilpotent_rational_homology_finite_of_abelianization
    [Countable G] [Group.IsNilpotent G]
    [Module.Finite ℚ (RationalAbelianSpace (Abelianization G))]
    (A : Rep ℤ G) [Module.Finite ℚ (ℚ ⊗[ℤ] A)] (i : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] groupHomology A i) := by
  obtain ⟨H, hH, hroot⟩ := nilpotent_rootCore_of_finite_abelianization (G := G)
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
  let : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  let : Module.Finite ℚ (ℚ ⊗[ℤ] groupHomology (Rep.res H.subtype A) i) :=
    finitelyGenerated_nilpotent_rational_homology_finite (Rep.res H.subtype A) i
  exact rational_homology_finite_of_core H S hS hScover (fun _ => le_sup_left) hindex A i

theorem nilpotent_rational_homology_finite [Countable G] [Group.IsNilpotent G]
    (hG : HasFiniteIntegralCohomologicalDimension G)
    (A : Rep ℤ G) [Module.Finite ℚ (ℚ ⊗[ℤ] A)] (i : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] groupHomology A i) := by
  obtain ⟨H, hH, S, hS, _, hHS, hcover, hindex⟩ := exists_nilpotent_root_exhaustion hG
  let : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  obtain ⟨d, hPD⟩ := nilpotent_poincareDuality_of_finitelyGenerated_torsionFree
    (hG.subgroup H).torsionFree
  let : Module.Finite ℚ (ℚ ⊗[ℤ] groupHomology (Rep.res H.subtype A) i) :=
    (hPD.typeFPInfinity H i).rational_homology_finite (Rep.res H.subtype A)
  exact rational_homology_finite_of_core H S hS hcover hHS hindex A i

theorem nilpotent_rational_homology_finite_of_first_homology
    [Countable G] [Group.IsNilpotent G]
    [Module.Finite ℚ (ℚ ⊗[ℤ] groupHomology.H1 (integralTrivialCoefficient G))]
    (A : Rep ℤ G) [Module.Finite ℚ (ℚ ⊗[ℤ] A)] (i : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] groupHomology A i) := by
  let : Module.Finite ℚ (RationalAbelianSpace (Abelianization G)) :=
    rationalH1_finite_iff_abelianization_finite.mp inferInstance
  exact nilpotent_rational_homology_finite_of_abelianization A i

end PolycyclicRecognition

end

end OAI
