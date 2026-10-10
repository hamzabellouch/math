import OAI.GroupTheory.PolycyclicRecognition.Algebra.CountableUnionDimension
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentRootExhaustion
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.DimensionFromRegularCohomology
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteIndexFiniteness

namespace OAI

/-! # Finite integral dimension from a finite nilpotent root core

A finitely generated subgroup containing a positive power of every element
has finite index in each finitely generated overgroup. Those overgroups have
one common duality dimension. The countable-union theorem then supplies a
finite integral dimension for the original, possibly infinitely generated,
nilpotent group. No ambient dimension bound is assumed.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [Group G] [Group.IsNilpotent G]

theorem nilpotent_rootCore_finiteIndex_of_torsionFree
    (htf : HasNoNontrivialTorsion G) (H : Subgroup G)
    (hroot : ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H)
    (L : Subgroup G) (hL : L.FG) : (H.subgroupOf L).FiniteIndex := by
  let : Group.FG L := (Group.fg_iff_subgroup_fg L).mpr hL
  have hp := (nilpotent_polyZ_of_finitelyGenerated_torsionFree
    (htf.of_injective L.subtype Subtype.val_injective)).isPolycyclic
  apply hp.finiteIndex_of_roots
  intro g
  obtain ⟨n, hn, hg⟩ := hroot g
  exact ⟨n, hn, hg⟩

theorem nilpotent_rootCore_common_duality
    (htf : HasNoNontrivialTorsion G) (H : Subgroup G) (hH : H.FG)
    (hroot : ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H) :
    ∃ d, IsIntegralPoincareDualityGroup H d ∧
      ∀ L : Subgroup G, L.FG → H ≤ L → IsIntegralPoincareDualityGroup L d := by
  let : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hH
  obtain ⟨d, hd⟩ := nilpotent_poincareDuality_of_finitelyGenerated_torsionFree
    (htf.of_injective H.subtype Subtype.val_injective)
  refine ⟨d, hd, ?_⟩
  intro L hL hHL
  let : Group.FG L := (Group.fg_iff_subgroup_fg L).mpr hL
  obtain ⟨e, he⟩ := nilpotent_poincareDuality_of_finitelyGenerated_torsionFree
    (htf.of_injective L.subtype Subtype.val_injective)
  let := nilpotent_rootCore_finiteIndex_of_torsionFree htf H hroot L hL
  have hHe : IsIntegralPoincareDualityGroup H e :=
    (he.finiteIndex_subgroup (H.subgroupOf L)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hHL)
  have hde : d = e := hd.dimension_unique hHe
  exact hde ▸ he

theorem nilpotent_finiteDimension_of_rootCore [Countable G]
    (htf : HasNoNontrivialTorsion G) (H : Subgroup G) (hH : H.FG)
    (hroot : ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H) :
    HasFiniteIntegralCohomologicalDimension G := by
  obtain ⟨d, _, hd⟩ := nilpotent_rootCore_common_duality htf H hH hroot
  obtain ⟨T, hT, hfg, hcover⟩ := exists_fg_subgroup_exhaustion (G := G)
  let S (n : ℕ) := H ⊔ T n
  have hS : Monotone S := fun _ _ h => sup_le_sup_left (hT h) H
  have hSfg (n : ℕ) : (S n).FG := hH.sup (hfg n)
  have hScover (g : G) : ∃ n, g ∈ S n := by
    obtain ⟨n, hn⟩ := hcover g
    exact ⟨n, (show T n ≤ S n from le_sup_right) hn⟩
  exact ⟨d + 1, cohomologicalDimension_le_of_exhaustion S hS hScover d
    (fun n => (hd (S n) (hSfg n) le_sup_left).cohomologicalDimension)⟩

end PolycyclicRecognition

end

end OAI
