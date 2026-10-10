import OAI.GroupTheory.PolycyclicRecognition.Finiteness.SubgroupTopHomologyDegree
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.HomologyExhaustionFiniteness
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExhaustionOrientation
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.HomologyExhaustion
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RankOneEndomorphisms
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.HomologyRankOneLimit
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ExhaustionOrientationDetection

namespace OAI

/-! # Detecting finite generation of the nilpotent kernel by its top homology -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
attribute [local instance 2100] Linear.homModule
variable {G : Type} [Group G] [Countable G] [Group.IsNilpotent G]

theorem nilpotent_topHomology_finiteness_criterion
    (hG : HasFiniteIntegralCohomologicalDimension G) :
    ∃ d : ℕ, ∃ R : Rep ℤ G, Nonempty (R.V ≃ₗ[ℤ] ℤ) ∧
      (∀ A : Rep ℤ G, ∀ i, d < i → IsZero (groupHomology A i)) ∧
      (∃ x : groupHomology R d, x ≠ 0) ∧
      (∀ (z : ℤ) (x : groupHomology R d), z • x = 0 → z = 0 ∨ x = 0) ∧
      (∀ x y : groupHomology R d, x ≠ 0 → y ≠ 0 →
        ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y) ∧
      (Module.Finite ℤ (groupHomology R d) → Group.FG G) ∧
      (∀ A : Rep ℤ G, Nonempty (A.V ≃ₗ[ℤ] ℤ) →
        (∃ x : groupHomology A d, x ≠ 0) → Nonempty (R ≅ A)) := by
  obtain ⟨d, S, hS, hfg, hcover, hd, hindex⟩ :=
    exists_nilpotent_duality_exhaustion_finiteIndex hG
  obtain ⟨R, ⟨eR⟩, hR⟩ := exists_exhaustion_orientation S hS hcover d hd hindex
  have hdegree n m (hnm : n ≤ m) :
      ∃ (u : groupHomology (Rep.res (S n).subtype R) d ≃ₗ[ℤ] ℤ)
        (v : groupHomology (Rep.res (S m).subtype R) d ≃ₗ[ℤ] ℤ),
        ∀ x, v (groupHomology.map (Subgroup.inclusion (hS hnm))
          (subgroupRestrictionMap (hS hnm) R) d x) =
          (((S n).subgroupOf (S m)).index : ℤ) * u x := by
    let := hindex n m
    exact nestedSubgroup_topHomology_degree (hS hnm) R eR (hd m) (hR m)
  have hinj n m (hnm : n ≤ m) : Function.Injective
      (groupHomology.map (Subgroup.inclusion (hS hnm))
        (subgroupRestrictionMap (hS hnm) R) d) := by
    obtain ⟨u, v, h⟩ := hdegree n m hnm
    let := hindex n m
    exact indexCoordinate_injective _ u v _ Subgroup.FiniteIndex.index_ne_zero h
  have hrank n : Nonempty (groupHomology (Rep.res (S n).subtype R) d ≃ₗ[ℤ] ℤ) := by
    obtain ⟨e⟩ := hR n (Rep.res (S n).subtype R)
    exact ⟨e.trans (rankOneEndomorphismsEquiv (Rep.res (S n).subtype R) eR)⟩
  refine ⟨d, R, ⟨eR⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A i hi
    apply groupHomology_isZero_of_exhaustion S hS hcover A i
    intro n
    let := (hd n).cohomologicalDimension
    exact groupHomology_isZero_above_dimension d _ i hi
  · obtain ⟨e⟩ := hR 0 (Rep.res (S 0).subtype R)
    let e0 := e.trans (rankOneEndomorphismsEquiv (Rep.res (S 0).subtype R) eR)
    refine ⟨subgroupHomologyInclusion (S 0) R d (e0.symm 1), ?_⟩
    intro h
    have hi := subgroupHomologyInclusion_injective_of_stages S hS hcover R d hinj 0
    have hz : e0.symm 1 = 0 := hi (h.trans (map_zero _).symm)
    have he := congrArg e0 hz
    simp at he
  · exact homology_torsionFree_of_rankOne_stages S hS hcover R d hrank
      (subgroupHomologyInclusion_injective_of_stages S hS hcover R d hinj)
  · exact homology_commensurable_of_rankOne_stages S hS hcover R d hrank
  · intro hfinite
    let := hfinite
    obtain ⟨n, hn⟩ := exhaustion_stabilizes_of_finite_homology S hS hcover R d hindex hdegree
    exact ⟨hn ▸ hfg n⟩

  · rintro A ⟨eA⟩ ⟨x, hx⟩
    exact exhaustion_orientation_of_nonzero_top S hS hcover d R eR hR A eA x hx

end PolycyclicRecognition

end

end OAI
