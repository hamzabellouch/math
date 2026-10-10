import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTBandProducts
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

/-! Exact inclusion-exclusion for a finite Euler product partitioned into
disjoint prime bands.  No analytic estimate is used in this identity. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma mrt_band_complement {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (J I : Finset κ)
    (P : κ → Finset ι) (hI : I ⊆ J) (hsub : ∀ j ∈ J, P j ⊆ S)
    (hdis : Set.PairwiseDisjoint (J : Set κ) P) :
    S \ I.biUnion P = (S \ J.biUnion P) ∪ (J \ I).biUnion P := by
  ext p
  constructor
  · intro hp
    rcases mem_sdiff.mp hp with ⟨hpS, hpI⟩
    by_cases hpJ : p ∈ J.biUnion P
    · obtain ⟨j, hj, hpj⟩ := mem_biUnion.mp hpJ
      have hjI : j ∉ I := fun hi => hpI (mem_biUnion.mpr ⟨j, hi, hpj⟩)
      exact mem_union_right _ (mem_biUnion.mpr ⟨j, mem_sdiff.mpr ⟨hj, hjI⟩, hpj⟩)
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hpS, hpJ⟩)
  · intro hp
    rcases mem_union.mp hp with hp | hp
    · rcases mem_sdiff.mp hp with ⟨hpS, hpJ⟩
      refine mem_sdiff.mpr ⟨hpS, ?_⟩
      intro hpI
      obtain ⟨j, hj, hpj⟩ := mem_biUnion.mp hpI
      exact hpJ (mem_biUnion.mpr ⟨j, hI hj, hpj⟩)
    · obtain ⟨j, hj, hpj⟩ := mem_biUnion.mp hp
      rcases mem_sdiff.mp hj with ⟨hjJ, hjI⟩
      refine mem_sdiff.mpr ⟨hsub j hjJ hpj, ?_⟩
      intro hpI
      obtain ⟨i, hi, hpi⟩ := mem_biUnion.mp hpI
      have hne : i ≠ j := fun he => hjI (he ▸ hi)
      exact Finset.disjoint_left.mp (hdis (hI hi) hjJ hne) hpi hpj

lemma mrt_band_complement_disjoint {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (J I : Finset κ)
    (P : κ → Finset ι) :
    Disjoint (S \ J.biUnion P) ((J \ I).biUnion P) := by
  apply Finset.disjoint_left.mpr
  intro p hp hp'
  obtain ⟨j, hj, hpj⟩ := mem_biUnion.mp hp'
  exact (mem_sdiff.mp hp).2 (mem_biUnion.mpr ⟨j, (mem_sdiff.mp hj).1, hpj⟩)

theorem mrt_band_complement_product {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (J I : Finset κ)
    (P : κ → Finset ι) (a : ι → ℂ) (hI : I ⊆ J)
    (hsub : ∀ j ∈ J, P j ⊆ S) (hdis : Set.PairwiseDisjoint (J : Set κ) P) :
    (∏ p ∈ S \ I.biUnion P, a p) =
      (∏ p ∈ S \ J.biUnion P, a p) * ∏ j ∈ J \ I, ∏ p ∈ P j, a p := by
  rw [mrt_band_complement S J I P hI hsub hdis,
    prod_union (mrt_band_complement_disjoint S J I P)]
  congr 1
  exact prod_biUnion (fun i hi j hj hij =>
    hdis (mem_sdiff.mp hi).1 (mem_sdiff.mp hj).1 hij)

/-- The alternating masked Euler products factor exactly into one
unrestricted complement and one nonempty factor for each band. -/
theorem mrt_euler_inclusion_exclusion {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (J : Finset κ)
    (P : κ → Finset ι) (a : ι → ℂ)
    (hsub : ∀ j ∈ J, P j ⊆ S) (hdis : Set.PairwiseDisjoint (J : Set κ) P) :
    (∑ I ∈ J.powerset, (-1 : ℂ) ^ I.card * ∏ p ∈ S \ I.biUnion P, a p) =
      (∏ p ∈ S \ J.biUnion P, a p) *
        ∏ j ∈ J, ((∏ p ∈ P j, a p) - 1) := by
  rw [prod_sub, mul_sum]
  apply sum_congr rfl
  intro I hI
  rw [mrt_band_complement_product S J I P a (mem_powerset.mp hI) hsub hdis,
    prod_const_one, mul_one]
  ring

end TwoPointCorrelations

end OAI
