import OAI.GroupTheory.PolycyclicRecognition.Analysis.BarChainExhaustion
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.FiniteDimensionHomology
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentExhaustionDimension

namespace OAI

/-! # Homology vanishing passes from an exhaustive sequence of subgroups

The proof uses finite support directly: a cycle lifts to a stage, injectivity
of its bar inclusion detects that it is a cycle there, and a local filling
maps to a global filling. No spectral sequence or colimit hypothesis is used.
-/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
variable {G : Type} [Group G]

theorem groupHomology_isZero_of_exhaustion (S : ℕ → Subgroup G)
    (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n)
    (A : Rep ℤ G) (i : ℕ)
    (hlocal : ∀ n, IsZero (groupHomology (Rep.res (S n).subtype A) i)) :
    IsZero (groupHomology A i) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro z hz
  obtain ⟨n, w, hw⟩ := exists_barChain_in_subgroup S hS hcover A i z
  let F := subgroupBarInclusion (S n) A
  let C := groupHomology.inhomogeneousChains (Rep.res (S n).subtype A)
  let j := (ComplexShape.down ℕ).next i
  let k := (ComplexShape.down ℕ).prev i
  have hwcycle : C.d i j w = 0 := by
    apply subgroupBarInclusion_injective (S n) A j
    have hc := congrArg (fun f => f.hom w) (F.comm i j)
    change F.f j (C.d i j w) = F.f j 0
    rw [map_zero]
    change (groupHomology.inhomogeneousChains A).d i j (F.f i w) =
      F.f j (C.d i j w) at hc
    rw [← hc, hw]
    exact hz
  have hex : (C.sc i).Exact :=
    (C.exactAt_iff_isZero_homology i).mpr (hlocal n)
  obtain ⟨v, hv⟩ := (ShortComplex.moduleCat_exact_iff _).mp hex w hwcycle
  refine ⟨F.f k v, ?_⟩
  have hc := congrArg (fun f => f.hom v) (F.comm k i)
  change (groupHomology.inhomogeneousChains A).d k i (F.f k v) = z
  change (groupHomology.inhomogeneousChains A).d k i (F.f k v) =
    F.f i (C.d k i v) at hc
  change C.d k i v = w at hv
  rw [hc, hv]
  exact hw

theorem nilpotent_exists_uniform_homology_bound [Countable G] [Group.IsNilpotent G]
    (hG : HasFiniteIntegralCohomologicalDimension G) :
    ∃ d : ℕ, ∀ (A : Rep ℤ G) (i : ℕ), d < i → IsZero (groupHomology A i) := by
  obtain ⟨d, S, hS, _, hcover, hd⟩ := exists_nilpotent_duality_exhaustion hG
  refine ⟨d, fun A i hi => groupHomology_isZero_of_exhaustion S hS hcover A i ?_⟩
  intro n
  let := (hd n).cohomologicalDimension
  exact groupHomology_isZero_above_dimension d _ i hi

end PolycyclicRecognition

end

end OAI
