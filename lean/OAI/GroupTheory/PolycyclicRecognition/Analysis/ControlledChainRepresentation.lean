import OAI.GroupTheory.PolycyclicRecognition.Analysis.ControlledFiniteChains
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteRepresentationQuotients
import Mathlib.RepresentationTheory.Subrepresentation

namespace OAI

/-! # Equivariant control of finite chains

Left translation preserves every relative-position bound. Consequently an
equivariant image of a finitely generated representation lies at one finite
scale in the homogeneous standard chains.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped MonoidAlgebra
variable {R G : Type} [CommRing R] [Group G] {n : ℕ}

theorem IsControlledTuple.left_translate {S : Set G} {x : Fin (n + 1) → G}
    (hx : IsControlledTuple S x) (g : G) : IsControlledTuple S (g • x) := by
  intro i j
  simpa using hx i j

def controlledChainSubrepresentation (S : Set G) :
    Subrepresentation (Representation.ofMulAction R G (Fin (n + 1) → G)) where
  toSubmodule := controlledChainSpan R G n S
  apply_mem_toSubmodule g := by
    intro c hc
    apply controlledChainSpan_map (Representation.ofMulAction R G _ g) _ hc
    intro x hx
    rw [Representation.ofMulAction_single]
    exact controlledChainSpan_single (hx.left_translate g)

theorem exists_common_controlledChainScale
    {C : Set (MonoidAlgebra R (Fin (n + 1) → G))} (hC : C.Finite) :
    ∃ S : Set G, S.Finite ∧ ∀ c ∈ C, c ∈ controlledChainSpan R G n S := by
  induction C, hC using Set.Finite.induction_on with
  | empty => exact ⟨∅, Set.finite_empty, by simp⟩
  | @insert c C hc hC ih =>
    obtain ⟨S, hS, hc⟩ := exists_controlledChainScale c
    obtain ⟨T, hT, hCT⟩ := ih
    refine ⟨S ∪ T, hS.union hT, ?_⟩
    intro x hx
    rcases hx with rfl | hx
    · exact controlledChainSpan_mono Set.subset_union_left hc
    · exact controlledChainSpan_mono Set.subset_union_right (hCT x hx)

theorem finiteRepresentation_range_controlled (A : Rep ℤ G)
    (hA : IntegralRepresentationFinite G A)
    (f : A ⟶ Rep.ofMulAction ℤ G (Fin (n + 1) → G)) :
    ∃ S : Set G, S.Finite ∧ ∀ a : A, f.hom a ∈ controlledChainSpan ℤ G n S := by
  let : Module ℤ A := A.hV2
  let : Module.Finite ℤ[G] A.ρ.asModule := hA
  obtain ⟨s, hsfin, hs⟩ := Submodule.fg_def.mp (Module.Finite.fg_top (R := ℤ[G])
    (M := A.ρ.asModule))
  obtain ⟨S, hS, hgen⟩ := exists_common_controlledChainScale
    (hsfin.image (fun a => f.hom (A.ρ.asModuleEquiv a)))
  let fM := Representation.IntertwiningMap.equivLinearMapAsModule A.ρ
    (Representation.ofMulAction ℤ G (Fin (n + 1) → G)) f.hom
  let Q := (controlledChainSubrepresentation (R := ℤ) (n := n) S).asSubmodule
  have hle : (⊤ : Submodule ℤ[G] A.ρ.asModule) ≤ Q.comap fM := by
    rw [← hs]
    apply Submodule.span_le.mpr
    intro a ha
    exact hgen _ ⟨a, ha, rfl⟩
  refine ⟨S, hS, fun a => ?_⟩
  exact hle (show A.ρ.asModuleEquiv.symm a ∈ (⊤ : Submodule ℤ[G] A.ρ.asModule)
    from Submodule.mem_top)

end PolycyclicRecognition

end

end OAI
