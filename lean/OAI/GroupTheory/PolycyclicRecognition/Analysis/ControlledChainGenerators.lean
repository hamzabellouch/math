import OAI.GroupTheory.PolycyclicRecognition.Analysis.ControlledChainRepresentation
import Mathlib.Data.Fintype.Pi

namespace OAI

/-! # Finite group-ring generators at a fixed scale

Normalizing the first vertex to the identity leaves only finitely many tuples.
Their translates generate all chains at the chosen scale.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped MonoidAlgebra
variable {R G : Type} [CommRing R] [Group G] {n : ℕ}

theorem finite_normalizedControlledTuples (S : Set G) (hS : S.Finite) :
    {x : Fin (n + 1) → G | IsControlledTuple S x ∧ x 0 = 1}.Finite := by
  apply (Set.Finite.pi' (fun _ : Fin (n + 1) => hS)).subset
  intro x hx i
  simpa only [hx.2, inv_one, one_mul] using hx.1 0 i

theorem controlledChainSubrepresentation_fg (S : Set G) (hS : S.Finite) :
    ((controlledChainSubrepresentation (R := R) (n := n) S).asSubmodule).FG := by
  let ρ := Representation.ofMulAction R G (Fin (n + 1) → G)
  let A := {x : Fin (n + 1) → G | IsControlledTuple S x ∧ x 0 = 1}
  let B : Set ρ.asModule := (fun x => ρ.asModuleEquiv.symm
    (MonoidAlgebra.single x 1)) '' A
  let N : Submodule R[G] ρ.asModule := Submodule.span R[G] B
  have hB : B.Finite := (finite_normalizedControlledTuples S hS).image _
  have hNQ : N ≤ (controlledChainSubrepresentation (R := R) (n := n) S).asSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    exact controlledChainSpan_single hx.1
  have hscalar : controlledChainSpan R G n S ≤
      (Subrepresentation.ofSubmodule' N).toSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    let y := (x 0)⁻¹ • x
    have hy : y ∈ A := by
      refine ⟨hx.left_translate _, ?_⟩
      simp [y]
    have hmem : ρ.asModuleEquiv.symm (MonoidAlgebra.single y 1) ∈ N :=
      Submodule.subset_span ⟨y, hy, rfl⟩
    have hxy : ρ (x 0) (MonoidAlgebra.single y 1) = MonoidAlgebra.single x 1 := by
      rw [Representation.ofMulAction_single]
      congr 1
      funext i
      simp [y]
    have hm := N.smul_mem (MonoidAlgebra.of R G (x 0)) hmem
    rw [← Representation.asModuleEquiv_symm_map_rho, hxy] at hm
    exact hm
  have hQN : (controlledChainSubrepresentation (R := R) (n := n) S).asSubmodule ≤ N :=
    fun _ hx => hscalar hx
  rw [le_antisymm hQN hNQ]
  exact Submodule.fg_span hB

end PolycyclicRecognition

end

end OAI
