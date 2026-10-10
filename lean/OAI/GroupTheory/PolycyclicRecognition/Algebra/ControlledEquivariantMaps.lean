import OAI.GroupTheory.PolycyclicRecognition.Analysis.ControlledChainGenerators

namespace OAI

/-! # Equivariant maps have uniform control on each finite scale -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped MonoidAlgebra
variable {G : Type} [Group G] {n m : ℕ}

theorem equivariant_controlledChainImage
    (f : Rep.ofMulAction ℤ G (Fin (n + 1) → G) ⟶
      Rep.ofMulAction ℤ G (Fin (m + 1) → G))
    (S : Set G) (hS : S.Finite) :
    ∃ T : Set G, T.Finite ∧ ∀ c ∈ controlledChainSpan ℤ G n S,
      f.hom c ∈ controlledChainSpan ℤ G m T := by
  let ρ := Representation.ofMulAction ℤ G (Fin (n + 1) → G)
  let σ := Representation.ofMulAction ℤ G (Fin (m + 1) → G)
  let Q := (controlledChainSubrepresentation (R := ℤ) (n := n) S).asSubmodule
  obtain ⟨s, hsfin, hs⟩ := Submodule.fg_def.mp (controlledChainSubrepresentation_fg
    (R := ℤ) (n := n) S hS)
  obtain ⟨T, hT, hgen⟩ := exists_common_controlledChainScale
    (hsfin.image (fun a => f.hom (ρ.asModuleEquiv a)))
  let fM := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ f.hom
  let Q' := (controlledChainSubrepresentation (R := ℤ) (n := m) T).asSubmodule
  have hle : Q ≤ Q'.comap fM := by
    rw [show Q = Submodule.span ℤ[G] s from hs.symm]
    apply Submodule.span_le.mpr
    intro a ha
    exact hgen _ ⟨a, ha, rfl⟩
  exact ⟨T, hT, fun c hc => hle (show ρ.asModuleEquiv.symm c ∈ Q from hc)⟩

theorem standardComplex_boundary_apply
    (c : MonoidAlgebra ℤ (Fin (n + 2) → G)) :
    ((Rep.standardComplex ℤ G).d (n + 1) n).hom c =
      (tupleChainComplex ℤ G).d (n + 1) n c := by
  change ((Rep.standardComplex ℤ G).d (n + 1) n).hom.toLinearMap c = _
  rw [Rep.standardComplex.d_eq, ← tupleChainComplex_boundary_linear]
  rfl

end PolycyclicRecognition

end

end OAI
