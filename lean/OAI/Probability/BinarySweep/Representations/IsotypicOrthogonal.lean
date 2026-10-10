import Mathlib
import OAI.Probability.BinarySweep.Representations.IsotypicMoment

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W Z : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [FiniteDimensional ℂ Z]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (τ : Representation ℂ G Z)

def adjointIntertwiner (hρ : ∀ g v, ‖ρ g v‖=‖v‖) (hσ : ∀ g w, ‖σ g w‖=‖w‖)
    (f : IntertwiningMap ρ σ) : IntertwiningMap σ ρ where
  toLinearMap := f.toLinearMap.adjoint
  isIntertwining' g := by
    have he := congrArg LinearMap.adjoint (f.isIntertwining' g⁻¹)
    simpa only [LinearMap.adjoint_comp,unitary_rep_adjoint ρ hρ,
      unitary_rep_adjoint σ hσ,inv_inv] using he.symm

omit [Fintype G] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
lemma intertwiner_zero_of_inequivalent [ρ.IsIrreducible] [σ.IsIrreducible]
    (h : ¬ Nonempty (ρ.Equiv σ)) (f : IntertwiningMap ρ σ) : f=0 := by
  exact (IsIrreducible.bijective_or_eq_zero f).resolve_left (fun hf => h ⟨f.ofBijective hf⟩)

omit [Fintype G] [FiniteDimensional ℂ W] in
theorem isotypic_orthogonal [ρ.IsIrreducible] [σ.IsIrreducible]
    (hρ : ∀ g v, ‖ρ g v‖=‖v‖) (_hσ : ∀ g w, ‖σ g w‖=‖w‖)
    (hτ : ∀ g z, ‖τ g z‖=‖z‖)
    (hne : ¬ Nonempty (ρ.Equiv σ)) :
    isotypicSpan σ τ ≤ (isotypicSpan ρ τ)ᗮ := by
  unfold isotypicSpan
  rw [← Submodule.iInf_orthogonal]
  apply iSup_le
  intro f
  rw [le_iInf_iff]
  intro g
  rintro _ ⟨w,rfl⟩
  rw [Submodule.mem_orthogonal]
  rintro _ ⟨v,rfl⟩
  have hn : ¬Nonempty (σ.Equiv ρ) := fun ⟨e⟩ => hne ⟨e.symm⟩
  have hz := intertwiner_zero_of_inequivalent σ ρ hn
    ((adjointIntertwiner ρ τ hρ hτ g).comp f)
  have he := congrArg (fun F : IntertwiningMap σ ρ => F w) hz
  change g.toLinearMap.adjoint (f.toLinearMap w) = 0 at he
  rw [← LinearMap.adjoint_inner_right,he]
  simp

end BinaryCoordinateSweeps.Irrep

end

end OAI
