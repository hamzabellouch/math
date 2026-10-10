import Mathlib
import OAI.Probability.BinarySweep.Representations.IsotypicMoment

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Irrep
open Representation

section Algebra
variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

def conjugateRep (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) : Representation ℂ G W :=
  e.conjRingEquiv.toMonoidHom.comp ρ

def conjugateEquiv (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) : ρ.Equiv (conjugateRep ρ e) :=
  .mk e (by intro g; ext v; change e (ρ g v) = e (ρ g (e.symm (e v))); rw [e.symm_apply_apply])

lemma irreducible_equiv (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (e : ρ.Equiv σ) [ρ.IsIrreducible] : σ.IsIrreducible := by
  apply (irreducible_iff_isSimpleModule_asModule σ).mpr
  exact IsSimpleModule.congr (LinearEquiv.ofBijective
    (IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap) e.toLinearEquiv.bijective).symm

end Algebra
variable {G V W : Type*} [Group G] [Fintype G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W)

lemma equivalent_evenMoment (e : ρ.Equiv σ)
    (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) (hσ : ∀ g w, ‖σ g w‖ = ‖w‖)
    (p : G → ℂ) (q : ℕ) :
    evenMoment q (groupAverage ρ p) = evenMoment q (groupAverage σ p) := by
  have he : e.toLinearEquiv.conj (((groupAverage ρ p).adjoint * groupAverage ρ p)^q) =
      ((groupAverage σ p).adjoint * groupAverage σ p)^q := by
    ext w
    obtain ⟨v,rfl⟩ := e.toLinearEquiv.surjective w
    simp only [LinearEquiv.conj_apply,LinearMap.comp_apply,LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    exact (even_compatible ρ σ p hρ hσ q e.toIntertwiningMap v).symm
  unfold evenMoment
  rw [← he,LinearMap.trace_conj']

end BinaryCoordinateSweeps.Irrep

end

end OAI
