import Mathlib
import OAI.Probability.BinarySweep.Representations.MultiplicityBound

namespace OAI

noncomputable section
open scoped BigOperators Classical TensorProduct

namespace BinaryCoordinateSweeps.Irrep
open Representation

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [ρ.IsIrreducible]

def evaluationToIsotypic : V ⊗[ℂ] IntertwiningMap ρ σ →ₗ[ℂ] isotypicSpan ρ σ :=
  (evaluation ρ σ).codRestrict _ (fun x => by
    rw [← evaluation_range]; exact ⟨x,rfl⟩)

lemma evaluationToIsotypic_bijective : Function.Bijective (evaluationToIsotypic ρ σ) := by
  constructor
  · intro x y h
    apply evaluation_injective ρ σ
    exact congrArg Subtype.val h
  · intro y
    have hy : y.val ∈ LinearMap.range (evaluation ρ σ) := by
      rw [evaluation_range]; exact y.property
    obtain ⟨x,hx⟩ := hy
    exact ⟨x,Subtype.ext hx⟩

def evaluationEquiv : V ⊗[ℂ] IntertwiningMap ρ σ ≃ₗ[ℂ] isotypicSpan ρ σ :=
  LinearEquiv.ofBijective (evaluationToIsotypic ρ σ) (evaluationToIsotypic_bijective ρ σ)

omit [Fintype G] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [ρ.IsIrreducible] in
lemma isotypic_invariant_of_compatible (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W)
    (hAB : ∀ f : IntertwiningMap ρ σ, ∀ v : V, B (f v) = f (A v)) :
    ∀ w ∈ isotypicSpan ρ σ, B w ∈ isotypicSpan ρ σ := by
  intro w hw
  apply Submodule.iSup_induction (fun f : IntertwiningMap ρ σ => LinearMap.range f.toLinearMap)
    (motive := fun w => B w ∈ isotypicSpan ρ σ) hw
  · intro f w hw
    obtain ⟨v,rfl⟩ := hw
    rw [show f.toLinearMap v = f v from rfl,hAB]
    exact (le_iSup (fun f : IntertwiningMap ρ σ => LinearMap.range f.toLinearMap) f) ⟨A v,rfl⟩
  · simp
  · intro x y hx hy; simpa only [map_add] using Submodule.add_mem _ hx hy

theorem isotypic_trace (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W)
    (hAB : ∀ f : IntertwiningMap ρ σ, ∀ v : V, B (f v) = f (A v)) :
    LinearMap.trace ℂ (isotypicSpan ρ σ)
      (B.restrict (isotypic_invariant_of_compatible ρ σ A B hAB)) =
    (Module.finrank ℂ (IntertwiningMap ρ σ) : ℂ) * LinearMap.trace ℂ V A := by
  let e := evaluationEquiv ρ σ
  let C := B.restrict (isotypic_invariant_of_compatible ρ σ A B hAB)
  have he : e.symm.conj C = TensorProduct.map A (LinearMap.id :
      IntertwiningMap ρ σ →ₗ[ℂ] IntertwiningMap ρ σ) := by
    apply TensorProduct.ext'
    intro v f
    apply e.injective
    change e (e.symm (C (e (v ⊗ₜ[ℂ] f)))) = e (A v ⊗ₜ[ℂ] f)
    rw [e.apply_symm_apply]
    apply Subtype.ext
    exact hAB f v
  have ht := LinearMap.trace_conj' C e.symm
  rw [he,LinearMap.trace_tensorProduct',LinearMap.trace_id] at ht
  exact ht.symm.trans (mul_comm _ _)

end BinaryCoordinateSweeps.Irrep

end

end OAI
