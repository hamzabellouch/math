import OAI.GroupTheory.PolycyclicRecognition.Algebra.RelativeCommutatorSeries
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ActionDepth

namespace OAI

/-! # Linear control of iterated commutators in a normal subgroup

An equivariant homomorphism from a normal subgroup into an additive vector
space sends action commutators to action differences. Vanishing of the
linear action filtration therefore puts the relative commutator series in
the kernel of that homomorphism.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped commutatorElement
variable {G k V : Type} [Group G] [Field k] [AddCommGroup V] [Module k V]

def linearPreimageSubgroup {N : Subgroup G} (π : N →* Multiplicative V)
    (W : Submodule k V) : Subgroup N where
  carrier := {a | (π a).toAdd ∈ W}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change (π (a * b)).toAdd ∈ W
    simpa only [map_mul, toAdd_mul] using W.add_mem ha hb
  inv_mem' := by
    intro a ha
    change (π a⁻¹).toAdd ∈ W
    simpa only [map_inv, toAdd_inv] using W.neg_mem ha

theorem relativeCommutatorSeries_le_linearFiltration
    (K N : Subgroup G) [N.Normal] (ρ : G →* (V ≃ₗ[k] V))
    (π : N →* Multiplicative V)
    (heq : ∀ g : G, ∀ a : N,
      (π (MulAut.conjNormal (H := N) g a)).toAdd = ρ g (π a).toAdd) (n : ℕ) :
    relativeCommutatorSeries K N n ≤
      (linearPreimageSubgroup π (linearActionFiltration
        (fun g : K => (ρ g).toLinearMap - 1) n)).map N.subtype := by
  let D := fun g : K => (ρ g).toLinearMap - 1
  induction n with
  | zero =>
    intro a ha
    refine ⟨⟨a, ha⟩, ?_, rfl⟩
    change (π ⟨a, ha⟩).toAdd ∈ (⊤ : Submodule k V)
    trivial
  | succ n ih =>
    apply Subgroup.commutator_le.mpr
    intro g hg a ha
    obtain ⟨a, hav, rfl⟩ := ih ha
    let b : N := MulAut.conjNormal (H := N) g a * a⁻¹
    have hb : (π b).toAdd = D ⟨g, hg⟩ (π a).toAdd := by
      simp only [b, map_mul, map_inv, toAdd_mul, toAdd_inv, heq]
      change ρ g (π a).toAdd + -(π a).toAdd = ρ g (π a).toAdd - (π a).toAdd
      exact (sub_eq_add_neg _ _).symm
    refine ⟨b, ?_, rfl⟩
    change (π b).toAdd ∈ linearActionFiltration D (n + 1)
    rw [hb]
    exact ActionDepth.generator (D := D) (⟨g, hg⟩ : K) n _ hav

theorem relativeCommutatorSeries_le_kernel_of_linearFiltration
    (K N : Subgroup G) [N.Normal] (ρ : G →* (V ≃ₗ[k] V))
    (π : N →* Multiplicative V)
    (heq : ∀ g : G, ∀ a : N,
      (π (MulAut.conjNormal (H := N) g a)).toAdd = ρ g (π a).toAdd)
    (c : ℕ) (hc : linearActionFiltration (fun g : K => (ρ g).toLinearMap - 1) c = ⊥) :
    relativeCommutatorSeries K N c ≤ π.ker.map N.subtype := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := relativeCommutatorSeries_le_linearFiltration K N ρ π heq c hg
  refine ⟨a, ?_, rfl⟩
  change (π a).toAdd ∈ linearActionFiltration (fun g : K => (ρ g).toLinearMap - 1) c at ha
  rw [hc, Submodule.mem_bot] at ha
  change π a = 1
  exact Multiplicative.toAdd.injective ha

end PolycyclicRecognition

end

end OAI
