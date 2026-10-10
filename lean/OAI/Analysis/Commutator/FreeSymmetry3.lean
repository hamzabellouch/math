import Mathlib
import OAI.Analysis.Commutator.CrossingPairings

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.Pairing

lemma not_crosses_iff_same_side {k l : ℕ} (σ : Pairing (TailSlots k l)) :
    ¬ Crosses σ ↔ (∃ a b : Fin k, σ (.inl a) = .inl b) ∨
      (∃ a b : Fin l, σ (.inr a) = .inr b) := by
  constructor
  · intro hn
    by_contra h
    apply hn
    constructor
    · intro a
      cases he : σ (.inl a) with
      | inl b => exact (h (Or.inl ⟨a, b, he⟩)).elim
      | inr b => exact ⟨b, rfl⟩
    · intro a
      cases he : σ (.inr a) with
      | inl b => exact ⟨b, rfl⟩
      | inr b => exact (h (Or.inr ⟨a, b, he⟩)).elim
  · rintro (⟨a, b, he⟩ | ⟨a, b, he⟩) hc
    · obtain ⟨j, hj⟩ := hc.1 a
      rw [he] at hj
      cases hj
    · obtain ⟨j, hj⟩ := hc.2 a
      rw [he] at hj
      cases hj

end Kadison.Pairing
end

end OAI
