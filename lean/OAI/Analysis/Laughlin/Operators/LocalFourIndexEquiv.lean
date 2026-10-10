import OAI.Analysis.Laughlin.FourBody.TransferConjugation

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

abbrev EmbeddedLocalFourIndex (Q D : ℕ) :=
  {b : Fin (D+1) × Fin (Q+1) × Fin (Q+1) // b.1.val+b.2.1.val+b.2.2.val=D ∧ b.2.1<b.2.2}

def localFourIndexEquiv (Q D : ℕ) (hDQ : D ≤ Q) :
    LocalFourIndex D ≃ EmbeddedLocalFourIndex Q D where
  toFun b := ⟨(b.val.1,⟨b.val.2.1.val,by omega⟩,⟨b.val.2.2.val,by omega⟩),b.property⟩
  invFun b := ⟨(b.val.1,⟨b.val.2.1.val,by have := b.property.1; omega⟩,
    ⟨b.val.2.2.val,by have := b.property.1; omega⟩),b.property⟩
  left_inv b := by cases b; rfl
  right_inv b := by cases b; rfl

theorem localFourIndex_sum {M : Type*} [AddCommMonoid M] (Q D : ℕ) (hDQ : D ≤ Q)
    (f : ℕ → Fin (Q+1) → Fin (Q+1) → M) :
    (∑ p : Fin (D+1), ∑ j : Fin (Q+1), ∑ k : Fin (Q+1),
      if p.val+j.val+k.val=D ∧ j<k then f p.val j k else 0) =
      ∑ b : LocalFourIndex D, f b.val.1.val ⟨b.val.2.1.val,by omega⟩ ⟨b.val.2.2.val,by omega⟩ := by
  classical
  let P := fun b : Fin (D+1) × Fin (Q+1) × Fin (Q+1) =>
    b.1.val+b.2.1.val+b.2.2.val=D ∧ b.2.1<b.2.2
  have he : (∑ b : Fin (D+1) × Fin (Q+1) × Fin (Q+1),
      if P b then f b.1.val b.2.1 b.2.2 else 0) =
      ∑ p : Fin (D+1), ∑ j : Fin (Q+1), ∑ k : Fin (Q+1),
        if p.val+j.val+k.val=D ∧ j<k then f p.val j k else 0 := by
    simp only [Fintype.sum_prod_type,P]
  rw [← he,← Finset.sum_filter,Finset.sum_subtype (p := P) _ (by simp)]
  exact (localFourIndexEquiv Q D hDQ).sum_comp
    (fun b => f b.val.1.val b.val.2.1 b.val.2.2) |>.symm

end Laughlin.Spin

end OAI
