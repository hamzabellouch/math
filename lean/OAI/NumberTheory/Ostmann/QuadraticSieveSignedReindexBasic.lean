import OAI.NumberTheory.Ostmann.QuadraticSieveSignedSupport
import OAI.NumberTheory.Ostmann.QuadraticSieveSquarefreeKernel

namespace OAI

namespace Ostmann.QuadraticSieve

def OddSquarefreeIndex := {v : ℕ // Odd v ∧ Squarefree v}

def squarefreeParityMap : OddSquarefreeIndex ⊕ OddSquarefreeIndex → {v : ℕ // Squarefree v}
  | .inl v => ⟨v.val, v.property.2⟩
  | .inr v => ⟨2 * v.val, Nat.squarefree_mul_iff.mpr
      ⟨Nat.coprime_two_left.mpr v.property.1, Nat.prime_two.squarefree, v.property.2⟩⟩

noncomputable def squarefreeParityEquiv :
    (OddSquarefreeIndex ⊕ OddSquarefreeIndex) ≃ {v : ℕ // Squarefree v} := by
  apply Equiv.ofBijective squarefreeParityMap
  constructor
  · intro x y h
    have he := congrArg Subtype.val h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        exact congrArg Sum.inl (Subtype.ext he)
      | inr y =>
        change x.val = 2 * y.val at he
        have ho := x.property.1
        rw [he, Nat.odd_mul] at ho
        norm_num at ho
    | inr x =>
      cases y with
      | inl y =>
        change 2 * x.val = y.val at he
        have ho := y.property.1
        rw [← he, Nat.odd_mul] at ho
        norm_num at ho
      | inr y =>
        change 2 * x.val = 2 * y.val at he
        exact congrArg Sum.inr (Subtype.ext (by omega))
  · intro n
    obtain ⟨e, v, he, hv1, hvn, hvo, hvsq, hev⟩ := squarefree_odd_factor n.property
    rcases he with rfl | rfl
    · exact ⟨Sum.inl ⟨v, hvo, hvsq⟩, Subtype.ext (by simpa only [squarefreeParityMap, one_mul] using hev.symm)⟩
    · exact ⟨Sum.inr ⟨v, hvo, hvsq⟩, Subtype.ext hev.symm⟩

@[simp] theorem squarefreeParityEquiv_inl (v : OddSquarefreeIndex) :
    (squarefreeParityEquiv (Sum.inl v)).val = v.val := rfl

@[simp] theorem squarefreeParityEquiv_inr (v : OddSquarefreeIndex) :
    (squarefreeParityEquiv (Sum.inr v)).val = 2 * v.val := rfl

attribute [irreducible] squarefreeParityEquiv

theorem tsum_squarefree_eq_odd_add_twice (g : ℕ → ℂ)
    (hg : Summable (fun v : {v : ℕ // Squarefree v} => g v.val)) :
    (∑' v : {v : ℕ // Squarefree v}, g v.val) =
      (∑' v : OddSquarefreeIndex, g v.val) + ∑' v : OddSquarefreeIndex, g (2 * v.val) := by
  have hs : Summable (fun p : OddSquarefreeIndex ⊕ OddSquarefreeIndex =>
      g (squarefreeParityEquiv p).val) := hg.comp_injective squarefreeParityEquiv.injective
  have hl : Summable (fun b : OddSquarefreeIndex => g (squarefreeParityEquiv (Sum.inl b)).val) :=
    hs.comp_injective Sum.inl_injective
  have hr : Summable (fun b : OddSquarefreeIndex => g (squarefreeParityEquiv (Sum.inr b)).val) :=
    hs.comp_injective Sum.inr_injective
  rw [← squarefreeParityEquiv.tsum_eq (fun v => g v.val)]
  simpa only [squarefreeParityEquiv_inl, squarefreeParityEquiv_inr] using
    Summable.tsum_sum (f := fun p => g (squarefreeParityEquiv p).val) hl hr

end Ostmann.QuadraticSieve

end OAI
