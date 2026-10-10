import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternFinite

namespace OAI

/-! # Exact passage from injective class assignments to the comparison sum -/

namespace Ostmann
open scoped Classical BigOperators

theorem sum_injective_assignments {A C M : Type*} [Fintype A] [Fintype C]
    [AddCommMonoid M] (F : (C → A) → M) :
    (∑ z : {z : C → A // Function.Injective z}, F z.val) =
      ∑ z : C → A, if Function.Injective z then F z else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun z : C → A => Function.Injective z))
    (by simp) F, Finset.sum_filter]

theorem sum_external_injective_pattern {A B C M : Type*}
    [Fintype A] [Fintype B] [Fintype C] [AddCommMonoid M]
    (F : (B → A) → (C → A) → M) :
    (∑ y : B → A, ∑ z : {z : C → A // Function.Injective z}, F y z.val) =
      ∑ x : B ⊕ C → A,
        if Function.Injective (fun c => x (.inr c)) then
          F (fun b => x (.inl b)) (fun c => x (.inr c)) else 0 := by
  simp_rw [sum_injective_assignments]
  have hp := Fintype.sum_prod_type (fun yz : (B → A) × (C → A) =>
    if Function.Injective yz.2 then F yz.1 yz.2 else 0)
  have he := (Equiv.sumArrowEquivProdArrow B C A).sum_comp
    (fun yz : (B → A) × (C → A) => if Function.Injective yz.2 then F yz.1 yz.2 else 0)
  simp only [finite_univ_canonical] at hp he ⊢
  exact hp.symm.trans he.symm

/-- This is an exact zero extension of the original injective class sum;
it is the form to which the independent-prior comparison applies. -/
theorem sum_external_injective_pattern_fin {A B C M : Type*}
    [Fintype A] [Fintype B] [Fintype C] [AddCommMonoid M] {N : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (F : (B → A) → (C → A) → M) :
    (∑ y : B → A, ∑ z : {z : C → A // Function.Injective z}, F y z.val) =
      ∑ x : Fin (N + 1) → A,
        if Function.Injective (fun c => x (e.symm (.inr c))) then
          F (fun b => x (e.symm (.inl b))) (fun c => x (e.symm (.inr c))) else 0 := by
  rw [sum_external_injective_pattern]
  have he := (Equiv.arrowCongr e (Equiv.refl A)).sum_comp
    (fun x : B ⊕ C → A => if Function.Injective (fun c => x (.inr c)) then
      F (fun b => x (.inl b)) (fun c => x (.inr c)) else 0)
  simp only [finite_univ_canonical] at he ⊢
  exact he.symm

end Ostmann

end OAI
