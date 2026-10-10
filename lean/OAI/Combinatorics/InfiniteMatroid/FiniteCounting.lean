import Mathlib

namespace OAI

section
open Set
namespace InfiniteMatroidCounterexample

noncomputable def splitFunction {A B V : Type*} (e : A ↪ B) :
    (B → V) ≃ (A → V) × ({b : B // b ∉ Set.range e} → V) := by
  classical
  exact (Equiv.piEquivPiSubtypeProd (· ∈ Set.range e) (fun _ ↦ V)).trans
    (Equiv.prodCongr ((Equiv.ofInjective e e.injective).arrowCongr (Equiv.refl V)).symm (Equiv.refl _))

@[simp] lemma splitFunction_fst {A B V : Type*} (e : A ↪ B) (f : B → V) :
    (splitFunction e f).1 = fun a ↦ f (e a) := rfl

lemma card_restriction {A B V : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Fintype V]
    (e : A ↪ B) (P : (A → V) → Prop) [DecidablePred P] :
    Fintype.card {f : B → V // P (fun a ↦ f (e a))} =
      Fintype.card {g : A → V // P g} * Fintype.card V ^ (Fintype.card B - Fintype.card A) := by
  classical
  let fs := splitFunction (V := V) e
  have he := (fs.subtypeEquiv (p := fun f ↦ P (fun a ↦ f (e a)))
      (q := fun f ↦ P f.1) (fun f ↦ by simp [fs])).trans Equiv.prodSubtypeFstEquivSubtypeProd
  have hc : Fintype.card {b : B // b ∈ Set.range e} = Fintype.card A :=
    (Fintype.card_congr (Equiv.ofInjective e e.injective)).symm
  rw [Fintype.card_congr he, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_subtype_compl, hc]

lemma function_density_restriction {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (P : (A → Bool) → Prop) [DecidablePred P] :
    (Fintype.card {f : B → Bool // P (fun a ↦ f (e a))} : ℝ) / Fintype.card (B → Bool) =
      (Fintype.card {g : A → Bool // P g} : ℝ) / Fintype.card (A → Bool) := by
  rw [card_restriction]
  simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hle : Fintype.card A ≤ Fintype.card B := Fintype.card_le_of_injective e e.injective
  have heq : (2:ℝ) ^ Fintype.card B = 2 ^ Fintype.card A * 2 ^ (Fintype.card B - Fintype.card A) := by
    rw [← pow_add, Nat.add_sub_of_le hle]
  rw [heq]
  field_simp

end InfiniteMatroidCounterexample
end

end OAI
