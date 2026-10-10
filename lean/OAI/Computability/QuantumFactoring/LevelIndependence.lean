import Mathlib

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


open scoped BigOperators
namespace ExactQuantumFactoring

noncomputable def equalLevelEquiv {A B T : Type*} (f : A → T) (g : B → T) :
    {x : A × B // f x.1 = g x.2} ≃ Σ b : B, {a : A // f a = g b} where
  toFun x := ⟨x.1.2, x.1.1, x.2⟩
  invFun x := ⟨(x.2.1,x.1),x.2.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

/-- Counting the equality of two independent levels by fibers, with no
assumption about an approximately uniform distribution. -/
theorem equalLevel_card {A B T : Type*} [Fintype A] [Fintype B]
    (f : A → T) (g : B → T) [DecidableEq T] :
    Fintype.card {x : A × B // f x.1 = g x.2} = ∑ b : B, Fintype.card {a : A // f a = g b} := by
  classical
  rw [Fintype.card_congr (equalLevelEquiv f g), Fintype.card_sigma]

theorem twice_equalLevel_card_le {A B T : Type*} [Fintype A] [Fintype B]
    (f : A → T) (g : B → T) [DecidableEq T]
    (hf : ∀ t, 2 * Fintype.card {a : A // f a = t} ≤ Fintype.card A) :
    2 * Fintype.card {x : A × B // f x.1 = g x.2} ≤ Fintype.card A * Fintype.card B := by
  classical
  rw [equalLevel_card, Finset.mul_sum]
  calc
    _ ≤ ∑ _ : B, Fintype.card A := Finset.sum_le_sum (fun b _ => hf (g b))
    _ = _ := by simp [mul_comm]

noncomputable def allEqualLevelEquiv {ι T : Type*} {G : ι → Type*} (i₀ : ι)
    (f : ∀ i, G i → T) :
    {x : ∀ i, G i // ∀ i, f i (x i) = f i₀ (x i₀)} ≃
      Σ t : T, ∀ i, {x : G i // f i x = t} where
  toFun x := ⟨f i₀ (x.1 i₀), fun i => ⟨x.1 i,x.2 i⟩⟩
  invFun x := ⟨fun i => (x.2 i).1, fun i => (x.2 i).2.trans (x.2 i₀).2.symm⟩
  left_inv x := rfl
  right_inv x := by
    rcases x with ⟨t,x⟩
    dsimp
    have he : f i₀ (x i₀).1 = t := (x i₀).2
    apply Sigma.ext he
    have hh : ∀ (s t : T) (a : ∀ i, {z : G i // f i z = s})
        (b : ∀ i, {z : G i // f i z = t}), s = t →
        (∀ i, (a i).val = (b i).val) → HEq a b := by
      rintro s t a b rfl hab
      apply heq_of_eq
      funext i
      exact Subtype.ext (hab i)
    exact hh _ _ _ _ he (fun _ => rfl)

/-- Exact product formula used in the source's retrospective F computation. -/
theorem allEqualLevel_card {ι T : Type*} {G : ι → Type*} [Fintype ι] [Fintype T]
    [∀ i, Fintype (G i)] [DecidableEq T] [DecidableEq ι] (i₀ : ι) (f : ∀ i, G i → T) :
    Fintype.card {x : ∀ i, G i // ∀ i, f i (x i) = f i₀ (x i₀)} =
      ∑ t : T, ∏ i : ι, Fintype.card {x : G i // f i x = t} := by
  classical
  rw [Fintype.card_congr (allEqualLevelEquiv i₀ f), Fintype.card_sigma]
  congr 1
  funext t
  exact Fintype.card_pi

/-- Extra components can only decrease the all-equal event. -/
theorem twice_constrained_card_le {A B C T : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : A → T) (g : B → T) [DecidableEq T]
    (P : A × B × C → Prop) [DecidablePred P]
    (hp : ∀ x, P x → f x.1 = g x.2.1)
    (hf : ∀ t, 2 * Fintype.card {a : A // f a = t} ≤ Fintype.card A) :
    2 * Fintype.card {x : A × B × C // P x} ≤
      Fintype.card A * Fintype.card B * Fintype.card C := by
  classical
  let emb : {x : A × B × C // P x} → ({x : A × B // f x.1 = g x.2} × C) :=
    fun x => (⟨(x.1.1,x.1.2.1),hp x.1 x.2⟩,x.1.2.2)
  have hinj : Function.Injective emb := by
    intro x y h
    apply Subtype.ext
    have h₁ := congrArg (fun z => z.1.1.1) h
    have h₂ := congrArg (fun z => z.1.1.2) h
    have h₃ := congrArg Prod.snd h
    exact Prod.ext h₁ (Prod.ext h₂ h₃)
  have hc := Fintype.card_le_of_injective emb hinj
  rw [Fintype.card_prod] at hc
  calc
    _ ≤ 2 * (Fintype.card {x : A × B // f x.1 = g x.2} * Fintype.card C) :=
      Nat.mul_le_mul_left 2 hc
    _ = (2 * Fintype.card {x : A × B // f x.1 = g x.2}) * Fintype.card C := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (twice_equalLevel_card_le f g hf)

/-- Two distinct independent components suffice for the exact half bound. -/
theorem twice_allEqualLevel_card_le {ι T : Type*} {G : ι → Type*}
    [Fintype ι] [∀ i, Fintype (G i)] [DecidableEq T] [DecidableEq ι]
    (i₀ i₁ : ι) (hi : i₁ ≠ i₀) (f : ∀ i, G i → T)
    (hf : ∀ t, 2 * Fintype.card {a : G i₀ // f i₀ a = t} ≤ Fintype.card (G i₀)) :
    2 * Fintype.card {x : ∀ i, G i // ∀ i, f i (x i) = f i₀ (x i₀)} ≤
      Fintype.card (∀ i, G i) := by
  classical
  let R := ∀ j : {j : ι // j ≠ i₀}, G j.val
  let g : R → T := fun x => f i₁ (x ⟨i₁,hi⟩)
  let emb : {x : ∀ i, G i // ∀ i, f i (x i) = f i₀ (x i₀)} →
      {x : G i₀ × R // f i₀ x.1 = g x.2} :=
    fun x => ⟨(Equiv.piSplitAt i₀ G) x.val, (x.property i₁).symm⟩
  have hinj : Function.Injective emb := by
    intro x y h
    apply Subtype.ext
    apply (Equiv.piSplitAt i₀ G).injective
    exact congrArg Subtype.val h
  have hc := Fintype.card_le_of_injective emb hinj
  calc
    _ ≤ 2 * Fintype.card {x : G i₀ × R // f i₀ x.1 = g x.2} :=
      Nat.mul_le_mul_left 2 hc
    _ ≤ Fintype.card (G i₀) * Fintype.card R := twice_equalLevel_card_le _ _ hf
    _ = Fintype.card (∀ i, G i) := by
      rw [← Fintype.card_prod]
      exact (Fintype.card_congr (Equiv.piSplitAt i₀ G)).symm

end ExactQuantumFactoring


end

end OAI
