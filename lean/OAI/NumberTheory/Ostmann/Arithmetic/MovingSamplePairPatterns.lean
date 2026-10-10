import OAI.NumberTheory.Ostmann.Arithmetic.MovingCompensationWeight
import OAI.NumberTheory.Ostmann.Tree.SampleEqualityPatterns

namespace OAI

/-! # Equality patterns of the two actual internal sample trees -/

namespace Ostmann
open scoped Classical BigOperators

def movingSamplePairCoordinates (A : Type*) (n : ℕ) :
    (MovingSampleSlots A n × MovingSampleSlots A n) ≃ (Bool × MovingSampleIndex n → A) where
  toFun a i := if i.1 then movingSampleCoordinates A n a.2 i.2
    else movingSampleCoordinates A n a.1 i.2
  invFun x := ((movingSampleCoordinates A n).symm (fun i => x (false, i)),
    (movingSampleCoordinates A n).symm (fun i => x (true, i)))
  left_inv a := by
    rcases a with ⟨l, r⟩
    simp only [Bool.false_eq_true, ite_false, ite_true, Equiv.symm_apply_apply]
  right_inv x := by
    funext i
    rcases i with ⟨b, i⟩
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, Equiv.apply_symm_apply]

@[simp] theorem movingSamplePairCoordinates_left {A : Type*} (n : ℕ)
    (x : Bool × MovingSampleIndex n → A) (i : MovingSampleIndex n) :
    movingSampleCoordinates A n ((movingSamplePairCoordinates A n).symm x).1 i = x (false, i) := by
  exact congrFun ((movingSampleCoordinates A n).apply_symm_apply (fun i => x (false, i))) i

@[simp] theorem movingSamplePairCoordinates_right {A : Type*} (n : ℕ)
    (x : Bool × MovingSampleIndex n → A) (i : MovingSampleIndex n) :
    movingSampleCoordinates A n ((movingSamplePairCoordinates A n).symm x).2 i = x (true, i) := by
  exact congrFun ((movingSampleCoordinates A n).apply_symm_apply (fun i => x (true, i))) i

theorem sum_movingSamplePair {A M : Type*} [Fintype A] [AddCommMonoid M]
    (n : ℕ) (F : MovingSampleSlots A n → MovingSampleSlots A n → M) :
    (∑ l, ∑ r, F l r) = ∑ x : Bool × MovingSampleIndex n → A,
      F ((movingSamplePairCoordinates A n).symm x).1 ((movingSamplePairCoordinates A n).symm x).2 := by
  have hs := Fintype.sum_prod_type (fun a : MovingSampleSlots A n × MovingSampleSlots A n => F a.1 a.2)
  have he := (movingSamplePairCoordinates A n).symm.sum_comp
    (fun a : MovingSampleSlots A n × MovingSampleSlots A n => F a.1 a.2)
  simp only [finite_univ_canonical] at hs he ⊢
  exact hs.symm.trans he.symm

/-- The two histories have exactly `4*n*2^n` independent internal draws,
irrespective of the number of protected bulk positions. -/
theorem card_movingSamplePairIndex (n : ℕ) :
    Fintype.card (Bool × MovingSampleIndex n) = 4 * n * 2 ^ n := by
  rw [Fintype.card_prod, Fintype.card_bool, card_movingSampleIndex]
  ring

theorem movingSamplePair_compensated_prior {A : Type*} (μ : ℕ → A → ℝ)
    (value : A → ℕ) (n : ℕ) (x : Bool × MovingSampleIndex n → A) :
    let a := (movingSamplePairCoordinates A n).symm x
    ((movingSampleProduct value a.1 : ℝ) * movingSamplesPrior μ a.1) *
      ((movingSampleProduct value a.2 : ℝ) * movingSamplesPrior μ a.2) =
        ∏ i : Bool × MovingSampleIndex n, (value (x i) : ℝ) * μ (movingSampleTier i.2) (x i) := by
  dsimp only
  rw [movingSamples_compensated_prior, movingSamples_compensated_prior,
    Fintype.prod_prod_type, Fintype.prod_bool]
  simp only [movingSamplePairCoordinates_left, movingSamplePairCoordinates_right]
  ring

/-- Exact decomposition of the original pair of sample trees by its
equality pattern. No restriction on coincidences between descendants is
inserted, and no factor depending on the bulk length appears. -/
theorem sum_movingSamplePair_patterns {A M : Type*} [Fintype A] [AddCommMonoid M]
    (n : ℕ) (F : MovingSampleSlots A n → MovingSampleSlots A n → M) :
    letI := sampleSetoidFintype (Bool × MovingSampleIndex n)
    (∑ l, ∑ r, F l r) =
      ∑ s : Setoid (Bool × MovingSampleIndex n),
        ∑ x : {x : Quotient s → A // Function.Injective x},
          let a := (movingSamplePairCoordinates A n).symm (fun i => x.val (Quotient.mk'' i))
          F a.1 a.2 := by
  let _ := sampleSetoidFintype (Bool × MovingSampleIndex n)
  have h₁ := sum_movingSamplePair n F
  have h₂ := sum_sample_equality_patterns (I := Bool × MovingSampleIndex n) (A := A) (M := M)
      (fun x => F ((movingSamplePairCoordinates A n).symm x).1
        ((movingSamplePairCoordinates A n).symm x).2)
  simp only [finite_univ_canonical] at h₁ h₂ ⊢
  exact h₁.trans h₂

end Ostmann

end OAI
