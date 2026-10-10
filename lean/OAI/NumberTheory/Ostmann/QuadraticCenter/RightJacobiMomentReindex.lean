import OAI.NumberTheory.Ostmann.QuadraticCenter.RightJacobiMomentSupport

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem primeSubsetProduct_injective {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) :
    Function.Injective (primeSubsetProduct : Finset P → ℕ) := by
  intro s t h
  calc
    s = primeSupportWithin P (primeSubsetProduct s) :=
      (primeSupportWithin_primeSubsetProduct hP s).symm
    _ = primeSupportWithin P (primeSubsetProduct t) := congrArg (primeSupportWithin P) h
    _ = t := primeSupportWithin_primeSubsetProduct hP t

theorem primeSubsetProduct_primeSupportWithin {P : Finset ℕ} {n : ℕ}
    (hn : Squarefree n) (hcover : n.primeFactors ⊆ P) :
    primeSubsetProduct (primeSupportWithin P n) = n := by
  classical
  have himage : (primeSupportWithin P n).image Subtype.val = n.primeFactors := by
    ext p
    constructor
    · intro hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      exact mem_primeSupportWithin.mp hq
    · intro hp
      exact Finset.mem_image.mpr ⟨⟨p, hcover hp⟩, mem_primeSupportWithin.mpr hp, rfl⟩
  rw [primeSubsetProduct_eq_image_prod, himage, Nat.prod_primeFactors_of_squarefree hn]

@[simp] theorem primeSubsetProduct_primeFactors_card {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (s : Finset P) :
    (primeSubsetProduct s).primeFactors.card = s.card := by
  rw [primeSubsetProduct_primeFactors hP]
  exact Finset.card_image_of_injective s Subtype.val_injective

theorem sum_primeSubsetProduct {A : Type*} [AddCommMonoid A]
    {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p) (S : Finset ℕ)
    (hS : ∀ n ∈ S, Squarefree n) (hcover : ∀ n ∈ S, n.primeFactors ⊆ P)
    (F : ℕ → A) :
    (∑ s : Finset P, if primeSubsetProduct s ∈ S then F (primeSubsetProduct s) else 0) =
      ∑ n ∈ S, F n := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun s _ => primeSubsetProduct s)
  · intro s hs
    exact (Finset.mem_filter.mp hs).2
  · intro s hs t ht he
    exact primeSubsetProduct_injective hP he
  · intro n hn
    refine ⟨primeSupportWithin P n, ?_, primeSubsetProduct_primeSupportWithin
      (hS n hn) (hcover n hn)⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      primeSubsetProduct_primeSupportWithin (hS n hn) (hcover n hn), hn]
  · intro s hs
    rfl

noncomputable def liftSquarefreeArray (P S : Finset ℕ) (b : ℕ → ℂ)
    (s : Finset P) : ℂ :=
  if primeSubsetProduct s ∈ S then b (primeSubsetProduct s) else 0

theorem sum_liftSquarefreeArray_mul {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (S : Finset ℕ)
    (hS : ∀ n ∈ S, Squarefree n) (hcover : ∀ n ∈ S, n.primeFactors ⊆ P)
    (b e : ℕ → ℂ) :
    (∑ s, liftSquarefreeArray P S b s * e (primeSubsetProduct s)) =
      ∑ n ∈ S, b n * e n := by
  simp only [liftSquarefreeArray, ite_mul, zero_mul]
  exact sum_primeSubsetProduct hP S hS hcover (fun n => b n * e n)

theorem sum_liftSquarefreeArray_norm {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (S : Finset ℕ)
    (hS : ∀ n ∈ S, Squarefree n) (hcover : ∀ n ∈ S, n.primeFactors ⊆ P)
    (b : ℕ → ℂ) :
    (∑ s, ‖liftSquarefreeArray P S b s‖) = ∑ n ∈ S, ‖b n‖ := by
  simp only [liftSquarefreeArray, apply_ite norm, norm_zero]
  exact sum_primeSubsetProduct hP S hS hcover (fun n => ‖b n‖)

theorem sum_liftSquarefreeArray_energy {P : Finset ℕ}
    (hP : ∀ p ∈ P, Nat.Prime p) (S : Finset ℕ)
    (hS : ∀ n ∈ S, Squarefree n) (hcover : ∀ n ∈ S, n.primeFactors ⊆ P)
    (b : ℕ → ℂ) (w : ℝ) :
    (∑ s, w ^ s.card * ‖liftSquarefreeArray P S b s‖ ^ 2) =
      ∑ n ∈ S, w ^ n.primeFactors.card * ‖b n‖ ^ 2 := by
  classical
  rw [← sum_primeSubsetProduct hP S hS hcover
    (fun n => w ^ n.primeFactors.card * ‖b n‖ ^ 2)]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hn : primeSubsetProduct s ∈ S
  · simp [liftSquarefreeArray, hn, primeSubsetProduct_primeFactors_card hP]
  · simp [liftSquarefreeArray, hn]

end Ostmann.QuadraticCenter

end OAI
