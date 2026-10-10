import OAI.NumberTheory.JointDickman.Arithmetic.PrimeDigitDecomposition
import OAI.NumberTheory.JointDickman.Amplification.CRTMean

namespace OAI

/-! # Prime-square CRT with the first and higher digits kept separate -/

namespace JointDickman
open Finset

noncomputable def primeDigitFamilyEquiv (P : Finset ℕ)
    [∀ p : P, NeZero p.val] :
    (∀ p : P, ZMod (p.val^2)) ≃ ((∀ p : P, ZMod p.val) × (∀ p : P, ZMod p.val)) where
  toFun x := (fun p => (primeDigits p.val (x p)).1, fun p => (primeDigits p.val (x p)).2)
  invFun x := fun p => joinPrimeDigits p.val (x.1 p,x.2 p)
  left_inv x := by funext p; exact join_primeDigits (x p)
  right_inv x := by
    apply Prod.ext <;> funext p
    · exact congrArg Prod.fst (primeDigits_join (x.1 p,x.2 p))
    · exact congrArg Prod.snd (primeDigits_join (x.1 p,x.2 p))

/-- Uniform CRT residues retain independent uniform higher digits after
all first digits are exposed. The test may depend on both entire families. -/
theorem prime_square_crt_digits (P : Finset ℕ) [∀ p : P, NeZero p.val]
    (hP : ∀ p ∈ P, p.Prime)
    (F : (∀ p : P, ZMod p.val) → (∀ p : P, ZMod p.val) → ℝ) :
    (∑ n ∈ range (∏ p ∈ P, p^2),
      F (fun p => (primeDigits p.val (n : ZMod (p.val^2))).1)
        (fun p => (primeDigits p.val (n : ZMod (p.val^2))).2)) /
      (∏ p ∈ P, (p : ℝ)^2) =
    (∑ r, ∑ t, F r t) / (∏ p ∈ P, (p : ℝ)^2) := by
  classical
  have hcop : Pairwise (fun p q : P => (p.val^2).Coprime (q.val^2)) := by
    intro p q hpq
    exact ((Nat.coprime_primes (hP p.val p.property) (hP q.val q.property)).mpr
      (fun h => hpq (Subtype.ext h))).pow _ _
  let G := fun x : ∀ p : P, ZMod (p.val^2) =>
    F (fun p => (primeDigits p.val (x p)).1) (fun p => (primeDigits p.val (x p)).2)
  have h := crt_uniform_mean (fun p : P => p.val^2) hcop G
  rw [P.prod_coe_sort (fun p : ℕ => p^2)] at h
  have hd : (∏ p : P, ((p.val^2 : ℕ) : ℝ)) = ∏ p ∈ P, (p : ℝ)^2 := by
    simp only [Nat.cast_pow]
    exact prod_coe_sort P (fun p : ℕ => (p : ℝ)^2)
  rw [hd] at h
  have hw (x : ∀ p : P, ZMod (p.val^2)) :
      finiteProductMass (fun p : P => fun _ : ZMod (p.val^2) => 1/((p.val^2 : ℕ) : ℝ)) x =
        1/(∏ p ∈ P, (p : ℝ)^2) := by
    simp only [finiteProductMass,prod_div_distrib,prod_const_one,hd]
  simp_rw [hw,one_div_mul_eq_div] at h
  rw [← sum_div] at h
  have hs : (∑ x, G x) = ∑ r, ∑ t, F r t := by
    have he := (primeDigitFamilyEquiv P).sum_comp (fun x => F x.1 x.2)
    exact he.trans (Fintype.sum_prod_type _)
  exact h.trans (congrArg (fun x => x/(∏ p ∈ P, (p : ℝ)^2)) hs)

end JointDickman

end OAI
