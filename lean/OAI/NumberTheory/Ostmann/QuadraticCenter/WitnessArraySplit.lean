import OAI.NumberTheory.Ostmann.QuadraticCenter.AdaptiveSmallArray
import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeProductArrays

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def primeProductArrayCoefficient (L : ℕ) [NeZero L]
    (A : ∀p:ℕ,Finset (ZMod p)) (lam X : ℝ) (t : ℕ→ℤ) (q P s : ℕ) : ℂ :=
  positiveDivisorArray L q lam A (adaptiveInverse q) P ((q:ℝ)/X)
    (centerCorrection q L (primeProductCenter q t)) ((primeProductCenter q t:ℝ)/q) s

def primeProductSmallSum (L : ℕ) [NeZero L]
    (A : ∀p:ℕ,Finset (ZMod p)) (lam X : ℝ) (t : ℕ→ℤ) (q : ℕ) : ℂ :=
  ∑s∈adaptiveSmallSupport L,primeProductArrayCoefficient L A lam X t q 1 s *
    (jacobiSym (s:ℤ) q:ℂ)

def primeProductLargeSum (L Z : ℕ) [NeZero L]
    (A : ∀p:ℕ,Finset (ZMod p)) (lam X : ℝ) (t : ℕ→ℤ) (q : ℕ) : ℂ :=
  ∑s∈adaptiveArraySupport L Z \ adaptiveSmallSupport L,
    primeProductArrayCoefficient L A lam X t q 1 s*(jacobiSym (s:ℤ) q:ℂ)

def primeProductNontrivialSum (L Z : ℕ) [NeZero L]
    (A : ∀p:ℕ,Finset (ZMod p)) (lam X : ℝ) (t : ℕ→ℤ) (q : ℕ) : ℂ :=
  ∑P∈q.divisors.erase 1,(-1:ℂ)^P.primeFactors.card *
    ∑s∈adaptiveArraySupport L Z,
      primeProductArrayCoefficient L A lam X t q P s*(jacobiSym (s:ℤ) q:ℂ)

theorem primeProductSmallSum_eq_actualSmallArray (L : ℕ) [NeZero L]
    (A : ∀p:ℕ,Finset (ZMod p)) (lam X : ℝ) (t : ℕ→ℤ) (q : ℕ) :
    primeProductSmallSum L A lam X t q =
      ∑s∈adaptiveSmallSupport L,adaptiveActualSmallArray L q lam A ((q:ℝ)/X)
        (centerCorrection q L (primeProductCenter q t)) ((primeProductCenter q t:ℝ)/q) s *
          (jacobiSym (s:ℤ) q:ℂ) := by
  classical
  apply Finset.sum_congr rfl
  intro s hs
  simp only [adaptiveActualSmallArray,ite_eq_left hs,primeProductArrayCoefficient,Int.cast_natCast]

theorem primeProductArraySum_split {F : Finset ℕ}
    [NeZero (∏p:F,p.val)] {Z q : ℕ} (hZ : 1≤Z) (hFZ : (∏p∈F,p)≤Z) (hq : q≠0)
    (A : ∀p:ℕ,Finset (ZMod p)) (lam X : ℝ) (t : ℕ→ℤ) :
    primeProductArraySum F A lam X t (Z^14) q =
      primeProductSmallSum (∏p:F,p.val) A lam X t q+
      primeProductLargeSum (∏p:F,p.val) Z A lam X t q+
      primeProductNontrivialSum (∏p:F,p.val) Z A lam X t q := by
  classical
  let L := ∏p:F,p.val
  let inner := fun P => ∑s∈adaptiveArraySupport L Z,
    primeProductArrayCoefficient L A lam X t q P s*(jacobiSym (s:ℤ) q:ℂ)
  have hprod : L=∏p∈F,p := by
    dsimp [L]
    exact Finset.prod_coe_sort F (fun p : ℕ => p)
  have hfull : primeProductArraySum F A lam X t (Z^14) q=
      ∑P∈q.divisors,(-1:ℂ)^P.primeFactors.card*inner P := by
    unfold primeProductArraySum inner primeProductArrayCoefficient adaptiveArraySupport adaptiveInverse
    simp only [←hprod,mul_comm]
    rfl
  have h1 : 1∈q.divisors := Nat.mem_divisors.mpr ⟨one_dvd _,hq⟩
  have hdiv := Finset.add_sum_erase q.divisors
    (fun P => (-1:ℂ)^P.primeFactors.card*inner P) h1
  have hsmall : adaptiveSmallSupport L ⊆ adaptiveArraySupport L Z :=
    adaptiveSmallSupport_subset hZ (by simpa only [hprod] using hFZ)
  have hs := Finset.sum_sdiff hsmall (f:=fun s =>
    primeProductArrayCoefficient L A lam X t q 1 s*(jacobiSym (s:ℤ) q:ℂ))
  rw [hfull,←hdiv]
  simp only [Nat.primeFactors_one,Finset.card_empty,pow_zero,one_mul]
  change inner 1+primeProductNontrivialSum L Z A lam X t q=_
  have hinner : inner 1=primeProductSmallSum L A lam X t q+
      primeProductLargeSum L Z A lam X t q := by
    dsimp [inner,primeProductSmallSum,primeProductLargeSum]
    simpa only [add_comm] using hs.symm
  rw [hinner]

theorem primeProductArraySum_norm_le_split {F : Finset ℕ}
    [NeZero (∏p:F,p.val)] {Z q : ℕ} (hZ : 1≤Z) (hFZ : (∏p∈F,p)≤Z) (hq : q≠0)
    (A : ∀p:ℕ,Finset (ZMod p)) (lam X : ℝ) (t : ℕ→ℤ) :
    ‖primeProductArraySum F A lam X t (Z^14) q‖ ≤
      ‖primeProductSmallSum (∏p:F,p.val) A lam X t q‖+
      ‖primeProductLargeSum (∏p:F,p.val) Z A lam X t q‖+
      ‖primeProductNontrivialSum (∏p:F,p.val) Z A lam X t q‖ := by
  rw [primeProductArraySum_split hZ hFZ hq A lam X t]
  exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))

end Ostmann.QuadraticCenter

end

end OAI
