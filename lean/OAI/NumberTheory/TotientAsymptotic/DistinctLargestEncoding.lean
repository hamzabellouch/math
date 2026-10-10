import OAI.NumberTheory.TotientAsymptotic.DistinctPrimeRemoval
import OAI.NumberTheory.TotientAsymptotic.DistinctPrimeMass

namespace OAI

/-! Exact reconstruction and residual bounds for unequal largest primes. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

structure DistinctLargestConditions {k : ℕ} (a b : ℕ) (i : Fin k)
    (y T U V I : ℝ) (f : PairedFactors k) : Prop where
  product_pos : 0 < pairedProduct f
  product_eq : pairedProduct f=∏ j,f.2 j
  left_two : 2 ≤ f.1 i
  right_two : 2 ≤ f.2 i
  order : largestPrimeFactor (f.2 i) < largestPrimeFactor (f.1 i)
  left_lower : T ≤ largestPrimeFactor (f.1 i)
  right_lower : T ≤ largestPrimeFactor (f.2 i)
  left_prime : (a*f.1 i+1).Prime
  right_prime : (b*f.2 i+1).Prime
  left_le : ((a*f.1 i:ℕ):ℝ) ≤ y
  right_le : ((b*f.2 i:ℕ):ℝ) ≤ y
  omega_le : ((pairedProduct f).primeFactorsList.length:ℝ) ≤ I
  support : ∀ p ∈ (pairedProduct f).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V

def CrossRemoval {k : ℕ} (i j l : Fin k) (f : PairedFactors k) : Prop :=
  l ≠ i ∧
  largestPrimeFactor (f.2 i) ∣ divideFactor i (largestPrimeFactor (f.1 i)) f.1 j ∧
  largestPrimeFactor (f.1 i) ∣ divideFactor i (largestPrimeFactor (f.2 i)) f.2 l

def distinctLargestEncoding {k : ℕ} (i j l : Fin k) (f : PairedFactors k) : TwoPrimeEncoding k :=
  let p := largestPrimeFactor (f.1 i)
  let q := largestPrimeFactor (f.2 i)
  ((doubleDivide i j p q f.1,doubleDivide i l q p f.2),(p,q))

def distinctPrimeDecode {k : ℕ} (i j l : Fin k) (e : TwoPrimeEncoding k) : PairedFactors k :=
  (doubleMultiply i j e.2.1 e.2.2 e.1.1,doubleMultiply i l e.2.2 e.2.1 e.1.2)

lemma distinctLargest_divisors {k a b : ℕ} {i : Fin k} {y T U V I : ℝ} {f : PairedFactors k}
    (hf : DistinctLargestConditions a b i y T U V I f) :
    (largestPrimeFactor (f.1 i)).Prime ∧ (largestPrimeFactor (f.2 i)).Prime ∧
    largestPrimeFactor (f.1 i) ∣ f.1 i ∧ largestPrimeFactor (f.2 i) ∣ f.2 i := by
  have hl := largestPrimeFactor_mem hf.left_two
  have hr := largestPrimeFactor_mem hf.right_two
  exact ⟨Nat.prime_of_mem_primeFactors hl,Nat.prime_of_mem_primeFactors hr,
    Nat.dvd_of_mem_primeFactors hl,Nat.dvd_of_mem_primeFactors hr⟩

lemma distinctLargest_slots {k a b : ℕ} {i : Fin k} {y T U V I : ℝ} {f : PairedFactors k}
    (hf : DistinctLargestConditions a b i y T U V I f) : ∃ j l,CrossRemoval i j l f :=
  distinct_largest_cross_slots i f hf.product_eq hf.left_two hf.right_two hf.order

lemma distinctLargest_decode {k a b : ℕ} {i j l : Fin k} {y T U V I : ℝ} {f : PairedFactors k}
    (hf : DistinctLargestConditions a b i y T U V I f) (hs : CrossRemoval i j l f) :
    distinctPrimeDecode i j l (distinctLargestEncoding i j l f)=f := by
  obtain ⟨_,_,hp,hq⟩ := distinctLargest_divisors hf
  exact Prod.ext (doubleMultiply_doubleDivide i j _ _ f.1 hp hs.2.1)
    (doubleMultiply_doubleDivide i l _ _ f.2 hq hs.2.2)

lemma distinctLargest_product {k a b : ℕ} {i j l : Fin k} {y T U V I : ℝ} {f : PairedFactors k}
    (hf : DistinctLargestConditions a b i y T U V I f) (hs : CrossRemoval i j l f) :
    pairedProduct (distinctLargestEncoding i j l f).1*
      ((distinctLargestEncoding i j l f).2.1*(distinctLargestEncoding i j l f).2.2)=pairedProduct f := by
  obtain ⟨_,_,hp,_⟩ := distinctLargest_divisors hf
  exact (mul_comm _ _).trans (prod_doubleDivide i j _ _ f.1 hp hs.2.1)

lemma distinctLargest_residual {k a b : ℕ} {i j l : Fin k} {y T U V I : ℝ} {f : PairedFactors k}
    (hf : DistinctLargestConditions a b i y T U V I f) (hs : CrossRemoval i j l f) :
    0 < pairedProduct (distinctLargestEncoding i j l f).1 ∧
    pairedProduct (distinctLargestEncoding i j l f).1=(∏ t,(distinctLargestEncoding i j l f).1.2 t) ∧
    ((pairedProduct (distinctLargestEncoding i j l f).1).primeFactorsList.length:ℝ) ≤ I ∧
    ∀ p ∈ (pairedProduct (distinctLargestEncoding i j l f).1).primeFactorsList,
      U < (p:ℝ) ∧ (p:ℝ) ≤ V := by
  obtain ⟨hp,hq,hpi,hqi⟩ := distinctLargest_divisors hf
  have hd := doubleDivide_prod_dvd i j _ _ f.1 hpi hs.2.1
  have he := prod_doubleDivide i j _ _ f.1 hpi hs.2.1
  have he' := prod_doubleDivide i l _ _ f.2 hqi hs.2.2
  refine ⟨doubleDivide_prod_pos i j _ _ f.1 hpi hs.2.1 hf.product_pos,?_,?_,?_⟩
  · apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hp.pos hq.pos)
    dsimp only [pairedProduct,distinctLargestEncoding]
    rw [he]
    rw [mul_comm (largestPrimeFactor (f.1 i)) (largestPrimeFactor (f.2 i)),he']
    exact hf.product_eq
  · exact (show ((∏ t,doubleDivide i j _ _ f.1 t).primeFactorsList.length:ℝ) ≤
        (pairedProduct f).primeFactorsList.length by
      exact_mod_cast (Nat.primeFactorsList_sublist_of_dvd hd hf.product_pos.ne').length_le).trans hf.omega_le
  · intro p hmem
    exact hf.support p (Nat.primeFactorsList_subset_of_dvd hd hf.product_pos.ne' hmem)

lemma distinctLargest_residual_squarefree {k a b : ℕ} {i j l : Fin k} {y T U V I : ℝ}
    {f : PairedFactors k} (hf : DistinctLargestConditions a b i y T U V I f)
    (hs : CrossRemoval i j l f) (hsq : Squarefree (pairedProduct f)) :
    Squarefree (pairedProduct (distinctLargestEncoding i j l f).1) :=
  Squarefree.squarefree_of_dvd
    (doubleDivide_prod_dvd i j _ _ f.1 (distinctLargest_divisors hf).2.2.1 hs.2.1) hsq

end TotientAsymptotic

end

end OAI
