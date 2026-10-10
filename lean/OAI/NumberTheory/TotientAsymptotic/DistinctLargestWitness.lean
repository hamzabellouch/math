import OAI.NumberTheory.TotientAsymptotic.DistinctLargestEncoding

namespace OAI

/-! The prime-pair sieve hypotheses for the recoverable unequal-prime encoding. -/
noncomputable section
namespace TotientAsymptotic

lemma distinctLargest_witness {k a b : ℕ} {i j l : Fin k} {y T U V I : ℝ}
    {f : PairedFactors k} (ha : 0 < a) (hb : 0 < b)
    (hf : DistinctLargestConditions a b i y T U V I f) (hs : CrossRemoval i j l f) :
    DistinctPrimeWitness a b i j y T (distinctLargestEncoding i j l f) := by
  obtain ⟨hp,hq,hpi,hqi⟩ := distinctLargest_divisors hf
  let p := largestPrimeFactor (f.1 i)
  let q := largestPrimeFactor (f.2 i)
  have hl : distinctCoefficient a i j (distinctLargestEncoding i j l f).1
      (distinctLargestEncoding i j l f).2.2=a*(f.1 i/p) := by
    change a*(multiplyFactor j q (doubleDivide i j p q f.1) i)=a*(f.1 i/p)
    rw [show multiplyFactor j q (doubleDivide i j p q f.1)=divideFactor i p f.1 from
      multiply_divideFactor j q _ hs.2.1]
    simp only [divideFactor,Function.update_self]
  have hr : (distinctLargestEncoding i j l f).1.2 i=f.2 i/q := by
    change divideFactor l p (divideFactor i q f.2) i=f.2 i/q
    simp only [divideFactor,Function.update_of_ne hs.1.symm,Function.update_self]
  have hleft0 : 0 < f.1 i/p := Nat.div_pos
    (Nat.le_of_dvd (by have := hf.left_two; omega) hpi) hp.pos
  have hright0 : 0 < f.2 i/q := Nat.div_pos
    (Nat.le_of_dvd (by have := hf.right_two; omega) hqi) hq.pos
  have hleft : a*(f.1 i/p)*p+1=a*f.1 i+1 := by rw [mul_assoc,Nat.div_mul_cancel hpi]
  have hright : b*(f.2 i/q)*q+1=b*f.2 i+1 := by rw [mul_assoc,Nat.div_mul_cancel hqi]
  have hleftle : ((a*(f.1 i/p):ℕ):ℝ) ≤ ((a*f.1 i:ℕ):ℝ) := by
    exact_mod_cast Nat.mul_le_mul_left a (Nat.div_le_self (f.1 i) p)
  have hrightle : ((b*(f.2 i/q):ℕ):ℝ) ≤ ((b*f.2 i:ℕ):ℝ) := by
    exact_mod_cast Nat.mul_le_mul_left b (Nat.div_le_self (f.2 i) q)
  constructor
  · exact hf.left_lower
  · exact hp
  · rw [hl]
    exact hleft ▸ hf.left_prime
  · rw [hl]
    exact Nat.mul_pos ha hleft0
  · rw [hl]
    exact hleftle.trans hf.left_le
  · exact hf.right_lower
  · exact hq
  · rw [hr]
    exact hright ▸ hf.right_prime
  · rw [hr]
    exact Nat.mul_pos hb hright0
  · rw [hr]
    exact hrightle.trans hf.right_le

end TotientAsymptotic

end

end OAI
