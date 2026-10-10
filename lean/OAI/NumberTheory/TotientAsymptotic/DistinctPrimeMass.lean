import OAI.NumberTheory.TotientAsymptotic.SquarefreeIntervalMass
import OAI.NumberTheory.TotientAsymptotic.DistinctPrimeTail

namespace OAI

/-! The reciprocal mass after extracting the two unequal largest primes. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

abbrev TwoPrimeEncoding (k : ℕ) := PairedFactors k × (ℕ × ℕ)

def twoPrimeWeight {k : ℕ} (e : TwoPrimeEncoding k) : ℝ :=
  ((pairedProduct e.1*(e.2.1*e.2.2):ℕ):ℝ)⁻¹

def distinctCoefficient {k : ℕ} (a : ℕ) (i j : Fin k) (r : PairedFactors k) (q : ℕ) : ℕ :=
  a*multiplyFactor j q r.1 i

structure DistinctPrimeWitness {k : ℕ} (a b : ℕ) (i j : Fin k) (y T : ℝ)
    (e : TwoPrimeEncoding k) : Prop where
  left_lower : T ≤ e.2.1
  left_prime : e.2.1.Prime
  left_shift_prime : (distinctCoefficient a i j e.1 e.2.2*e.2.1+1).Prime
  left_pos : 0 < distinctCoefficient a i j e.1 e.2.2
  left_le : (distinctCoefficient a i j e.1 e.2.2:ℝ) ≤ y
  right_lower : T ≤ e.2.2
  right_prime : e.2.2.Prime
  right_shift_prime : (b*e.1.2 i*e.2.2+1).Prime
  right_pos : 0 < b*e.1.2 i
  right_le : ((b*e.1.2 i:ℕ):ℝ) ≤ y

lemma distinct_prime_fiber_sum {k : ℕ} (E : Finset (TwoPrimeEncoding k))
    (r : PairedFactors k) :
    (∑ e ∈ E.filter (fun e => e.1=r),twoPrimeWeight e)=
      (pairedProduct r:ℝ)⁻¹*
        (∑ q ∈ (E.filter (fun e => e.1=r)).image Prod.snd,((q.1*q.2:ℕ):ℝ)⁻¹) := by
  classical
  rw [Finset.mul_sum,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro e he
    have hh := (Finset.mem_filter.mp he).2
    simp only [twoPrimeWeight,hh,Nat.cast_mul,mul_inv_rev]
    ring
  · intro e he f hf hh
    exact Prod.ext ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm) hh

lemma distinct_prime_fiber_bound {k a b : ℕ} (i j : Fin k) (y T C : ℝ)
    (htail : ∀ (E : Finset (ℕ × ℕ)) (a : ℕ → ℕ) (b : ℕ),
      0 < b → (b:ℝ) ≤ y →
      (∀ q ∈ E,T ≤ q.1 ∧ q.1.Prime ∧ (a q.2*q.1+1).Prime ∧
        0 < a q.2 ∧ (a q.2:ℝ) ≤ y ∧ T ≤ q.2 ∧ q.2.Prime ∧ (b*q.2+1).Prime) →
      (∑ q ∈ E,((q.1*q.2:ℕ):ℝ)⁻¹) ≤ C*(B y)^2/(Real.log T)^2)
    (E : Finset (TwoPrimeEncoding k))
    (hE : ∀ e ∈ E,DistinctPrimeWitness a b i j y T e)
    (r : PairedFactors k) (hr : r ∈ E.image Prod.fst) :
    (∑ e ∈ E.filter (fun e => e.1=r),twoPrimeWeight e) ≤
      (C*(B y)^2/(Real.log T)^2)*(pairedProduct r:ℝ)⁻¹ := by
  classical
  obtain ⟨e,he,her⟩ := Finset.mem_image.mp hr
  have hw := hE e he
  have hp : 0 < b*r.2 i := by simpa only [her] using hw.right_pos
  have hle : ((b*r.2 i:ℕ):ℝ) ≤ y := by simpa only [her] using hw.right_le
  have ht := htail ((E.filter (fun e => e.1=r)).image Prod.snd)
    (distinctCoefficient a i j r) (b*r.2 i) hp hle (by
      intro q hq
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨hf,hfr⟩ := Finset.mem_filter.mp hf
      have hh := hE f hf
      refine ⟨hh.left_lower,hh.left_prime,?_,?_,?_,hh.right_lower,hh.right_prime,?_⟩
      · simpa only [hfr] using hh.left_shift_prime
      · simpa only [hfr] using hh.left_pos
      · simpa only [hfr] using hh.left_le
      · simpa only [hfr] using hh.right_shift_prime)
  rw [distinct_prime_fiber_sum]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left ht
    (inv_nonneg.mpr (Nat.cast_nonneg (pairedProduct r)))

theorem distinct_prime_squarefree_mass_bound : ∃ C D : ℝ,0 < C ∧ 0 < D ∧
    ∀ (k a b : ℕ) (i j : Fin k) (y T U V I : ℝ),
    Real.exp 2 ≤ y → 1 < T → 1 ≤ k → 2 ≤ U → U ≤ V →
    (k:ℝ)*(B V-B U+D) ≤ I → ∀ E : Finset (TwoPrimeEncoding k),
    (∀ e ∈ E,DistinctPrimeWitness a b i j y T e) →
    (∀ e ∈ E,Squarefree (pairedProduct e.1)) →
    (∀ e ∈ E,0 < pairedProduct e.1 ∧ pairedProduct e.1=(∏ t,e.1.2 t) ∧
      ((pairedProduct e.1).primeFactorsList.length:ℝ) ≤ I ∧
      ∀ p ∈ (pairedProduct e.1).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V) →
    (∑ e ∈ E,twoPrimeWeight e) ≤
      (C*(B y)^2/(Real.log T)^2)*Real.exp (I*(Real.log k+1)) := by
  classical
  obtain ⟨C,hC,htail⟩ := distinct_prime_reciprocal_tail
  obtain ⟨D,hD,halloc⟩ := squarefree_interval_allocation_bound
  refine ⟨C,D,hC,hD,?_⟩
  intro k a b i j y T U V I hy hT hk hU hUV hI E hE hsq hQ
  let R := E.image Prod.fst
  let M := C*(B y)^2/(Real.log T)^2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hmass : (∑ r ∈ R,(pairedProduct r:ℝ)⁻¹) ≤ Real.exp (I*(Real.log k+1)) := by
    have hR : ∀ r ∈ R,0 < pairedProduct r ∧ pairedProduct r=(∏ j,r.2 j) ∧
        ((pairedProduct r).primeFactorsList.length:ℝ) ≤ I ∧
        ∀ p ∈ (pairedProduct r).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V := by
      intro r hr
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hr
      exact hQ e he
    apply halloc k U V I hk hU hUV hI R
    · exact fun r hr => ⟨(hR r hr).1,(hR r hr).2.1⟩
    · intro r hr
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hr
      exact hsq e he
    · exact fun r hr => (hR r hr).2.2.1
    · exact fun r hr => (hR r hr).2.2.2
  have hmap : ∀ e ∈ E,e.1 ∈ R := fun e he => Finset.mem_image.mpr ⟨e,he,rfl⟩
  have hfiber (r : PairedFactors k) (hr : r ∈ R) :
      (∑ e ∈ E.filter (fun e => e.1=r),twoPrimeWeight e) ≤
        M*(pairedProduct r:ℝ)⁻¹ := by
    exact distinct_prime_fiber_bound i j y T C (htail y T hy hT) E hE r hr
  calc
    _ = ∑ r ∈ R,∑ e ∈ E.filter (fun e => e.1=r),twoPrimeWeight e :=
      (Finset.sum_fiberwise_of_maps_to hmap twoPrimeWeight).symm
    _ ≤ ∑ r ∈ R,M*(pairedProduct r:ℝ)⁻¹ := Finset.sum_le_sum hfiber
    _ = M*(∑ r ∈ R,(pairedProduct r:ℝ)⁻¹) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass hM

end TotientAsymptotic

end

end OAI
