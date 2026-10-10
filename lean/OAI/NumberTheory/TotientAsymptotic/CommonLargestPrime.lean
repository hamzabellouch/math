import OAI.NumberTheory.TotientAsymptotic.CommonPrimeMass
import OAI.NumberTheory.TotientAsymptotic.RemovePrimeFactor
import OAI.NumberTheory.TotientAsymptotic.LargestPrimeCofactor

namespace OAI

/-! Recoverable extraction of the common largest prime from an actual pair of factors. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def commonLargestEncoding {k : ℕ} (i : Fin k) (f : PairedFactors k) : PairedFactors k × ℕ :=
  let q := largestPrimeFactor (f.1 i)
  ((divideFactor i q f.1,divideFactor i q f.2),q)

def commonPrimeDecode {k : ℕ} (i : Fin k) (e : PairedFactors k × ℕ) : PairedFactors k :=
  (multiplyFactor i e.2 e.1.1,multiplyFactor i e.2 e.1.2)

structure CommonLargestConditions {k : ℕ} (a b : ℕ) (i : Fin k)
    (y T U V I : ℝ) (f : PairedFactors k) : Prop where
  product_pos : 0 < pairedProduct f
  product_eq : pairedProduct f=∏ j,f.2 j
  left_two : 2 ≤ f.1 i
  right_two : 2 ≤ f.2 i
  same_prime : largestPrimeFactor (f.1 i)=largestPrimeFactor (f.2 i)
  prime_lower : T ≤ largestPrimeFactor (f.1 i)
  left_prime : (a*f.1 i+1).Prime
  right_prime : (b*f.2 i+1).Prime
  different : a*f.1 i+1 ≠ b*f.2 i+1
  left_le : ((a*f.1 i:ℕ):ℝ) ≤ y
  right_le : ((b*f.2 i:ℕ):ℝ) ≤ y
  omega_le : ((pairedProduct f).primeFactorsList.length:ℝ) ≤ I
  support : ∀ p ∈ (pairedProduct f).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V

lemma commonLargest_divisors {k a b : ℕ} {i : Fin k} {y T U V I : ℝ} {f : PairedFactors k}
    (hf : CommonLargestConditions a b i y T U V I f) :
    (largestPrimeFactor (f.1 i)).Prime ∧ largestPrimeFactor (f.1 i) ∣ f.1 i ∧
      largestPrimeFactor (f.1 i) ∣ f.2 i := by
  have hl := largestPrimeFactor_mem hf.left_two
  have hr := largestPrimeFactor_mem hf.right_two
  refine ⟨Nat.prime_of_mem_primeFactors hl,Nat.dvd_of_mem_primeFactors hl,?_⟩
  rw [hf.same_prime]
  exact Nat.dvd_of_mem_primeFactors hr

lemma commonLargest_decode {k a b : ℕ} {i : Fin k} {y T U V I : ℝ} {f : PairedFactors k}
    (hf : CommonLargestConditions a b i y T U V I f) :
    commonPrimeDecode i (commonLargestEncoding i f)=f := by
  obtain ⟨_,hl,hr⟩ := commonLargest_divisors hf
  exact Prod.ext (multiply_divideFactor i _ _ hl) (multiply_divideFactor i _ _ hr)

lemma commonLargest_product {k a b : ℕ} {i : Fin k} {y T U V I : ℝ} {f : PairedFactors k}
    (hf : CommonLargestConditions a b i y T U V I f) :
    pairedProduct (commonLargestEncoding i f).1*(commonLargestEncoding i f).2=pairedProduct f := by
  obtain ⟨_,hl,_⟩ := commonLargest_divisors hf
  change (∏ j,divideFactor i (largestPrimeFactor (f.1 i)) f.1 j)*largestPrimeFactor (f.1 i)=pairedProduct f
  rw [mul_comm,prod_divideFactor i _ _ hl]
  rfl

lemma commonLargest_witness {k a b : ℕ} {i : Fin k} {y T U V I : ℝ} {f : PairedFactors k}
    (ha : 0 < a) (hb : 0 < b) (hf : CommonLargestConditions a b i y T U V I f) :
    CommonPrimeWitness a b i y T (commonLargestEncoding i f) := by
  obtain ⟨hq,hl,hr⟩ := commonLargest_divisors hf
  let q := largestPrimeFactor (f.1 i)
  have hl0 : 0 < f.1 i/q := Nat.div_pos (Nat.le_of_dvd (lt_of_lt_of_le (by norm_num : 0 < 2) hf.left_two) hl) hq.pos
  have hr0 : 0 < f.2 i/q := Nat.div_pos (Nat.le_of_dvd (lt_of_lt_of_le (by norm_num : 0 < 2) hf.right_two) hr) hq.pos
  have hele : a*(f.1 i/q) ≤ a*f.1 i := Nat.mul_le_mul_left a (Nat.div_le_self _ _)
  have here : b*(f.2 i/q) ≤ b*f.2 i := Nat.mul_le_mul_left b (Nat.div_le_self _ _)
  have heleR : ((a*(f.1 i/q):ℕ):ℝ) ≤ ((a*f.1 i:ℕ):ℝ) := by exact_mod_cast hele
  have hereR : ((b*(f.2 i/q):ℕ):ℝ) ≤ ((b*f.2 i:ℕ):ℝ) := by exact_mod_cast here
  have hel : a*(f.1 i/q)*q+1=a*f.1 i+1 := by rw [mul_assoc,Nat.div_mul_cancel hl]
  have her : b*(f.2 i/q)*q+1=b*f.2 i+1 := by rw [mul_assoc,Nat.div_mul_cancel hr]
  change CommonPrimeWitness a b i y T ((divideFactor i q f.1,divideFactor i q f.2),q)
  constructor
  · simpa [divideFactor] using Nat.mul_pos ha hl0
  · simpa [divideFactor] using Nat.mul_pos hb hr0
  · simpa [divideFactor] using heleR.trans hf.left_le
  · simpa [divideFactor] using hereR.trans hf.right_le
  · exact hf.prime_lower
  · exact hq
  · simpa only [divideFactor,Function.update_self,hel] using hf.left_prime
  · simpa only [divideFactor,Function.update_self,her] using hf.right_prime
  · simpa only [divideFactor,Function.update_self,hel,her] using hf.different

lemma commonLargest_residual {k a b : ℕ} {i : Fin k} {y T U V I : ℝ} {f : PairedFactors k}
    (hf : CommonLargestConditions a b i y T U V I f) :
    0 < pairedProduct (commonLargestEncoding i f).1 ∧
    pairedProduct (commonLargestEncoding i f).1=(∏ j,(commonLargestEncoding i f).1.2 j) ∧
    ((pairedProduct (commonLargestEncoding i f).1).primeFactorsList.length:ℝ) ≤ I ∧
    ∀ p ∈ (pairedProduct (commonLargestEncoding i f).1).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V := by
  obtain ⟨hq,hl,hr⟩ := commonLargest_divisors hf
  have he := prod_divideFactor i (largestPrimeFactor (f.1 i)) f.1 hl
  have he' := prod_divideFactor i (largestPrimeFactor (f.1 i)) f.2 hr
  refine ⟨divideFactor_prod_pos i _ _ hl hf.product_pos,?_,?_,?_⟩
  · apply Nat.eq_of_mul_eq_mul_left hq.pos
    exact he.trans (hf.product_eq.trans he'.symm)
  · exact (show ((∏ j,divideFactor i (largestPrimeFactor (f.1 i)) f.1 j).primeFactorsList.length:ℝ) ≤
        (pairedProduct f).primeFactorsList.length by
      exact_mod_cast divideFactor_prod_omega_le i _ _ hl hf.product_pos).trans hf.omega_le
  · intro p hp
    exact hf.support p (divideFactor_prod_factors i _ _ hl hf.product_pos hp)

/-- The equal-largest-prime branch, for the original finite family of pairs. -/
theorem common_largest_prime_mass_bound : ∃ C U₀ : ℝ,0 < C ∧ 2 ≤ U₀ ∧
    ∀ (k a b : ℕ) (i : Fin k) (y T U V I : ℝ),0 < a → 0 < b →
    Real.exp 2 ≤ y → 1 ≤ B y → 1 < T → 1 ≤ k → U₀ ≤ U →
    4*(k:ℝ)^2 ≤ U → U ≤ V → (k:ℝ)*(B V-B U+1) ≤ I →
    ∀ Q : Finset (PairedFactors k),
    (∀ f ∈ Q,CommonLargestConditions a b i y T U V I f) →
    (∑ f ∈ Q,(pairedProduct f:ℝ)⁻¹) ≤
      (C*(B y)^2/(Real.log T)^2)*Real.exp (I*(Real.log k+1)+1) := by
  classical
  obtain ⟨C,U₀,hC,hU₀,hbound⟩ := common_prime_mass_bound
  refine ⟨C,U₀,hC,hU₀,?_⟩
  intro k a b i y T U V I ha hb hy hBy hT hk hU hquad hUV hI Q hQ
  let E := Q.image (commonLargestEncoding i)
  have hE : ∀ e ∈ E,CommonPrimeWitness a b i y T e := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    exact commonLargest_witness ha hb (hQ f hf)
  have hres : ∀ e ∈ E,0 < pairedProduct e.1 ∧ pairedProduct e.1=(∏ j,e.1.2 j) ∧
      ((pairedProduct e.1).primeFactorsList.length:ℝ) ≤ I ∧
      ∀ p ∈ (pairedProduct e.1).primeFactorsList,U < (p:ℝ) ∧ (p:ℝ) ≤ V := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    exact commonLargest_residual (hQ f hf)
  have hi : ∀ f ∈ Q,∀ g ∈ Q,commonLargestEncoding i f=commonLargestEncoding i g → f=g := by
    intro f hf g hg he
    have hh := congrArg (commonPrimeDecode i) he
    rwa [commonLargest_decode (hQ f hf),commonLargest_decode (hQ g hg)] at hh
  have hsum : (∑ f ∈ Q,(pairedProduct f:ℝ)⁻¹)=
      ∑ e ∈ E,((pairedProduct e.1*e.2:ℕ):ℝ)⁻¹ := by
    rw [Finset.sum_image hi]
    apply Finset.sum_congr rfl
    intro f hf
    rw [commonLargest_product (hQ f hf)]
  rw [hsum]
  exact hbound k a b i y T U V I hy hBy hT hk hU hquad hUV hI E hE hres

end TotientAsymptotic

end

end OAI
