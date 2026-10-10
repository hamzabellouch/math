import Mathlib
import OAI.Computability.QuantumFactoring.Exactness

namespace OAI

section
open scoped BigOperators


/-! Explicit, uniform O(n) fair-bit lengths for every order-trial retention.
Mere dyadicity would not bound the worst-case circuit cost. -/
namespace ExactQuantumFactoring.OrderTrial
open scoped BigOperators

def DyadicAt (k : ℕ) (x : ℚ) : Prop := ∃ z : ℤ, x=(z:ℚ)/2^k
namespace DyadicAt
lemma integer (k : ℕ) (z : ℤ) : DyadicAt k (z:ℚ) := by
  refine ⟨z*2^k,?_⟩
  push_cast
  field_simp
lemma mono {k l : ℕ} {x : ℚ} (h : DyadicAt k x) (hkl : k≤l) : DyadicAt l x := by
  obtain ⟨z,rfl⟩ := h
  obtain ⟨c,rfl⟩ := Nat.exists_eq_add_of_le hkl
  refine ⟨z*2^c,?_⟩
  push_cast
  rw [pow_add]
  field_simp
lemma add {k : ℕ} {x y : ℚ} (hx : DyadicAt k x) (hy : DyadicAt k y) : DyadicAt k (x+y) := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  exact ⟨a+b,by push_cast; ring⟩
lemma sub {k : ℕ} {x y : ℚ} (hx : DyadicAt k x) (hy : DyadicAt k y) : DyadicAt k (x-y) := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  exact ⟨a-b,by push_cast; ring⟩
lemma mul {k l : ℕ} {x y : ℚ} (hx : DyadicAt k x) (hy : DyadicAt l y) : DyadicAt (k+l) (x*y) := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  refine ⟨a*b,?_⟩
  push_cast
  rw [pow_add]
  ring
lemma int_mul {k : ℕ} {x : ℚ} (z : ℤ) (hx : DyadicAt k x) : DyadicAt k ((z:ℚ)*x) := by
  obtain ⟨a,rfl⟩ := hx
  exact ⟨z*a,by push_cast; ring⟩
end DyadicAt

lemma majorant_at (n d j u : ℕ) : DyadicAt (24*n) (majorant ((2^n)^16) (2^n) d j u) := by
  refine ⟨majorantNumerator ((2^n)^16) (2^n) d j u,?_⟩
  rw [majorant_numerator (by positivity) (by positivity)]
  congr 1
  push_cast
  rw [← pow_mul,← pow_mul,← pow_add]
  congr 1
  omega
lemma majorantSum_at (n d j : ℕ) : DyadicAt (24*n+1) (majorantSum ((2^n)^16) (2^n) d j) := by
  refine ⟨∑ u ∈ Finset.range d, majorantNumerator ((2^n)^16) (2^n) d j u,?_⟩
  rw [majorantSum_numerator (by positivity) (by positivity)]
  congr 1
  push_cast
  rw [← pow_mul,← pow_mul,← pow_add,pow_succ]
  ring_nf
lemma probability_at (n d j t : ℕ) : DyadicAt (64*n) (residueProbabilityRat ((2^n)^16) d j t) := by
  refine ⟨(residueGaussianNumerator ((2^n)^16) d j t).norm,?_⟩
  rw [residueProbabilityRat]
  congr 1
  push_cast
  rw [← pow_mul,← pow_mul]
  congr 1
  omega
lemma coefficient_at (n : ℕ) (lam S : ℚ) : DyadicAt (10*n) (modeCoeff n lam S) := ⟨_,rfl⟩
lemma lambda_at {n d : ℕ} (hd : d≤2^n) : DyadicAt (n+10) (prescribedMass d) := by
  have h : DyadicAt (Nat.clog 2 d+10) (prescribedMass d) := ⟨1,by simp [prescribedMass]⟩
  exact h.mono (Nat.add_le_add_right (Nat.clog_le_of_le_pow hd) 10)
lemma remainder_at {n d : ℕ} (hn : 1≤n) (hd : d≤2^n) (j : ℕ) :
    DyadicAt (34*n+1) (modeRemainder n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j)) := by
  unfold modeRemainder
  apply DyadicAt.sub
  · exact (lambda_at hd).mono (by omega)
  · have h := (coefficient_at n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j)).mul
      (majorantSum_at n d j)
    convert h using 1; omega

noncomputable def discrepancyRetention (n d j t : ℕ) : ℚ :=
  2*((2:ℚ)^n)^3*(majorant ((2^n)^16) (2^n) d j ((j*t)%d)-
    residueProbabilityRat ((2^n)^16) d j t)*modeCoeff n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j)
noncomputable def remainderRetention (n d j : ℕ) : ℚ :=
  4*((2:ℚ)^n)^2*modeRemainder n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j)

lemma discrepancy_at (n d j t : ℕ) : DyadicAt (74*n) (discrepancyRetention n d j t) := by
  have h := ((majorant_at n d j ((j*t)%d)).mono (show 24*n≤64*n by omega)).sub (probability_at n d j t)
  have h' := (h.int_mul (2*(2^n)^3)).mul
    (coefficient_at n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j))
  push_cast at h'
  convert h' using 1 <;> first | rfl | omega
lemma remainderRetention_at {n d : ℕ} (hn : 1≤n) (hd : d≤2^n) (j : ℕ) :
    DyadicAt (34*n+1) (remainderRetention n d j) := by
  have h := (remainder_at hn hd j).int_mul (4*(2^n)^2)
  simpa only [Int.cast_mul,Int.cast_ofNat,Int.cast_pow,remainderRetention] using h

/-- One clock-independent number of bits works for all three modes, on every
valid label, including d=1,j=0. -/
def retentionBits (n : ℕ) := 80*n+20
lemma retentions_fixedDenominator {n d : ℕ} (hn : 1≤n) (hd : d≤2^n) (j t : ℕ) :
    DyadicAt (retentionBits n) (modeCoeff n (prescribedMass d) (majorantSum ((2^n)^16) (2^n) d j)) ∧
    DyadicAt (retentionBits n) (discrepancyRetention n d j t) ∧
    DyadicAt (retentionBits n) (remainderRetention n d j) := by
  exact ⟨(coefficient_at n _ _).mono (by unfold retentionBits; omega),
    (discrepancy_at n d j t).mono (by unfold retentionBits; omega),
    (remainderRetention_at hn hd j).mono (by unfold retentionBits; omega)⟩

lemma retained_numerator {T : ℕ} {x : ℚ} (hx : DyadicAt T x) (h₀ : 0≤x) (h₁ : x≤1) :
    ∃ z : ℕ, z≤2^T ∧ x=(z:ℚ)/2^T ∧ (Int.floor (x*2^T)).toNat=z := by
  obtain ⟨a,ha⟩ := hx
  have hp : (0:ℚ)<2^T := by positivity
  have ha₀ : 0≤a := by
    rw [ha,div_nonneg_iff] at h₀
    rcases h₀ with h | h
    · exact_mod_cast h.1
    · exact False.elim ((not_le_of_gt hp) h.2)
  have ha₁ : a≤(2:ℤ)^T := by
    rw [ha,div_le_one hp] at h₁
    exact_mod_cast h₁
  refine ⟨a.toNat,?_,?_,?_⟩
  · simpa using Int.toNat_le_toNat ha₁
  · have he : (a.toNat:ℚ)=(a:ℚ) := by exact_mod_cast (Int.toNat_of_nonneg ha₀)
    rw [he]; exact ha
  · rw [ha,div_mul_cancel₀ _ hp.ne',Int.floor_intCast]

end ExactQuantumFactoring.OrderTrial


end

end OAI
