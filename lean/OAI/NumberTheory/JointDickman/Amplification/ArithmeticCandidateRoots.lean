import OAI.NumberTheory.JointDickman.Amplification.ArithmeticGraphPair
import OAI.NumberTheory.JointDickman.Amplification.CandidateModularRoots

namespace OAI

/-! # The arithmetic quotient and its candidate root -/

namespace JointDickman
open Finset

/-- The reconstructed multiplier satisfies the exact affine equation before
any residue model or exceptional event is introduced. -/
theorem divisorEdgeInverse_equation {a b c N : ℕ} {j : ℤ}
    (ha : 0 < a) (hc : 0 < c) (he : (a : ℤ)-b = j*c)
    (hcop : a.Coprime j.natAbs) {n : ℕ}
    (hn : n ∈ divisorEdgeNew a b c N j) :
    a*b*divisorEdgeInverse a b c n+b = c*n := by
  obtain ⟨hm,hback⟩ := divisorEdge_inverse_mem ha hc he hcop hn
  obtain ⟨_,_,_,hca,_⟩ := mem_filter.mp hm
  calc
    _ = b*(a*divisorEdgeInverse a b c n+1) := by ring
    _ = b*(c*((a*divisorEdgeInverse a b c n+1)/c)) := by
      rw [Nat.mul_div_cancel' hca]
    _ = c*(b*((a*divisorEdgeInverse a b c n+1)/c)) := by ring
    _ = _ := by rw [hback]

/-- Outside coefficient primes the remaining arithmetic argument has the
ordinary linear root used by the candidate model. -/
theorem affine_quotient_prime_root {a b c m n p : ℕ} [Fact p.Prime]
    (he : a*b*m+b = c*n) (ha : ¬ p ∣ a) (hb : ¬ p ∣ b)
    (hc : ¬ p ∣ c) :
    p ∣ m ↔ (n : ZMod p) = (b : ZMod p)/(c : ZMod p) := by
  have ha0 : (a : ZMod p) ≠ 0 := fun h => ha ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hb0 : (b : ZMod p) ≠ 0 := fun h => hb ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hc0 : (c : ZMod p) ≠ 0 := fun h => hc ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hz : (a : ZMod p)*b*m+b = (c : ZMod p)*n := by
    simpa only [Nat.cast_add,Nat.cast_mul] using congrArg (fun t : ℕ => (t : ZMod p)) he
  rw [← ZMod.natCast_eq_zero_iff, eq_div_iff hc0]
  constructor
  · intro hm
    simpa only [hm,mul_zero,zero_add,mul_comm] using hz.symm
  · intro hn
    have hm : (a : ZMod p)*b*m = 0 := by linear_combination hz + hn
    exact (mul_eq_zero.mp hm).resolve_left (mul_ne_zero ha0 hb0)

/-- A prime of the third coefficient cannot divide the remaining argument. -/
theorem affine_quotient_no_third_coefficient {a b c m n p : ℕ} [Fact p.Prime]
    (he : a*b*m+b = c*n) (hb : ¬ p ∣ b) (hc : p ∣ c) : ¬ p ∣ m := by
  intro hm
  have hleft : p ∣ a*b*m+b := by
    rw [he]
    exact dvd_mul_of_dvd_left hc n
  have habm : p ∣ a*b*m := dvd_mul_of_dvd_right hm (a*b)
  exact hb ((Nat.dvd_add_iff_right habm).mpr hleft)

/-- For a coefficient with exactly one factor of `p`, testing the quotient
for `p` is a test of the original numerator modulo `p²`. -/
theorem prime_square_product_iff {p d m : ℕ} (hp : p.Prime)
    (hd : p ∣ d) (hdd : ¬ p^2 ∣ d) : p^2 ∣ d*m ↔ p ∣ m := by
  obtain ⟨k,rfl⟩ := hd
  have hk : ¬ p ∣ k := by
    intro h
    apply hdd
    simpa only [pow_two] using Nat.mul_dvd_mul_left p h
  rw [pow_two,mul_assoc,Nat.mul_dvd_mul_iff_left hp.pos]
  exact ⟨fun h => (hp.dvd_mul.mp h).resolve_left hk, fun h => dvd_mul_of_dvd_right h k⟩

theorem affine_quotient_coefficient_root {a b c m n p : ℕ} (hp : p.Prime)
    (he : a*b*m+b = c*n) (hpab : p ∣ a*b) (hpab2 : ¬ p^2 ∣ a*b) :
    p ∣ m ↔ p^2 ∣ c*n-b := by
  have hsub : c*n-b = a*b*m := by omega
  rw [hsub]
  exact (prime_square_product_iff hp hpab hpab2).symm

/-- With the manuscript's site indexing, the linear root is precisely
`candidateModRoot`, not a new independently specified residue. -/
theorem candidate_affine_quotient_root {M p u m : ℕ} [Fact p.Prime]
    (e : BlockCandidateIndex M)
    (he : candidateHigh e*candidateLow e*m+candidateLow e =
      candidateQuotient e*(u+(e.1.1.val+1)))
    (ha : ¬ p ∣ candidateHigh e) (hb : ¬ p ∣ candidateLow e)
    (hc : ¬ p ∣ candidateQuotient e) :
    p ∣ m ↔ (u : ZMod p) = candidateModRoot p e := by
  rw [affine_quotient_prime_root he ha hb hc]
  have hc0 : (candidateQuotient e : ZMod p) ≠ 0 :=
    fun h => hc ((ZMod.natCast_eq_zero_iff _ _).mp h)
  unfold candidateModRoot candidateRootNumerator
  simp only [Nat.cast_add,Nat.cast_one,Int.cast_sub,Int.cast_natCast,Int.cast_mul,
    Int.cast_add,Int.cast_one]
  rw [eq_div_iff hc0,eq_div_iff hc0]
  constructor <;> intro h <;> linear_combination h

end JointDickman

end OAI
