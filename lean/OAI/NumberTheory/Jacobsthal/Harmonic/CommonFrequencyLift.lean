import OAI.NumberTheory.Jacobsthal.Estimates.PrimitiveThreeQuarters
import OAI.NumberTheory.Jacobsthal.Partitions.UnitReductionFibres

namespace OAI

namespace Erdos970

section

open scoped BigOperators
namespace ErdosKloosterman.PrimePower

theorem common_frequency_lift_product (p s : ℕ) [Fact p.Prime] (hs : 0 < s)
    (h k : ℤ) :
    standardSum (p*p^s) ((p : ℤ)*h) ((p : ℤ)*k) =
      (p : ℂ) * standardSum (p^s) h k := by
  unfold standardSum sum
  simp_rw [scaled_phase_reduction p (p^s) h k]
  convert! sum_comp_unit_reduction p s hs
    (fun u : (ZMod (p^s))ˣ => (ZMod.stdAddChar (N := p^s)) ((h : ZMod (p^s))*(u : ZMod (p^s)) +
      (k : ZMod (p^s))*(↑u⁻¹ : ZMod (p^s)))) using 1
  · apply Finset.sum_congr (by ext u; simp)
    intro u _
    rfl
  · congr 1
    apply Finset.sum_congr (by ext u; simp)
    intro u _
    rfl

theorem common_frequency_lift (p s : ℕ) [Fact p.Prime] (hs : 0 < s) (h k : ℤ) :
    standardSum (p^(s+1)) ((p : ℤ)*h) ((p : ℤ)*k) =
      (p : ℂ) * standardSum (p^s) h k := by
  rw [standardSum_modulus_congr _ (p*p^s) (pow_succ' p s)]
  exact common_frequency_lift_product p s hs h k

theorem common_frequency_gcd (p s : ℕ) (h k : ℤ) :
    Nat.gcd (p^(s+1)) (Int.gcd ((p : ℤ)*h) ((p : ℤ)*k)) =
      p * Nat.gcd (p^s) (Int.gcd h k) := by
  rw [pow_succ', Int.gcd_mul_left, Int.natAbs_natCast, Nat.gcd_mul_left]

end ErdosKloosterman.PrimePower

end

end Erdos970

end OAI
