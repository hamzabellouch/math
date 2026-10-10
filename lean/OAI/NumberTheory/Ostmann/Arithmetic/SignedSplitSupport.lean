import OAI.NumberTheory.Ostmann.Arithmetic.JointSplitProbability

namespace OAI

/-! # Signed frequencies in the actual split-support equations -/

namespace Ostmann

open scoped BigOperators Classical

def frequencySignUnit (q : ℕ) (v : ℤ) : (ZMod q)ˣ := if 0 ≤ v then 1 else -1

theorem intCast_frequencySign (q : ℕ) (v : ℤ) :
    (v : ZMod q) = (v.natAbs : ZMod q) * frequencySignUnit q v := by
  by_cases hv : 0 ≤ v
  · have he := congrArg (Int.castRingHom (ZMod q)) (Int.eq_natAbs_of_nonneg hv)
    simpa only [frequencySignUnit, hv, ↓reduceIte, Units.val_one, mul_one,
      Int.coe_castRingHom, Int.cast_natCast] using he
  · have he := congrArg (Int.castRingHom (ZMod q))
      (Int.eq_neg_natAbs_of_nonpos (le_of_not_ge hv))
    simpa only [frequencySignUnit, hv, ↓reduceIte, Units.val_neg, Units.val_one,
      Int.coe_castRingHom, Int.cast_neg, Int.cast_natCast, mul_neg, mul_one] using he

theorem signed_coefficient_equation_iff {q : ℕ} (v w : ℤ) (x y : (ZMod q)ˣ) :
    (v : ZMod q) * x = (w : ZMod q) * y ↔
      (v.natAbs : ZMod q) * (frequencySignUnit q v * x : (ZMod q)ˣ) =
        (w.natAbs : ZMod q) * (frequencySignUnit q w * y : (ZMod q)ˣ) := by
  rw [intCast_frequencySign q v, intCast_frequencySign q w]
  simp only [Units.val_mul, mul_assoc]

theorem common_reduced_modulus {s v w : ℕ} (h : v.gcd s = w.gcd s) :
    reducedFrequency (v.gcd w) s = s / v.gcd s := by
  have hg : (v.gcd w).gcd s = v.gcd s := by
    rw [Nat.gcd_assoc, ← h, ← Nat.gcd_assoc, Nat.gcd_self]
  simp only [reducedFrequency, Nat.gcd_comm s, hg]

/-- Both signs are absorbed into fixed units, and impossible gcd patterns
contribute zero. Thus no soluble-pattern hypothesis is needed. -/
theorem signed_joint_split_probability_le {s t Q : ℕ} [NeZero s] [NeZero t] [NeZero Q]
    (hs : s ∣ Q) (ht : t ∣ Q) (v w v' w' : ℤ)
    (A B P : (ZMod s)ˣ) (A' B' P' : (ZMod t)ˣ) :
    (Fintype.card (ZMod Q)ˣ : ℝ)⁻¹ * (∑ x : (ZMod Q)ˣ,
      if (v : ZMod s) * (A * (P / ZMod.unitsMap hs x) : (ZMod s)ˣ) =
          (w : ZMod s) * (B * ZMod.unitsMap hs x : (ZMod s)ˣ) ∧
        (v' : ZMod t) * (A' * (P' / ZMod.unitsMap ht x) : (ZMod t)ˣ) =
          (w' : ZMod t) * (B' * ZMod.unitsMap ht x : (ZMod t)ˣ)
      then (1 : ℝ) else 0) ≤
      2 * (((reducedFrequency (v.natAbs.gcd w.natAbs) s).lcm
          (reducedFrequency (v'.natAbs.gcd w'.natAbs) t)).divisors.card : ℝ) ^ 2 /
        (reducedFrequency (v.natAbs.gcd w.natAbs) s).lcm
          (reducedFrequency (v'.natAbs.gcd w'.natAbs) t) := by
  simp_rw [signed_coefficient_equation_iff, ← mul_assoc]
  by_cases h : v.natAbs.gcd s = w.natAbs.gcd s
  · by_cases h' : v'.natAbs.gcd t = w'.natAbs.gcd t
    · rw [common_reduced_modulus h, common_reduced_modulus h']
      exact joint_split_probability_le hs ht v.natAbs w.natAbs v'.natAbs w'.natAbs h h'
        (frequencySignUnit s v * A) (frequencySignUnit s w * B) P
        (frequencySignUnit t v' * A') (frequencySignUnit t w' * B') P'
    · have hz (x : (ZMod Q)ˣ) : ¬((v'.natAbs : ZMod t) *
          ((frequencySignUnit t v' * A') * (P' / ZMod.unitsMap ht x) : (ZMod t)ˣ) =
        (w'.natAbs : ZMod t) *
          ((frequencySignUnit t w' * B') * ZMod.unitsMap ht x : (ZMod t)ˣ)) := by
        intro he
        exact h' (unit_coefficient_gcd_eq _ _ _ _ he)
      simp only [hz, and_false, ↓reduceIte, Finset.sum_const_zero, mul_zero]
      positivity
  · have hz (x : (ZMod Q)ˣ) : ¬((v.natAbs : ZMod s) *
          ((frequencySignUnit s v * A) * (P / ZMod.unitsMap hs x) : (ZMod s)ˣ) =
        (w.natAbs : ZMod s) *
          ((frequencySignUnit s w * B) * ZMod.unitsMap hs x : (ZMod s)ˣ)) := by
        intro he
        exact h (unit_coefficient_gcd_eq _ _ _ _ he)
    simp only [hz, false_and, ↓reduceIte, Finset.sum_const_zero, mul_zero]
    positivity

end Ostmann

end OAI
