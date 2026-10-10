import OAI.NumberTheory.EgyptianFractions.FiveProducts

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337.ThreePrimeLocalFactor

/-- Orthogonality with the zero residue removed. -/
theorem nonzero_character_sum {p : ℕ} [NeZero p] (t : ZMod p) :
    (∑ a ∈ (Finset.univ : Finset (ZMod p)).erase 0,
      ZMod.stdAddChar (t * a)) =
      if t = 0 then (p : ℂ) - 1 else -1 := by
  classical
  have hsum := FiveProducts.character_sum t
  have hsplit := Finset.sum_erase_add
    (s := (Finset.univ : Finset (ZMod p)))
    (fun a => ZMod.stdAddChar (t * a)) (Finset.mem_univ 0)
  simp only [mul_zero, AddChar.map_zero_eq_one] at hsplit
  rw [hsum] at hsplit
  split_ifs at hsplit ⊢ <;> linear_combination hsplit

/-- The prime-modulus Ramanujan sum, indexed by nonzero residues. -/
def primeRamanujanSum (p : ℕ) [NeZero p] (u : ℕ) : ℂ :=
  ∑ a ∈ (Finset.univ : Finset (ZMod p)).erase 0,
    ZMod.stdAddChar (-(u : ZMod p) * a)

/-- Removing the zero frequency from character orthogonality gives the
prime Ramanujan sum. In fact this formula needs only a nonzero modulus. -/
theorem primeRamanujanSum_eq (p : ℕ) [NeZero p] (u : ℕ) :
    primeRamanujanSum p u = if p ∣ u then (p : ℂ) - 1 else -1 := by
  simpa only [primeRamanujanSum, neg_eq_zero, ZMod.natCast_eq_zero_iff] using
    nonzero_character_sum (-(u : ZMod p))

/-- The normalized cubic prime-frequency contribution to the ternary
singular series. -/
def localFactor (p u : ℕ) [NeZero p] : ℂ :=
  1 - primeRamanujanSum p u / ((p : ℂ) - 1) ^ 3

/-- The two familiar local factors follow exactly from finite character
orthogonality; this is not an asymptotic prime-counting assertion. -/
theorem localFactor_eq (p u : ℕ) (hp : p.Prime) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    localFactor p u =
      if p ∣ u then 1 - 1 / ((p : ℂ) - 1) ^ 2
      else 1 + 1 / ((p : ℂ) - 1) ^ 3 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hp1 : (p : ℂ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [localFactor, primeRamanujanSum_eq]
  split_ifs
  · field_simp
  · ring

/-- The normalized cubic exponential-sum contribution of the nonzero
frequencies at a prime modulus. -/
def cubicPrimeCoefficient (p u : ℕ) [NeZero p] : ℂ :=
  ∑ a ∈ (Finset.univ : Finset (ZMod p)).erase 0,
    ((∑ b ∈ (Finset.univ : Finset (ZMod p)).erase 0,
      ZMod.stdAddChar (a * b)) / ((p : ℂ) - 1)) ^ 3 *
      ZMod.stdAddChar (-(u : ZMod p) * a)

/-- The cubic coefficient is exactly the signed, normalized Ramanujan sum.
Thus the local Euler factor is the zero-frequency contribution plus the
actual nonzero-frequency cubic sum. -/
theorem cubicPrimeCoefficient_eq (p u : ℕ) [NeZero p] :
    cubicPrimeCoefficient p u =
      -primeRamanujanSum p u / ((p : ℂ) - 1) ^ 3 := by
  classical
  unfold cubicPrimeCoefficient
  calc
    _ = ∑ a ∈ (Finset.univ : Finset (ZMod p)).erase 0,
        (-1 / ((p : ℂ) - 1) ^ 3) *
          ZMod.stdAddChar (-(u : ZMod p) * a) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [nonzero_character_sum, ite_eq_right (Finset.mem_erase.mp ha).1, div_pow]
      norm_num
    _ = (-1 / ((p : ℂ) - 1) ^ 3) * primeRamanujanSum p u := by
      rw [← Finset.mul_sum]
      rfl
    _ = _ := by ring

theorem one_add_cubicPrimeCoefficient (p u : ℕ) [NeZero p] :
    1 + cubicPrimeCoefficient p u = localFactor p u := by
  rw [cubicPrimeCoefficient_eq, localFactor]
  ring

/-- A real-valued statement of the local factor for direct use with real
Euler products. -/
theorem one_add_cubicPrimeCoefficient_eq_real (p u : ℕ) (hp : p.Prime) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    1 + cubicPrimeCoefficient p u =
      ((if p ∣ u then 1 - 1 / ((p : ℝ) - 1) ^ 2
        else 1 + 1 / ((p : ℝ) - 1) ^ 3 : ℝ) : ℂ) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  rw [one_add_cubicPrimeCoefficient, localFactor_eq p u hp]
  split_ifs <;> push_cast <;> rfl

end Problem337.ThreePrimeLocalFactor

end

end OAI
