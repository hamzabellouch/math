import OAI.NumberTheory.EgyptianFractions.PrimeFactorPrefix
import OAI.NumberTheory.EgyptianFractions.DyadicBands

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.DivisorClasses

attribute [local instance] Classical.propDecidable

/-- The selected sorted prime-factor prefix, including both separation facts. -/
def PrefixWitness (n : ℕ) (Y : ℝ) (d p : ℕ) : Prop :=
  0 < d ∧ p.Prime ∧ d ∣ n ∧ (d : ℝ) ≤ Real.sqrt Y ∧
    Real.sqrt Y < (d * p : ℕ) ∧ p ∣ n / d ∧
    (∀ q : ℕ, q.Prime → q ∣ d → q ≤ p) ∧
    (∀ q : ℕ, q.Prime → q ∣ n / d → p ≤ q)

def LargeClass (n : ℕ) (v Y : ℝ) : Prop :=
  (n : ℝ) ≤ Real.sqrt Y ∨ ∃ d p : ℕ,
    PrefixWitness n Y d p ∧ v ^ (15 / 16 : ℝ) ≤ Real.log p

def SmallClass (n : ℕ) (S v Y : ℝ) : Prop :=
  ∃ d p : ℕ, PrefixWitness n Y d p ∧
    Real.log p < v ^ (15 / 16 : ℝ) ∧ Real.log p < 4 * Real.log S

def BandClass (n : ℕ) (S v Y : ℝ) (j : ℕ) : Prop :=
  ∃ d p : ℕ, PrefixWitness n Y d p ∧
    Real.log p < v ^ (15 / 16 : ℝ) ∧
    DyadicBands.InBand (4 * Real.log S) j (Real.log p)

/-- Every integer belongs to one of the three actual prime-prefix regimes.
No choice of prefix, divisor estimate, or distribution assertion is assumed. -/
theorem class_cover (n : ℕ) (S v Y : ℝ) (J : ℕ)
    (hY : 1 ≤ Real.sqrt Y)
    (hbands : ∀ w : ℝ, 4 * Real.log S ≤ w → w < v ^ (15 / 16 : ℝ) →
      ∃ j : ℕ, j < J ∧ DyadicBands.InBand (4 * Real.log S) j w) :
    LargeClass n v Y ∨ SmallClass n S v Y ∨
      ∃ j : ℕ, j < J ∧ BandClass n S v Y j := by
  by_cases hn : (n : ℝ) ≤ Real.sqrt Y
  · exact Or.inl (Or.inl hn)
  obtain ⟨d, p, hpref⟩ := prime_factor_prefix n (Real.sqrt Y) hY (lt_of_not_ge hn)
  have hw : PrefixWitness n Y d p := hpref
  by_cases hp : v ^ (15 / 16 : ℝ) ≤ Real.log p
  · exact Or.inl (Or.inr ⟨d, p, hw, hp⟩)
  have hphi : Real.log p < v ^ (15 / 16 : ℝ) := lt_of_not_ge hp
  by_cases hsmall : Real.log p < 4 * Real.log S
  · exact Or.inr (Or.inl ⟨d, p, hw, hphi, hsmall⟩)
  obtain ⟨j, hj, hband⟩ := hbands (Real.log p) (le_of_not_gt hsmall) hphi
  exact Or.inr (Or.inr ⟨j, hj, d, p, hw, hphi, hband⟩)

/-- An occupied intermediate class automatically has an admissible lower scale. -/
theorem band_scale_lt {n : ℕ} {S v Y : ℝ} {j : ℕ}
    (h : BandClass n S v Y j) :
    4 * Real.log S * 2 ^ j < v ^ (15 / 16 : ℝ) := by
  obtain ⟨d, p, _, hp, hband⟩ := h
  exact hband.1.trans_lt hp

/-- Finite summation over the actual regimes. Overlap of prefix witnesses is
harmless because all weights are nonnegative. -/
theorem sum_le_class_bounds {ι : Type*} (H : Finset ι) (n : ι → ℕ)
    (w : ι → ℝ) (S v Y : ℝ) (J : ℕ) (L M A : ℝ)
    (hY : 1 ≤ Real.sqrt Y)
    (hbands : ∀ x : ℝ, 4 * Real.log S ≤ x → x < v ^ (15 / 16 : ℝ) →
      ∃ j : ℕ, j < J ∧ DyadicBands.InBand (4 * Real.log S) j x)
    (hw : ∀ i ∈ H, 0 ≤ w i)
    (hlarge : (∑ i ∈ H with LargeClass (n i) v Y, w i) ≤ L)
    (hsmall : (∑ i ∈ H with SmallClass (n i) S v Y, w i) ≤ M)
    (hband : ∀ j < J, (∑ i ∈ H with BandClass (n i) S v Y j, w i) ≤ A) :
    (∑ i ∈ H, w i) ≤ L + M + (J : ℝ) * A := by
  classical
  have hpoint : ∀ i ∈ H, w i ≤
      (if LargeClass (n i) v Y then w i else 0) +
      (if SmallClass (n i) S v Y then w i else 0) +
      ∑ j ∈ Finset.range J, if BandClass (n i) S v Y j then w i else 0 := by
    intro i hi
    have hl0 : 0 ≤ if LargeClass (n i) v Y then w i else 0 := by
      split_ifs <;> simp_all
    have hs0 : 0 ≤ if SmallClass (n i) S v Y then w i else 0 := by
      split_ifs <;> simp_all
    have hb0 : ∀ j : ℕ, 0 ≤ if BandClass (n i) S v Y j then w i else 0 := by
      intro j
      split_ifs <;> simp_all
    have hsum0 := Finset.sum_nonneg (s := Finset.range J) (fun j _ => hb0 j)
    rcases class_cover (n i) S v Y J hY hbands with hl | hs | ⟨j, hj, hb⟩
    · rw [ite_eq_left hl]
      linarith
    · rw [ite_eq_left hs]
      linarith
    · have hsingle := Finset.single_le_sum (s := Finset.range J)
        (fun j _ => hb0 j) (Finset.mem_range.mpr hj)
      rw [ite_eq_left hb] at hsingle
      linarith
  calc
    (∑ i ∈ H, w i) ≤ ∑ i ∈ H,
        ((if LargeClass (n i) v Y then w i else 0) +
        (if SmallClass (n i) S v Y then w i else 0) +
        ∑ j ∈ Finset.range J, if BandClass (n i) S v Y j then w i else 0) :=
      Finset.sum_le_sum hpoint
    _ = (∑ i ∈ H with LargeClass (n i) v Y, w i) +
        (∑ i ∈ H with SmallClass (n i) S v Y, w i) +
        ∑ j ∈ Finset.range J, ∑ i ∈ H with BandClass (n i) S v Y j, w i := by
      simp only [Finset.sum_add_distrib, Finset.sum_filter]
      rw [Finset.sum_comm]
    _ ≤ L + M + ∑ _j ∈ Finset.range J, A := by
      apply add_le_add (add_le_add hlarge hsmall)
      exact Finset.sum_le_sum (fun j hj => hband j (Finset.mem_range.mp hj))
    _ = L + M + (J : ℝ) * A := by simp

end Problem337.DivisorClasses

end

end OAI
