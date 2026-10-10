import OAI.NumberTheory.Ostmann.Characters.RichShellSelectionBlocks

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters

theorem exists_paired_harmonic_blocks : ∃ C : ℝ, 0 < C ∧
    ∀ (E : Finset ℕ), (∀ p ∈ E, p.Prime) → ∀ w A D b ρ L d W : ℝ,
      0 < w → 0 ≤ A → 0 ≤ D → 0 < d → 0 < W → d*b = ρ/4 → w ≤ b*L →
      4*(W+C+1) ≤ ρ*L → 4*(C+2) ≤ ρ*L →
      ρ*L ≤ harmonicIntervalMass E A (A+w) → ρ*L ≤ harmonicIntervalMass E D (D+w) →
      ∃ s R : ℝ, A ≤ s ∧ s+1 ≤ A+w ∧ d ≤ harmonicIntervalMass E s (s+1) ∧
        D ≤ R ∧ R+W ≤ D+w ∧ d*W ≤ harmonicIntervalMass E R (R+W) := by
  obtain ⟨C,hC,hblock⟩ := exists_fixed_width_harmonic_block
  refine ⟨C,hC,?_⟩
  intro E hE w A D b ρ L d W hw hA hD hd hW hdb hwhi hlarge hsmall hmA hmD
  have hdw : d*w ≤ ρ*L/4 := by
    have hh := mul_le_mul_of_nonneg_left hwhi hd.le
    calc
      _ ≤ d*(b*L) := hh
      _ = _ := by rw [← mul_assoc,hdb]; ring
  have hstart : d*((D+w)-D)+W+C < harmonicIntervalMass E D (D+w) := by linarith
  obtain ⟨n,hn,hmn⟩ := hblock E hE D (D+w) W d hD (by linarith) hW hd.le hstart
  let R := D+(n:ℝ)*W
  have hR : D ≤ R := by dsimp [R]; nlinarith [mul_nonneg (Nat.cast_nonneg n) hW.le]
  have hRend : R+W ≤ D+w := by dsimp [R]; nlinarith
  have hmR : d*W ≤ harmonicIntervalMass E R (R+W) := by
    convert hmn using 1; dsimp [R]; congr 1; ring
  have hlow : d*((A+w)-A)+1+C < harmonicIntervalMass E A (A+w) := by linarith
  obtain ⟨l,hl,hml⟩ := hblock E hE A (A+w) 1 d hA (by linarith) zero_lt_one hd.le hlow
  refine ⟨A+(l:ℝ),R,by linarith [Nat.cast_nonneg (α := ℝ) l],?_,?_,hR,hRend,hmR⟩
  · simpa only [mul_one,add_assoc] using hl
  · simpa only [mul_one,add_assoc] using hml

end Ostmann.Characters

end

end OAI
