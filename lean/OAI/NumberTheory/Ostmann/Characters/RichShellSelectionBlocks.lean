import OAI.NumberTheory.Ostmann.Characters.RichShellSelectionMass

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters

theorem exists_fixed_width_harmonic_block : ∃ C : ℝ, 0 < C ∧
    ∀ (E : Finset ℕ), (∀ p ∈ E, p.Prime) → ∀ a b W d : ℝ,
      0 ≤ a → a ≤ b → 0 < W → 0 ≤ d →
      d*(b-a)+W+C < harmonicIntervalMass E a b →
      ∃ i : ℕ, a+((i:ℝ)+1)*W ≤ b ∧
        d*W ≤ harmonicIntervalMass E (a+i*W) (a+((i:ℝ)+1)*W) := by
  obtain ⟨C,hC,hcap⟩ := harmonicIntervalMass_mertens
  refine ⟨C,hC,?_⟩
  intro E hE a b W d ha hab hW hd hmass
  let N := ⌊(b-a)/W⌋₊
  have hfloor : (N:ℝ)*W ≤ b-a :=
    (le_div_iff₀ hW).mp (Nat.floor_le (div_nonneg (sub_nonneg.mpr hab) hW.le))
  have htail : b-a < ((N:ℝ)+1)*W := (div_lt_iff₀ hW).mp (Nat.lt_floor_add_one ((b-a)/W))
  have hlo : a ≤ a+(N:ℝ)*W := by nlinarith [mul_nonneg (Nat.cast_nonneg N) hW.le]
  have hsplit := harmonicIntervalMass_add E hlo (by linarith : a+(N:ℝ)*W ≤ b)
  have hrest := hcap E hE (a+(N:ℝ)*W) b (ha.trans hlo) (by linarith)
  have hprefix : d*((N:ℝ)*W) < harmonicIntervalMass E a (a+(N:ℝ)*W) := by
    have := mul_le_mul_of_nonneg_left hfloor hd
    linarith
  have hsum := harmonicIntervalMass_grid E a W hW.le N
  have hex : ∃ i ∈ Finset.range N,
      d*W ≤ harmonicIntervalMass E (a+(i:ℝ)*W) (a+((i:ℝ)+1)*W) := by
    by_contra hn
    push Not at hn
    have hs := Finset.sum_le_sum (fun i hi => (hn i hi).le)
    have hs' : (∑ i ∈ Finset.range N, harmonicIntervalMass E (a+(i:ℝ)*W) (a+((i:ℝ)+1)*W)) ≤
        (N:ℝ)*(d*W) := by simpa using hs
    rw [hsum] at hs'
    nlinarith
  obtain ⟨i,hi,him⟩ := hex
  have hiN : ((i:ℝ)+1) ≤ N := by exact_mod_cast Finset.mem_range.mp hi
  refine ⟨i,?_,him⟩
  nlinarith [mul_le_mul_of_nonneg_right hiN hW.le]

theorem exists_rich_grid_unit_shell : ∃ C : ℝ, 0 < C ∧
    ∀ (E : Finset ℕ), (∀ p ∈ E, p.Prime) → ∀ U x y d : ℝ,
      0 ≤ U → U ≤ x → x+1 ≤ y → 0 ≤ d →
      d*(y-x)+C < harmonicIntervalMass E x y →
      ∃ i : ℕ, x ≤ U+(i:ℝ) ∧ U+(i:ℝ)+1 ≤ y ∧
        d ≤ harmonicIntervalMass E (U+(i:ℝ)) (U+(i:ℝ)+1) := by
  obtain ⟨C,hC,hcap⟩ := harmonicIntervalMass_mertens
  obtain ⟨B,hB,hblock⟩ := exists_fixed_width_harmonic_block
  refine ⟨C+B+2,by linarith,?_⟩
  intro E hE U x y d hU hUx hxy hd hmass
  let n := ⌈x-U⌉₊
  let a := U+(n:ℝ)
  have hxa : x ≤ a := by have := Nat.le_ceil (x-U); dsimp [a,n]; linarith
  have hax : a < x+1 := by
    have := Nat.ceil_lt_add_one (sub_nonneg.mpr hUx)
    dsimp [a,n]
    linarith
  have hay : a ≤ y := by linarith
  have hx0 : 0 ≤ x := hU.trans hUx
  have hl := hcap E hE x a hx0 hxa
  have he := harmonicIntervalMass_add E hxa hay
  have hm : d*(y-a)+1+B < harmonicIntervalMass E a y := by
    have := mul_le_mul_of_nonneg_left (show y-a ≤ y-x by linarith) hd
    linarith
  obtain ⟨i,hi,hdi⟩ := hblock E hE a y 1 d (hx0.trans hxa) hay zero_lt_one hd hm
  refine ⟨n+i,?_,?_,?_⟩
  · push_cast
    dsimp [a] at hxa
    linarith [Nat.cast_nonneg (α := ℝ) i]
  · simpa only [a,Nat.cast_add,mul_one,add_assoc] using hi
  · simpa only [a,Nat.cast_add,mul_one,add_assoc] using hdi

end Ostmann.Characters

end

end OAI
