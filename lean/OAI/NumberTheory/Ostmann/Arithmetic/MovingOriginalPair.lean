import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalGiantWeight
import OAI.NumberTheory.Ostmann.Arithmetic.PrimePairResidues

namespace OAI

/-! # Exact residue decomposition of the original recursive averages -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

theorem moving_original_prime_pair_residues {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (hg : ∀ i, g i 0 = 0) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hf : T.Frequencies (· ≠ 0)) (M : ℕ) (hM0 : 0 < M)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hMq : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (u v r s : ℝ)
    (hu : ∀ p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊, p.Prime → M < p)
    (hr : ∀ p ∈ Finset.Ioc ⌊Real.exp r⌋₊ ⌊Real.exp s⌋₊, p.Prime → M < p) :
    let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
    complexPrimeInterval 1 0 r s (fun y => complexPrimeInterval 1 0 u v (fun x =>
      movingOriginalGiantWeight q value childBound pivotBound F E g Dq S ψ X lo hi φ G T t
        ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) =
      ∑ b ∈ reducedResidues M, ∑ a ∈ reducedResidues M,
        complexPrimeInterval M b r s (fun y => complexPrimeInterval M a u v (fun x =>
          movingResidueCoefficient q value F E g Dq S T nodes a b *
            movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y))) := by
  dsimp only
  apply prime_pair_residue_factorization M hM0 u v r s hu hr
  intro p hp hpp z hz hzp a ha b hb hpa hzb
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hz0 : (0 : ℝ) < z := by exact_mod_cast hzp.pos
  rw [Real.exp_log hp0, Real.exp_log hz0]
  exact movingOriginalGiantWeight_factor q value hvalue childBound pivotBound F E g hg Dq S
    ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout T t hT hf p z a b M hM hMq
    (Int.natCast_modEq_iff.mpr hpa) (Int.natCast_modEq_iff.mpr hzb)

theorem moving_original_mixed_pair_residues {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (hg : ∀ i, g i 0 = 0) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hf : T.Frequencies (· ≠ 0)) (M : ℕ) (hM0 : 0 < M)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hMq : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (u v r s J : ℝ)
    (hr : ∀ p ∈ Finset.Ioc ⌊Real.exp r⌋₊ ⌊Real.exp s⌋₊, p.Prime → M < p) :
    let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
    complexPrimeInterval 1 0 r s (fun y => complexIntegerInterval 1 0 u v J (fun x =>
      movingOriginalGiantWeight q value childBound pivotBound F E g Dq S ψ X lo hi φ G T t
        ⌊Real.exp x⌋₊ ⌊Real.exp y⌋₊)) =
      ∑ b ∈ reducedResidues M, ∑ a ∈ Finset.range M,
        complexPrimeInterval M b r s (fun y => complexIntegerInterval M a u v J (fun x =>
          movingResidueCoefficient q value F E g Dq S T nodes a b *
            movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y))) := by
  dsimp only
  apply mixed_pair_residue_factorization M hM0 u v r s J hr
  intro p hp z hz hzp a ha b hb hpa hzb
  have hp0 : (0 : ℝ) < p :=
    (Real.exp_pos u).trans (Nat.lt_of_floor_lt (Finset.mem_Ioc.mp hp).1)
  have hz0 : (0 : ℝ) < z := by exact_mod_cast hzp.pos
  rw [Real.exp_log hp0, Real.exp_log hz0]
  exact movingOriginalGiantWeight_factor q value hvalue childBound pivotBound F E g hg Dq S
    ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout T t hT hf p z a b M hM hMq
    (Int.natCast_modEq_iff.mpr hpa) (Int.natCast_modEq_iff.mpr hzb)

end Ostmann

end OAI
