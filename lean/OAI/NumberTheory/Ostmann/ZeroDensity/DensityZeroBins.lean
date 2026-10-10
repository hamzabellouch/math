import Mathlib.Data.Finset.Sigma
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityLocalMultiplicity

namespace OAI

/-! # Actual zero indices, unit ordinate bins and separated representatives -/

namespace Ostmann

open scoped BigOperators Classical

abbrev DensityZeroIndex := Σ _ : PrimitiveComplexCharacter, ℕ
abbrev DensityZeroBin := Σ _ : PrimitiveComplexCharacter, ℤ

noncomputable def densityZeroIndices (F : Finset PrimitiveComplexCharacter) (σ T : ℝ) :
    Finset DensityZeroIndex :=
  F.sigma fun χ => ((actualCharacterZeros χ).heightIndices T).filter
    (fun i => σ ≤ ((actualCharacterZeros χ).zeros i).re)

noncomputable def densityZeroBin (i : DensityZeroIndex) : DensityZeroBin :=
  ⟨i.1, ⌊((actualCharacterZeros i.1).zeros i.2).im⌋⟩

 theorem densityZeroIndices_mem (F : Finset PrimitiveComplexCharacter) (σ T : ℝ)
    (i : DensityZeroIndex) : i ∈ densityZeroIndices F σ T ↔
      i.1 ∈ F ∧ |((actualCharacterZeros i.1).zeros i.2).im| ≤ T ∧
        σ ≤ ((actualCharacterZeros i.1).zeros i.2).re := by
  simp [densityZeroIndices, ComplexZeroEnumeration.mem_heightIndices]

 theorem densityZeroIndices_card (F : Finset PrimitiveComplexCharacter) (σ T : ℝ) :
    ((densityZeroIndices F σ T).card : ℝ) =
      ∑ χ ∈ F, ((actualCharacterZeros χ).count σ T : ℝ) := by
  simp [densityZeroIndices, Finset.card_sigma, ComplexZeroEnumeration.count]

 theorem densityZeroBin_nonempty (S : Finset DensityZeroIndex) (k : DensityZeroBin)
    (hk : k ∈ S.image densityZeroBin) :
    ∃ n : ℕ, (⟨k.1, n⟩ : DensityZeroIndex) ∈ S ∧
      ⌊((actualCharacterZeros k.1).zeros n).im⌋ = k.2 := by
  obtain ⟨⟨χ, n⟩, hn, he⟩ := Finset.mem_image.mp hk
  cases he
  exact ⟨n, hn, rfl⟩

 theorem densityZeroBin_fiber_bound (Q : ℕ) (hQ : 1 ≤ Q) (T σ : ℝ)
    (hT : 2 ≤ T) (hσ : 1 / 2 ≤ σ) (F : Finset PrimitiveComplexCharacter)
    (hF : ∀ χ ∈ F, χ.modulus ≤ Q) (k : DensityZeroBin) :
    (((densityZeroIndices F σ T).filter fun i => densityZeroBin i = k).card : ℝ) ≤
      (8 / Real.log (14 / 13)) * Real.log ((Q : ℝ) * T) := by
  let S := (densityZeroIndices F σ T).filter fun i => densityZeroBin i = k
  let N := S.image (fun i => i.2)
  have hchar (i : DensityZeroIndex) (hi : i ∈ S) : i.1 = k.1 :=
    congrArg Sigma.fst (Finset.mem_filter.mp hi).2
  have hdata (n : ℕ) (hn : n ∈ N) :
      k.1 ∈ F ∧ |((actualCharacterZeros k.1).zeros n).im| ≤ T ∧
        σ ≤ ((actualCharacterZeros k.1).zeros n).re ∧
        ⌊((actualCharacterZeros k.1).zeros n).im⌋ = k.2 := by
    obtain ⟨⟨χ, m⟩, hm, rfl⟩ := Finset.mem_image.mp hn
    have hc := hchar ⟨χ, m⟩ hm
    dsimp at hc
    subst χ
    have hd := (densityZeroIndices_mem F σ T ⟨k.1, m⟩).mp (Finset.mem_filter.mp hm).1
    have hb := (Finset.mem_filter.mp hm).2
    have hb' : ⌊((actualCharacterZeros k.1).zeros m).im⌋ = k.2 :=
      congrArg (fun x : DensityZeroBin => x.2) hb
    exact ⟨hd.1, hd.2.1, hd.2.2, hb'⟩
  have hinj : Set.InjOn (fun i : DensityZeroIndex => i.2) S := by
    intro i hi j hj he
    exact Sigma.ext ((hchar i hi).trans (hchar j hj).symm) (heq_of_eq he)
  have hcard : N.card = S.card := Finset.card_image_of_injOn hinj
  by_cases hn : N.Nonempty
  · obtain ⟨n, hn⟩ := hn
    have hd := hdata n hn
    have hc := characterOrdinateBins_center_bound T k.2 (by
      rw [← hd.2.2.2]
      exact characterOrdinateBins_mem T _ hd.2.1)
    have hb := density_local_index_log_bound Q hQ T hT k.1 (hF k.1 hd.1) N k.2
      (fun n hn => hσ.trans (hdata n hn).2.2.1)
      (fun n hn => (hdata n hn).2.2.2) hc
    rwa [hcard] at hb
  · have hzero : N.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hn)
    change (S.card : ℝ) ≤ _
    rw [← hcard, hzero, Nat.cast_zero]
    have hq : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    apply mul_nonneg (by positivity)
    exact Real.log_nonneg (by nlinarith)

 theorem densityZeroIndices_bin_bound (Q : ℕ) (hQ : 1 ≤ Q) (T σ : ℝ)
    (hT : 2 ≤ T) (hσ : 1 / 2 ≤ σ) (F : Finset PrimitiveComplexCharacter)
    (hF : ∀ χ ∈ F, χ.modulus ≤ Q) :
    ((densityZeroIndices F σ T).card : ℝ) ≤
      ((densityZeroIndices F σ T).image densityZeroBin).card *
        ((8 / Real.log (14 / 13)) * Real.log ((Q : ℝ) * T)) := by
  rw [Finset.card_eq_sum_card_image densityZeroBin (densityZeroIndices F σ T), Nat.cast_sum]
  calc
    _ ≤ ∑ k ∈ (densityZeroIndices F σ T).image densityZeroBin,
        ((8 / Real.log (14 / 13)) * Real.log ((Q : ℝ) * T)) := by
      exact Finset.sum_le_sum fun k _ => densityZeroBin_fiber_bound Q hQ T σ hT hσ F hF k
    _ = _ := by simp

 theorem density_ordinate_bin_separation (x y : ℝ)
    (hm : ⌊x⌋ % 10 = ⌊y⌋ % 10) (hne : ⌊x⌋ ≠ ⌊y⌋) :
    1 ≤ |x / (2 * Real.pi) - y / (2 * Real.pi)| := by
  have hgap : ⌊x⌋ + 10 ≤ ⌊y⌋ ∨ ⌊y⌋ + 10 ≤ ⌊x⌋ := by omega
  have hphys : 9 ≤ |x - y| := by
    rcases hgap with h | h
    · have hc : (⌊x⌋ : ℝ) + 10 ≤ ⌊y⌋ := by exact_mod_cast h
      have hh : 9 ≤ y - x := by linarith [Int.floor_le y, Int.lt_floor_add_one x]
      rw [abs_sub_comm]
      exact hh.trans (le_abs_self _)
    · have hc : (⌊y⌋ : ℝ) + 10 ≤ ⌊x⌋ := by exact_mod_cast h
      exact (show 9 ≤ x - y by linarith [Int.floor_le x, Int.lt_floor_add_one y]).trans (le_abs_self _)
  rw [← sub_div, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
  nlinarith [Real.pi_lt_four]

end Ostmann

end OAI
