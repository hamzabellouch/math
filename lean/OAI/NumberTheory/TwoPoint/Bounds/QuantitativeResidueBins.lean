import OAI.NumberTheory.TwoPoint.Bounds.QuantitativeRoughBins

namespace OAI

/-! The progression class in a partial centering term depends on the
rough shift. Splitting by its residue costs exactly the fixed modulus. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma sum_modulus_fibres (l : ℕ) [NeZero l] (Z : Finset ℕ)
    (F : ZMod l → ℕ → ℂ) :
    (∑ r : ZMod l, ∑ z ∈ Z.filter (fun z : ℕ => (z : ZMod l) = r), F r z) =
      ∑ z ∈ Z, F (z : ZMod l) z := by
  simp only [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro z _
  simp

noncomputable def residueScaledRoughProfile (l : ℕ) [NeZero l] (b : ZMod l)
    (Z : Finset ℕ) (h n : ℕ) : ℂ :=
  ∑ z ∈ Z, (z : ℂ)⁻¹ *
    (progressionSequence liouville l (b * (z : ZMod l)) n * liouville (n + h * z))

noncomputable def residueScaledRoughAverage (l : ℕ) [NeZero l] (b : ZMod l)
    (Z : Finset ℕ) (h Y : ℕ) : ℂ :=
  positivePrefix (residueScaledRoughProfile l b Z h) Y / (Y : ℂ)

lemma residueScaledRoughProfile_partition (l : ℕ) [NeZero l] (b : ZMod l)
    (Z : Finset ℕ) (h n : ℕ) :
    residueScaledRoughProfile l b Z h n =
      ∑ r : ZMod l, roughShiftProfile (progressionSequence liouville l (b * r))
        liouville (Z.filter (fun z : ℕ => (z : ZMod l) = r)) h n := by
  exact (sum_modulus_fibres l Z (fun r z => (z : ℂ)⁻¹ *
    (progressionSequence liouville l (b * r) n * liouville (n + h * z)))).symm

lemma residueScaledRoughAverage_partition (l : ℕ) [NeZero l] (b : ZMod l)
    (Z : Finset ℕ) (h Y : ℕ) :
    residueScaledRoughAverage l b Z h Y =
      ∑ r : ZMod l, roughShiftAverage (progressionSequence liouville l (b * r))
        liouville (Z.filter (fun z : ℕ => (z : ZMod l) = r)) h Y := by
  simp only [residueScaledRoughAverage, positivePrefix, residueScaledRoughProfile_partition,
    roughShiftAverage]
  rw [sum_comm, sum_div]

theorem quantitative_residue_bin (hM : PrimeReciprocalInput)
    (hMRT : MRTLiouvilleShortInput) (h : ℕ) (hh : 0 < h) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (Y l : ℕ), Real.exp ((1 / 2 : ℝ) * L ^ (1000 : ℝ)) ≤ (Y : ℝ) →
      ∀ [NeZero l] (b : ZMod l) (M τ : ℝ), 0 < τ → τ < 2 →
      ∀ Z : Finset ℕ,
      (∀ z ∈ Z, M ≤ (z : ℝ) ∧ (z : ℝ) ≤ τ * M ∧
        Real.exp (L ^ (199 / 200 : ℝ)) ≤ (z : ℝ) ∧ (z : ℝ) ≤ Real.exp (2 * L) ∧
        avoidsPrimeSet (sievePrimesUpTo (Real.exp (L ^ (99 / 100 : ℝ)))) z) →
      ‖residueScaledRoughAverage l b Z h Y‖ ≤ (l : ℝ) * C * L ^ (-21 / 20 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := quantitative_rough_real_bin hM hMRT h hh
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with L hb
  intro Y l hY _ b M τ hτ hτtwo Z hZ
  rw [residueScaledRoughAverage_partition]
  calc
    _ ≤ ∑ r : ZMod l, ‖roughShiftAverage (progressionSequence liouville l (b * r))
        liouville (Z.filter (fun z : ℕ => (z : ZMod l) = r)) h Y‖ := norm_sum_le _ _
    _ ≤ ∑ _r : ZMod l, C * L ^ (-21 / 20 : ℝ) := by
      apply sum_le_sum
      intro r _
      exact hb Y l hY (b * r) M τ hτ hτtwo _ (fun z hz => hZ z (mem_filter.mp hz).1)
    _ = _ := by simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]; ring

end TwoPointCorrelations

end OAI
