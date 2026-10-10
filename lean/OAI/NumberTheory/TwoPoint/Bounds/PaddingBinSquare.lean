import OAI.NumberTheory.TwoPoint.Bounds.PaddingPairSampling
import OAI.NumberTheory.TwoPoint.Bounds.PaddingPrimeOscillation
import Mathlib.Algebra.Order.Floor.Ring

namespace OAI

/-! The actual bin-square padding average is bounded by the exact difference
small-ball probability, uniformly in a common translation of all bins. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

namespace FiniteLaw

variable {α β : Type*} [Fintype α]

lemma average_finset_sum (μ : FiniteLaw α) (s : Finset β) (F : β → α → ℝ) :
    μ.average (fun x => ∑ b ∈ s, F b x) = ∑ b ∈ s, μ.average (F b) := by
  simp only [average, mul_sum]
  exact sum_comm

lemma partial_collision_bound (μ : FiniteLaw α) (bin : α → β) (B : Finset β) :
    (∑ b ∈ B, (μ.probability (fun x => bin x = b)) ^ 2) ≤
      μ.average (fun x => μ.probability (fun y => bin x = bin y)) := by
  calc
    _ = μ.average (fun x => μ.average (fun y =>
        ∑ b ∈ B, (if bin x = b then 1 else 0) * (if bin y = b then 1 else 0))) := by
      simp only [average_finset_sum]
      apply sum_congr rfl
      intro b _
      simpa only [probability] using square_average_eq μ (fun x => if bin x = b then 1 else 0)
    _ ≤ _ := by
      apply μ.average_mono
      intro x
      apply μ.average_mono
      intro y
      change (∑ b ∈ B, (if bin x = b then (1 : ℝ) else 0) *
        (if bin y = b then 1 else 0)) ≤ if bin x = bin y then 1 else 0
      by_cases h : bin x = bin y
      · have he (b : β) :
            (if bin x = b then (1 : ℝ) else 0) * (if bin y = b then 1 else 0) =
              (if bin x = b then 1 else 0) := by
          by_cases hx : bin x = b <;> simp [hx, ← h]
        simp_rw [he]
        rw [ite_eq_left h]
        by_cases hx : bin x ∈ B <;> simp [hx]
      · rw [ite_eq_right h]
        apply le_of_eq
        apply sum_eq_zero
        intro b _
        by_cases hx : bin x = b
        · have hy : bin y ≠ b := fun hy => h (hx.trans hy.symm)
          simp [hx, hy]
        · simp [hx]

end FiniteLaw

noncomputable def paddingBin (η c x : ℝ) : ℤ := ⌊(x + c) / η⌋

lemma paddingBin_difference {η c x y : ℝ} (hη : 0 < η)
    (h : paddingBin η c x = paddingBin η c y) : |x - y| < η := by
  have hh := Int.abs_sub_lt_one_of_floor_eq_floor h
  have he : (x + c) / η - (y + c) / η = (x - y) / η := by ring
  rw [he, abs_div, abs_of_pos hη] at hh
  exact (div_lt_one hη).mp hh

noncomputable def paddingBinMass (Q : Finset ℕ) (a : Q → Bool) (η c : ℝ) (j : ℤ) : ℝ :=
  (paddingDivisorLaw Q a).probability (fun b => paddingBin η c (paddingLog Q b) = j)

lemma padding_bin_square_small_ball (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 2 ≤ p)
    (η c : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (B : Finset ℤ) :
    (paddingAvailableLaw Q hQ).average (fun a =>
      ∑ j ∈ B, (paddingBinMass Q a η c j) ^ 2) ≤
        (paddingDifferenceLaw Q hQ).probability
          (fun x => |paddingDifferenceValue Q x| ≤ 1) := by
  calc
    _ ≤ (paddingAvailableLaw Q hQ).average (fun a =>
        (paddingDivisorLaw Q a).average (fun b =>
          (paddingDivisorLaw Q a).probability (fun d =>
            paddingBin η c (paddingLog Q b) = paddingBin η c (paddingLog Q d)))) := by
      apply FiniteLaw.average_mono
      intro a
      exact FiniteLaw.partial_collision_bound _ _ _
    _ ≤ (paddingAvailableLaw Q hQ).average (fun a =>
        (paddingDivisorLaw Q a).average (fun b =>
          (paddingDivisorLaw Q a).probability (fun d => |paddingLog Q b - paddingLog Q d| ≤ 1))) := by
      apply FiniteLaw.average_mono
      intro a
      apply FiniteLaw.average_mono
      intro b
      apply FiniteLaw.average_mono
      intro d
      by_cases h : paddingBin η c (paddingLog Q b) = paddingBin η c (paddingLog Q d)
      · have hd := (paddingBin_difference hη h).le.trans hη1
        simp [h, hd]
      · simp [h]
        split_ifs <;> norm_num
    _ = _ := padding_pair_difference_average Q hQ (fun z => if |z| ≤ 1 then 1 else 0)

/-- The manuscript's squared bin mass, with tilted prime availability and
actual independent divisor selections, is `O(1/L)` uniformly in bin location. -/
theorem ModFiveThetaInput.padding_bin_square (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L η c : ℝ) (B : Finset ℤ), 1 ≤ L → 0 < η → η ≤ 1 →
      (paddingAvailableLaw (paddingPrimeSupply E L)
        (fun _ hp => (paddingPrimeSupply_prime hp).two_le)).average (fun a =>
          ∑ j ∈ B, (paddingBinMass (paddingPrimeSupply E L) a η c j) ^ 2) ≤ C / L := by
  obtain ⟨C, hC, hbound⟩ := hP.padding_small_ball E
  exact ⟨C, hC, fun L η c B hL hη hη1 =>
    (padding_bin_square_small_ball _ _ η c hη hη1 B).trans (hbound L hL)⟩

end TwoPointCorrelations

end OAI
