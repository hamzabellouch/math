import OAI.NumberTheory.TwoPoint.Walks.CanonicalPartialCentering
import OAI.NumberTheory.TwoPoint.Bounds.PaddingBinCount

namespace OAI

/-! Sum the actual partial-centering errors over the logarithmic bins.
The interval exponent remains the absolute value 1000. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

lemma bin_cutoff_ge (L η X : ℝ) (hη : 0 < η) (hX : 0 ≤ X)
    (j : ℤ) (hj : j ∈ paddingBinIndices L η) :
    X ≤ X * Real.exp ((j : ℝ) * η) := by
  have hj0 : (0 : ℝ) ≤ j := by
    exact_mod_cast ((mem_paddingBinIndices_iff L η j hη).mp hj).1
  have he : 1 ≤ Real.exp ((j : ℝ) * η) := Real.one_le_exp (mul_nonneg hj0 hη.le)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he hX

lemma bin_partial_error_sum_bound (L η C S V : ℝ) (J : ℕ)
    (hL : 1 ≤ L) (hη : 0 < η) (hηone : η ≤ 1)
    (hC : 0 ≤ C) (hS : 0 ≤ S) (hV : 0 ≤ V)
    (F : ℤ → ℂ)
    (hF : ∀ j ∈ paddingBinIndices L η,
      ‖F j‖ ≤ C * L ^ (-21 / 20 : ℝ) * (2 : ℝ) ^ J * S * V) :
    ∑ j ∈ paddingBinIndices L η, ‖F j‖ ≤
      (101 * C) * η⁻¹ * (2 : ℝ) ^ J * L ^ (-1 / 20 : ℝ) * S * V := by
  have hLp : 0 < L := by linarith
  calc
    _ ≤ ∑ _j ∈ paddingBinIndices L η,
        C * L ^ (-21 / 20 : ℝ) * (2 : ℝ) ^ J * S * V :=
      sum_le_sum hF
    _ = ((paddingBinIndices L η).card : ℝ) *
        (C * L ^ (-21 / 20 : ℝ) * (2 : ℝ) ^ J * S * V) := by
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ (101 * L / η) *
        (C * L ^ (-21 / 20 : ℝ) * (2 : ℝ) ^ J * S * V) :=
      mul_le_mul_of_nonneg_right (paddingBinIndices_card_linear L η hL hη hηone)
        (by positivity)
    _ = _ := by
      have hp : L * L ^ (-21 / 20 : ℝ) = L ^ (-1 / 20 : ℝ) := by
        calc
          _ = L ^ (1 : ℝ) * L ^ (-21 / 20 : ℝ) := by rw [Real.rpow_one]
          _ = L ^ ((1 : ℝ) + (-21 / 20)) := (Real.rpow_add hLp _ _).symm
          _ = _ := by norm_num
      calc
        _ = (101 * C) * η⁻¹ * (2 : ℝ) ^ J *
            (L * L ^ (-21 / 20 : ℝ)) * S * V := by ring
        _ = _ := by rw [hp]

theorem quantitative_canonical_centering_bins (hP : ModFiveThetaInput)
    (hM : PrimeReciprocalInput) (hMRT : MRTLiouvilleShortInput)
    (h : ℕ) (hh : 0 < h) (l : ℕ) [NeZero l] (E : Finset ℕ)
    (hEl : ∀ p, p.Prime → p ∣ l → p ∈ E) (W : ℝ) (hW : 1 ≤ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Q := paddingPrimeSupply E L
      let R := boundedPaddingDivisors Q ⌊100 * Real.log L⌋₊
      ∀ (X : ℝ), Real.exp (L ^ (1000 : ℝ)) ≤ X →
      ∀ (η : ℝ), 0 < η → η < Real.log 2 →
      ∀ (eligible : ℤ → ℕ → ℕ → Prop),
      (∀ j d q, eligible j d q → actualPaddingBin η (Real.log d) j q) →
      ∀ b : ZMod l,
      ∑ j ∈ paddingBinIndices L η,
        ‖tupleNonrawBin P R actualPaddingCoefficient (eligible j) l b h
          (X * Real.exp ((j : ℝ) * η))‖ ≤
        C * η⁻¹ * (2 : ℝ) ^ J * L ^ (-1 / 20 : ℝ) * paddingTiltNormalizer Q *
          ∏ i, primeHarmonicMass (P i) := by
  obtain ⟨C, hC, hb⟩ := quantitative_canonical_nonraw_bin hP hM hMRT h hh l E hEl W hW
  refine ⟨101 * C, mul_pos (by norm_num) hC, ?_⟩
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with L hb hL
  dsimp only
  intro X hX η hη hηlog eligible helig b
  have hXp : 0 < X := (Real.exp_pos _).trans_le hX
  have hlog : Real.log 2 < 1 := by
    linarith [Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)]
  have hηone : η ≤ 1 := hηlog.le.trans hlog.le
  apply bin_partial_error_sum_bound L η C _ _ _ hL hη hηone hC.le
    (paddingTiltNormalizer_pos _).le (prod_nonneg fun i _ => by unfold primeHarmonicMass; positivity)
  intro j hj
  exact hb (X * Real.exp ((j : ℝ) * η))
    (hX.trans (bin_cutoff_ge L η X hη hXp.le j hj)) η hη hηlog j
      (eligible j) (helig j) b

end TwoPointCorrelations

end OAI
