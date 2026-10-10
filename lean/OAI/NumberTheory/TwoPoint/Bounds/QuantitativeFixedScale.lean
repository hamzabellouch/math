import OAI.NumberTheory.TwoPoint.Bounds.FinalCorrelationBound
import OAI.NumberTheory.TwoPoint.Walks.RetainedFinalScale
import OAI.NumberTheory.TwoPoint.Bounds.QuantitativeFinalWindows

namespace OAI

/-! Assembly of the actual graph, deletion and centering estimates.
The interval exponent and prime-band width are absolute: they are chosen
before the shift, modulus, or residue class. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem quantitative_fixed_scale (hP : ModFiveThetaInput)
    (hBr : BravermanDepth22Input) (hM : PrimeReciprocalInput)
    (hMRT : MRTLiouvilleShortInput) :
    ∃ (A : ℕ) (W : ℝ), 1000 ≤ A ∧ 10 ≤ W ∧
      ∀ (h l : ℕ) [NeZero l], 0 < h →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
        ∀ X : ℝ, Real.exp (L ^ A) ≤ X → ∀ b : ℕ,
          ‖progressionLiouvilleMean h l b X‖ ≤
            C * Real.exp (-(primeSupplyCount W L : ℝ)) := by
  obtain ⟨As, W, hAs, hW, hs⟩ :=
    hP.eventually_canonical_retained_weighted_saving hBr
  obtain ⟨Ad, hAd, hd⟩ := hBr.eventually_canonical_shifted_source_deletion_uniform hP
  let A := As + Ad
  have hA : 1000 ≤ A := by dsimp only [A]; omega
  have hWone : 1 ≤ W := by linarith
  refine ⟨A, W, hA, hW, ?_⟩
  intro h l _ hh
  have hl : 0 < l := NeZero.pos l
  let E := (h * l).primeFactors
  have hE : ∀ p, p.Prime → p ∣ h → p ∈ E := by
    intro p hp hph
    exact Nat.mem_primeFactors.mpr
      ⟨hp, dvd_mul_of_dvd_left hph l, (Nat.mul_pos hh hl).ne'⟩
  have hEl : ∀ p, p.Prime → p ∣ l → p ∈ E := by
    intro p hp hpl
    exact Nat.mem_primeFactors.mpr
      ⟨hp, dvd_mul_of_dvd_right hpl h, (Nat.mul_pos hh hl).ne'⟩
  obtain ⟨Cd, hCd, hd⟩ := hd h E hE W 3 hW (by norm_num)
  obtain ⟨Cc, hCc, hc⟩ := quantitative_centering_assembly hP hM hMRT h hh l E hEl W hWone
  let Cs : ℝ := 1212 * Real.exp 1 * (l : ℝ) ^ 2 + 606
  refine ⟨Cs + 4 * Cd + 2 * Cc + 19, by dsimp only [Cs]; positivity, ?_⟩
  filter_upwards [hs h l hh hl E hE hEl, hd, hc,
    hP.eventually_canonical_retained_mass E W hWone,
    eventually_quantitative_final_windows W (by linarith),
    eventually_rare_error_saving W hWone,
    eventually_ge_atTop (101 : ℝ)] with L hs hd hc hm hw hr hlarge
  intro X hX b
  have hL : 1 ≤ L := by linarith
  let J := primeSupplyCount W L
  let η := Real.exp (-(J : ℝ))
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  let Q := paddingPrimeSupply E L
  let S := paddingTiltNormalizer Q
  let V := ∏ i, primeHarmonicMass (P i)
  let M := S * V
  let S₀ := totalPaddingBinMass (primeTupleDivisors P) Q L η
  let bins := paddingBinIndices L η
  let eligible := numericalBinEligible L η
  let T := fun j : ℤ => X * Real.exp ((j : ℝ) * η)
  let N := fun j : ℤ => ⌊T j⌋₊
  let v := fun j : ℤ => (N j : ℂ) / (T j : ℂ)
  let raw := ∑ j ∈ bins, v j * canonicalUncutPrefix h l b E W L (eligible j) (N j)
  let retained := ∑ j ∈ bins,
    v j * canonicalRetainedPrefix h l b E W L (eligible j) hL hWone hE (N j)
  let cost := fun site => canonicalShiftedSourceDeletion h E W L η (Real.exp (4 * J))
    hL hWone hE bins (fun d => Real.log d) eligible site (fun _ => 1) N
  have hη : 0 < η := Real.exp_pos _
  have hηone : η ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg J))
  have hXpos : 0 < X := (Real.exp_pos _).trans_le hX
  have hwindow := hw.2.2.2.2 A hA X hX
  have hN (A' : ℕ) (hA' : A' ≤ A) (j : ℤ) (hj : j ∈ bins) :
      Real.exp (L ^ A' / 2) ≤ (N j : ℝ) :=
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
      (pow_le_pow_right₀ hL hA') (by norm_num))).trans (hwindow.2 j hj)
  have hv : ∀ j ∈ bins, ‖v j‖ ≤ 1 := by
    intro j _
    exact floor_cutoff_weight_norm_le (T j) (mul_pos hXpos (Real.exp_pos _))
  have he : ∀ j ∈ bins, ∀ d q, eligible j d q → PaddingPairEligible L η d q := by
    intro j hj d q hdq
    exact numericalBinEligible_pair L η hη j hj d q hdq
  have hb : ∀ j ∈ bins, ∀ d q, eligible j d q →
      actualPaddingBin η (Real.log d) j q := by
    intro j _ d q hdq
    exact numericalBinEligible_bin L η j d q hdq
  have hbins : (bins.card : ℝ) ≤ Real.exp (3 * Real.log L) :=
    paddingBinIndices_card_polynomial L W hlarge hWone
  have hm' := hm hL η hη
  have hV : 1 ≤ V := (one_le_pow₀ hWone).trans hm'.1
  have hM : 0 < M := mul_pos (paddingTiltNormalizer_pos Q) (by linarith)
  have hmass : M / 2 ≤ S₀ := hm'.2
  have hS₀ : 0 < S₀ := (half_pos hM).trans_le hmass
  have hret : ‖retained‖ / S₀ ≤ Cs * η :=
    hs hL eligible he b N v (hN As (by dsimp only [A]; omega)) hv
  have hdelete : ‖raw - retained‖ ≤ cost (fun _ _ _ => 0) +
      cost (fun _ d q => (h * q * d : ℕ)) :=
    canonical_weighted_correlation_deletion h l b E W L η hL hWone hE bins
      (fun d => Real.log d) eligible N v hb hv
  have hd' (site : ℤ → ℕ → ℕ → ℤ) : cost site / M ≤ (Cd + 4) * η := by
    have hx := hd hL η (Real.exp (4 * J)) hη hηone (Real.exp_pos _) bins
      (fun d => Real.log d) eligible hbins he hb site (fun _ => 1) N
      (hN Ad (by dsimp only [A]; omega))
    exact hx.trans (quantitative_deletion_small L W Cd J hL hWone hCd.le
      (primeSupplyCount_final_budget L W hL hWone) hr)
  have hdel : ‖raw - retained‖ ≤ 2 * M * ((Cd + 4) * η) := by
    have h₁ := (div_le_iff₀ hM).mp (hd' (fun _ _ _ => 0))
    have h₂ := (div_le_iff₀ hM).mp (hd' (fun _ d q => (h * q * d : ℕ)))
    nlinarith
  have hcenter : ‖raw - (S₀ : ℂ) * progressionLiouvilleMean h l b X‖ ≤
      Cc * η * M + S₀ * (2 * η + 1 / X) := by
    have hx := hc hL X hwindow.1 η hη hw.2.2.2.1 b
    change ‖raw - (S₀ : ℂ) * progressionLiouvilleMean h l b X‖ ≤ _ at hx
    have hsmall := (quantitative_small_terms L W J hL hWone
      (primeSupplyCount_final_budget L W hL hWone)).1
    have hinv : η⁻¹ = Real.exp (J : ℝ) := by
      dsimp only [η]
      rw [Real.exp_neg, inv_inv]
    rw [← hinv] at hsmall
    have hcsmall := mul_le_mul_of_nonneg_left hsmall hCc.le
    have hcsmall' := mul_le_mul_of_nonneg_right hcsmall hM.le
    dsimp only [M] at hcsmall'
    nlinarith
  exact correlation_normalized_bound raw retained (progressionLiouvilleMean h l b X)
    S₀ M η Cs Cd Cc (1 / X) hS₀ hM.le hη.le (by dsimp only [Cs]; positivity)
    hCd.le hCc.le hmass (reciprocal_cutoff_saving L W X A hL hWone (by omega) hX)
    hret hdel hcenter

end TwoPointCorrelations

end OAI
