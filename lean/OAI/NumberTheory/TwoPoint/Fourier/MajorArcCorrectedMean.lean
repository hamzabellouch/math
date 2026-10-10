import OAI.NumberTheory.TwoPoint.Fourier.MajorArcPerturbedGlobal
import OAI.NumberTheory.TwoPoint.Fourier.MajorArcBandAvoidance
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCorrectionParameters
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCorrectionArcScale

namespace OAI

/-! Apply the character estimate to the completely multiplicative part
inside each small correction divisor. The original coefficient and original
pretentious distance return in the conclusion. -/
namespace TwoPointCorrelations

open Finset

theorem major_arc_corrected_typical_mean
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ X V H K H₀ : ℕ,
      2 ≤ X → 1 ≤ Real.log (X:ℝ) → H ≤ V → N₀ ≤ K → 1 ≤ K →
      Real.sqrt (X:ℝ) ≤ K →
      ∀ P Q : ℝ, 2 ≤ P → P ≤ Q → 2 ≤ Real.log P → 1 ≤ Real.log Q →
      8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P →
      2 ≤ mrtBaseResolution P Q (1/100) → 2*Q ≤ K →
      ∀ J : ℕ, 1 ≤ J →
      (∀ n : ℕ, K ≤ n → n ≤ 2*X →
        200*Real.log (Real.log n)+1 ≤ Real.log (mrtBandLower P Q J) ∧
        ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log n))) →
      ∀ W : ℝ, 2 ≤ W → W ≤ K → W^9 ≤ mrtBaseResolution P Q (1/100) → W^5 ≤ P →
      W^250 ≤ (H:ℝ) →
      (∀ d : ℕ, 0 < d → d ≤ mrtCorrectionCutoff W →
        V/d+1 ≤ 2*X ∧ (2*(K:ℝ)+1)/(V/d+1:ℕ) ≤ (W^4)⁻¹) →
      ∀ q : ℕ, 0 < q → (q:ℝ) ≤ W → (q:ℝ) ≤ mrtModulusCutoff X H₀ →
      (∀ d : ℕ, 0 < d → d ≤ mrtCorrectionCutoff W → q ≤ V/d+1 ∧
        ∀ k : ℕ, 1 ≤ k → k ≤ H/d+1 → ((H/d+1:ℕ):ℝ)/W^2 ≤ k →
          ∀ b ∈ q.divisors, 4 ≤ k/b+1 ∧ k/b+1 ≤ K ∧
            W ≤ (k/b+1:ℕ) ∧ Q/(k/b+1:ℕ) ≤ W^7) →
      ∀ F : ℕ → ℂ, F 1=1 → Multiplicative F → OneBounded F →
      ∀ M : ℝ, 0 ≤ M → MRTDistanceLowerBound F X H₀ M → ∀ r : ℤ, ∀ β : ℝ,
      |β| *(H:ℝ) ≤ 1 →
      shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) V H ((r:ℝ)/q+β) ≤
      mrtCorrectionBound*(V:ℝ)*H*
        (4*(1+4*Real.pi)*(4*C*(Real.sqrt W*(1+Real.log W))*(Real.exp (-2*M/5)+
          Real.sqrt (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))+W⁻¹)+3/W)+
          5*W^(-5/4:ℝ)) := by
  obtain ⟨C,hC,N₀,hmajor⟩ := major_arc_typical_perturbed_global hprime hhigh
  refine ⟨C,hC,N₀,?_⟩
  intro X V H K H₀ hX hLX hHV hKN hK hKX P Q hP hPQ hLP hLQ hbudget hres hQK
    J hJ hbands W hW hWK hWR hWP hH houter q hq hqW hqmax hwindow
    F hF1 hFm hFb M hM hd r β hβ
  have hCB : 0 < mrtCorrectionBound := Real.exp_pos _
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 < W := by linarith
  obtain ⟨hD,hDH,hDover,hDtail⟩ := mrt_correction_cutoff_scale hW hH
  have hWP2 : W^2 ≤ P := (pow_le_pow_right₀ hW1 (by norm_num : (2:ℕ)≤5)).trans hWP
  let R := Real.exp (-2*M/5)+Real.sqrt
    (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))+W⁻¹
  let ε := (1+4*Real.pi)*(4*C*(Real.sqrt W*(1+Real.log W))*R+3/W)
  have hlog : 0 ≤ 1+Real.log W := by linarith [Real.log_nonneg hW1]
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hp : ∀ j ∈ Icc 1 J, ∀ p ∈ mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j),
      mrtCorrectionCutoff W < p := by
    intro j hj p hp
    have hlow := major_arc_actual_prime_lower hP hPQ (by linarith) hj hp
    exact_mod_cast (mrt_correction_cutoff_bounds hW).2.2.trans_lt (hWP.trans_lt hlow)
  have hav : ∀ b ∈ q.divisors, mrtPrimeAvoids ((Icc 1 J).biUnion
      (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j))) b := by
    intro b hb
    have hb0 : 0 < b := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hb).1 hq
    have hbq : b ≤ q := Nat.le_of_dvd hq (Nat.mem_divisors.mp hb).1
    apply major_arc_actual_bands_avoid hP hPQ (by linarith) hb0
    exact (show (b:ℝ) ≤ q by exact_mod_cast hbq).trans (hqW.trans
      ((le_self_pow₀ hW1 (by decide : (5:ℕ)≠0)).trans hWP))
  have hm := mrt_correction_typical_quotient_mean (Icc 1 J)
    (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j))
    (fun _ _ _ hp => mrtPrimeBand_prime hp) F hFm hFb hF1 V H (mrtCorrectionCutoff W)
    hD hDH hHV hp ((r:ℝ)/q+β) ε hε ?_
  · have ht : (mrtCorrectionCutoff W:ℝ)/H+
        2*(mrtCorrectionCutoff W:ℝ)^(-(1/4:ℝ)) ≤ 5*W^(-5/4:ℝ) := by linarith
    calc
      _ ≤ mrtCorrectionBound*(V:ℝ)*H*(4*ε+
          (mrtCorrectionCutoff W:ℝ)/H+2*(mrtCorrectionCutoff W:ℝ)^(-(1/4:ℝ))) := hm
      _ ≤ mrtCorrectionBound*(V:ℝ)*H*(4*ε+5*W^(-5/4:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith only [ht]
      _ = _ := by dsimp [ε,R]; ring
  intro d hdD
  obtain ⟨hdI,hdD⟩ := mem_filter.mp hdD
  have hd0 : 0 < d := (mem_Icc.mp hdI).1
  have hdW : (d:ℝ) ≤ W^5 :=
    (show (d:ℝ) ≤ mrtCorrectionCutoff W by exact_mod_cast hdD).trans
      (mrt_correction_cutoff_bounds hW).2.2
  have hdH : d ≤ H := hdD.trans hDH
  have hHp : W^5 ≤ ((H/d+1:ℕ):ℝ) := by
    have hb := mrt_correction_quotient_power hW1 hH hd0 hdW
      (show (H:ℝ)/W^2 ≤ H from div_le_self (Nat.cast_nonneg H) (one_le_pow₀ hW1))
    exact (pow_le_pow_right₀ hW1 (by norm_num : (5:ℕ)≤243)).trans hb
  have hβd : |(d:ℝ)*β| *((H/d+1:ℕ):ℝ) ≤ 2 := by
    have hlen := mrt_quotient_length_le_two hd0 hdH
    have hdr : (0:ℝ) < d := by exact_mod_cast hd0
    rw [abs_mul,abs_of_pos hdr]
    calc
      _ = |β| *((d:ℝ)*(H/d+1:ℕ)) := by ring
      _ ≤ |β| *(2*(H:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg β)
        calc
          (d:ℝ)*(H/d+1:ℕ) ≤ (d:ℝ)*(2*((H:ℝ)/d)) :=
            mul_le_mul_of_nonneg_left hlen hdr.le
          _ = _ := by field_simp
      _ ≤ _ := by nlinarith
  have hFcomp1 : mrtCompletePart F 1=1 := fromPrimePowers_one _
  have hi := hmajor X (V/d+1) (H/d+1) K H₀ hX hLX (houter d hd0 hdD).1
    hKN hK hKX P Q hP hPQ hLP hLQ hbudget hres hQK J hJ hbands W hW1 hWK hWR hWP2
    hHp (houter d hd0 hdD).2 q hq (hwindow d hd0 hdD).1 hqW hqmax hav
    (hwindow d hd0 hdD).2 (mrtCompletePart F) hFcomp1
    (fun a b ha hb => mrtCompletePart_mul F ha hb) (mrtCompletePart_oneBounded F hFb)
    M hM (major_arc_complete_distance hd) (d*(r:ℤ)) ((d:ℝ)*β) hβd
  have hphase : (d:ℝ)*((r:ℝ)/q+β) = ((d*(r:ℤ):ℤ):ℝ)/q+(d:ℝ)*β := by
    push_cast
    ring
  rw [hphase]
  simpa only [ε,R,mul_assoc,mul_left_comm,mul_comm] using hi

end TwoPointCorrelations

end OAI
