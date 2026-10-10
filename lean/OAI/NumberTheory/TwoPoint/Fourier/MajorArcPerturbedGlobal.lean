import OAI.NumberTheory.TwoPoint.Fourier.MajorArcGlobalMean
import OAI.NumberTheory.TwoPoint.Fourier.MajorArcGlobalRate
import OAI.NumberTheory.TwoPoint.Fourier.MajorArcPrefixCutoff

namespace OAI

/-! Major-arc perturbation for the literal typical coefficient. Very short
prefixes use boundedness; every longer prefix uses the proved character mean. -/
namespace TwoPointCorrelations

open Finset

theorem major_arc_typical_perturbed_global
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ X V H K H₀ : ℕ,
      2 ≤ X → 1 ≤ Real.log (X:ℝ) → V ≤ 2*X → N₀ ≤ K → 1 ≤ K →
      Real.sqrt (X:ℝ) ≤ K →
      ∀ P Q : ℝ, 2 ≤ P → P ≤ Q → 2 ≤ Real.log P → 1 ≤ Real.log Q →
      8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P →
      2 ≤ mrtBaseResolution P Q (1/100) → 2*Q ≤ K →
      ∀ J : ℕ, 1 ≤ J →
      (∀ n : ℕ, K ≤ n → n ≤ 2*X →
        200*Real.log (Real.log n)+1 ≤ Real.log (mrtBandLower P Q J) ∧
        ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log n))) →
      ∀ W : ℝ, 1 ≤ W → W ≤ K → W^9 ≤ mrtBaseResolution P Q (1/100) → W^2 ≤ P →
      W^5 ≤ (H:ℝ) → (2*(K:ℝ)+1)/(V:ℝ) ≤ (W^4)⁻¹ →
      ∀ q : ℕ, 0 < q → q ≤ V → (q:ℝ) ≤ W → (q:ℝ) ≤ mrtModulusCutoff X H₀ →
      (∀ d ∈ q.divisors, mrtPrimeAvoids ((Icc 1 J).biUnion
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j))) d) →
      (∀ h : ℕ, 1 ≤ h → h ≤ H → (H:ℝ)/W^2 ≤ h →
        ∀ d ∈ q.divisors, 4 ≤ h/d+1 ∧ h/d+1 ≤ K ∧
          W ≤ (h/d+1:ℕ) ∧ Q/(h/d+1:ℕ) ≤ W^7) →
      ∀ F : ℕ → ℂ, F 1=1 → (∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) → OneBounded F →
      ∀ M : ℝ, 0 ≤ M → MRTDistanceLowerBound F X H₀ M → ∀ r : ℤ, ∀ β : ℝ,
      |β| *(H:ℝ) ≤ 2 →
      shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) V H ((r:ℝ)/q+β) ≤
      (1+4*Real.pi)*(V:ℝ)*H*
        (4*C*(Real.sqrt W*(1+Real.log W))*(Real.exp (-2*M/5)+
          Real.sqrt (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))+W⁻¹)+3/W) := by
  obtain ⟨C,hC,N₀,hrational⟩ := major_arc_typical_rational_global hprime hhigh
  refine ⟨C,hC,N₀,?_⟩
  intro X V H K H₀ hX hLX hV hKN hK hKX P Q hP hPQ hLP hLQ hbudget hres hQK
    J hJ hbands W hW hWK hWR hWP hH hboundary q hq hqV hqW hqmax havoid hwindow
    F hF1 hFc hFb M hM hd r β hβ
  let R := Real.exp (-2*M/5)+
    Real.sqrt (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))+W⁻¹
  let ε := 4*C*(Real.sqrt W*(1+Real.log W))*R+3/W
  have hW0 : 0 < W := by linarith
  have hH0 : (0:ℝ) < H := (pow_pos hW0 5).trans_le hH
  have hV0 : (0:ℝ) < V := by exact_mod_cast hq.trans_le hqV
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hlog : 0 ≤ 1+Real.log W := by linarith [Real.log_nonneg hW]
  have hmain : 0 ≤ 4*C*(Real.sqrt W*(1+Real.log W))*R := by positivity
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hsmall : (V:ℝ)*((H:ℝ)/W^2) ≤ (V:ℝ)*H*ε := by
    have hsq : W ≤ W^2 := le_self_pow₀ hW (by decide)
    have hi : (W^2)⁻¹ ≤ W⁻¹ := inv_le_inv₀ (pow_pos hW0 2) hW0 |>.mpr hsq
    have he : W⁻¹ ≤ ε := by dsimp [ε]; rw [div_eq_mul_inv]; nlinarith [inv_pos.mpr hW0]
    have hh := mul_le_mul_of_nonneg_left (hi.trans he) (Nat.cast_nonneg H)
    simpa only [div_eq_mul_inv,mul_assoc] using mul_le_mul_of_nonneg_left hh hV0.le
  have hp := major_arc_perturbation_cutoff_two _
    (mrtTypicalCoefficient_oneBounded (Icc 1 J)
      (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F hFb)
    V H (by exact_mod_cast hH0) ((r:ℝ)/q) β ((H:ℝ)/W^2) ((V:ℝ)*H*ε)
    (by positivity) hsmall hβ ?_
  · convert hp using 1
    dsimp [ε,R]
    ring
  intro h hh hhH hu
  have hp3 : W^3 ≤ (h:ℝ) := by
    apply le_trans _ hu
    apply (le_div_iff₀ (pow_pos hW0 2)).mpr
    simpa only [←pow_add] using hH
  have hqh : q ≤ h := by
    have ht : (q:ℝ) ≤ h := hqW.trans ((le_self_pow₀ hW (by decide : 3≠0)).trans hp3)
    exact_mod_cast ht
  have hr := hrational X V h K H₀ hX hLX hV hKN hK hKX P Q hP hPQ hLP hLQ
    hbudget hres hQK J hJ hbands W hW hWK hWR hWP q hq hqV hqh hqmax havoid
    (hwindow h hh hhH hu) F hF1 hFc hFb M hM hd r
  have hn := major_arc_global_normalized hC.le hR hW hq1 hqW hV0 hboundary hp3 hr
  have hhreal : (h:ℝ) ≤ H := by exact_mod_cast hhH
  calc
    _ ≤ (V:ℝ)*h*ε := hn
    _ ≤ _ := by gcongr

end TwoPointCorrelations

end OAI
