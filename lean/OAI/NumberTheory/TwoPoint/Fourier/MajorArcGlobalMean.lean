import OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalGlobalRange
import OAI.NumberTheory.TwoPoint.Fourier.MajorArcPerturbedSharp
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCorrectionQuotient

namespace OAI

/-! Global typical means for each character in the exact gcd decomposition.
The quotient volume is retained before the divisor sum is taken. -/
namespace TwoPointCorrelations

open Finset

lemma major_arc_character_volume {C R I : ℝ} {V H K q d : ℕ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hd : 0 < d) (hdq : d ≤ q)
    (hdV : d ≤ V) (hdH : d ≤ H)
    (hmean : I ≤ C*(V/d+1:ℕ)*(H/d+1:ℕ)*R+
      (2*(K:ℝ)+1)*(H/d+1:ℕ)) :
    (d:ℝ)*I ≤ (4*C*V*H*R+2*(q:ℝ)*(2*(K:ℝ)+1)*H)/(d:ℝ) := by
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  have hx := mrt_quotient_length_le_two hd hdV
  have hh := mrt_quotient_length_le_two hd hdH
  have hmain : C*(V/d+1:ℕ)*(H/d+1:ℕ)*R ≤
      C*(2*((V:ℝ)/d))*(2*((H:ℝ)/d))*R := by gcongr
  have herr : (2*(K:ℝ)+1)*(H/d+1:ℕ) ≤
      (2*(K:ℝ)+1)*(2*((H:ℝ)/d)) := by gcongr
  have hq : (d:ℝ) ≤ q := by exact_mod_cast hdq
  calc
    _ ≤ (d:ℝ)*(C*(2*((V:ℝ)/d))*(2*((H:ℝ)/d))*R+
        (2*(K:ℝ)+1)*(2*((H:ℝ)/d))) :=
      mul_le_mul_of_nonneg_left (hmean.trans (add_le_add hmain herr)) hdr.le
    _ = (4*C*V*H*R+2*(d:ℝ)*(2*(K:ℝ)+1)*H)/(d:ℝ) := by field_simp; ring
    _ ≤ _ := by gcongr

theorem major_arc_typical_rational_global
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
      ∀ q : ℕ, 0 < q → q ≤ V → q ≤ H → (q:ℝ) ≤ mrtModulusCutoff X H₀ →
      (∀ d ∈ q.divisors, mrtPrimeAvoids ((Icc 1 J).biUnion
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j))) d) →
      (∀ d ∈ q.divisors, 4 ≤ H/d+1 ∧ H/d+1 ≤ K ∧
        W ≤ (H/d+1:ℕ) ∧ Q/(H/d+1:ℕ) ≤ W^7) →
      ∀ F : ℕ → ℂ, F 1=1 → (∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) → OneBounded F →
      ∀ M : ℝ, 0 ≤ M → MRTDistanceLowerBound F X H₀ M → ∀ r : ℤ,
      shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) V H ((r:ℝ)/q) ≤
      Real.sqrt (q:ℝ)*((1+Real.log q)*
        (4*C*V*H*(Real.exp (-2*M/5)+
          Real.sqrt (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))+W⁻¹)+
          2*(q:ℝ)*(2*(K:ℝ)+1)*H)+(q:ℝ)*V) := by
  obtain ⟨C,hC,N₀,hglobal⟩ := halasz_typical_global_range hprime hhigh
  refine ⟨C,hC,N₀,?_⟩
  intro X V H K H₀ hX hLX hV hKN hK hKX P Q hP hPQ hLP hLQ hbudget hres hQK
    J hJ hbands W hW hWK hWR hWP q hq hqV hqH hqmax havoid hwindow F hF1 hFc hFb M hM hd r
  let R := Real.exp (-2*M/5)+
    Real.sqrt (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))+W⁻¹
  have hR : 0 ≤ R := by dsimp [R]; positivity
  apply major_arc_typical_rational_sharp _ _
    (fun j _ p hp => mrtPrimeBand_prime hp) F hFc hFb q hq r V H
    (4*C*V*H*R+2*(q:ℝ)*(2*(K:ℝ)+1)*H) (by positivity) havoid
  intro d χ
  have hd0 : 0 < d.val := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp d.property).1 hq
  have hdq : d.val ≤ q := Nat.le_of_dvd hq (Nat.mem_divisors.mp d.property).1
  have hwin := hwindow d.val d.property
  have hY : V/d.val+1 ≤ 2*X+1 := (Nat.add_le_add_right (Nat.div_le_self V d.val) 1).trans
    (Nat.add_le_add_right hV 1)
  have hχ1 : twistByCharacter F χ 1=1 := by simp [twistByCharacter,hF1]
  have hm := hglobal X (V/d.val+1) (H/d.val+1) K 1 hX hLX hY hKN hK hKX
    hwin.1 hwin.2.1 P Q hP hPQ hLP hLQ hbudget hres hQK J hJ hbands
    W hW hWK hWR hWP hwin.2.2.1 hwin.2.2.2
    (twistByCharacter F χ) hχ1 (major_arc_twist_complete F hFc χ) (hFb.twistByCharacter χ) M hM
    (fun t ht => major_arc_divisor_distance hd q hq hqmax d χ t ht)
  apply major_arc_character_volume hC.le hR hd0 hdq (hdq.trans hqV) (hdq.trans hqH)
  simpa only [R,Nat.cast_one] using hm

end TwoPointCorrelations

end OAI
