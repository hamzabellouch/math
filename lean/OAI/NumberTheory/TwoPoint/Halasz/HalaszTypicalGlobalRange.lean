import OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalGlobalMean
import OAI.NumberTheory.TwoPoint.Halasz.HalaszShortEndpoint

namespace OAI

/-! Keep the actual outer volume when quotient rounding adds a bounded
number of origins beyond the range of the original distance hypothesis. -/
namespace TwoPointCorrelations

open Finset

lemma halasz_short_truncate_outer (B : ℕ → ℂ) (hB : OneBounded B)
    (X Y H D : ℕ) (hY : Y ≤ X+D) (a b : ℝ) (ha : 0 ≤ a)
    (hmean : ∀ Z : ℕ, Z ≤ Y → Z ≤ X →
      shortExponentialIntegral B Z H 0 ≤ a*(Z:ℝ)+b) :
    shortExponentialIntegral B Y H 0 ≤ a*(Y:ℝ)+b+(D:ℝ)*H := by
  have hz : Y ≤ min Y X+D := by omega
  have hm := hmean (min Y X) (min_le_left _ _) (min_le_right _ _)
  have hv : ((min Y X:ℕ):ℝ) ≤ Y := by exact_mod_cast min_le_left Y X
  calc
    _ ≤ shortExponentialIntegral B (min Y X) H 0+(D:ℝ)*H :=
      halasz_short_outer_endpoint B hB Y (min Y X) D H hz 0
    _ ≤ (a*((min Y X:ℕ):ℝ)+b)+(D:ℝ)*H := add_le_add hm le_rfl
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hv ha]

theorem halasz_typical_global_range
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ X Y H K D : ℕ,
      2 ≤ X → 1 ≤ Real.log (X:ℝ) → Y ≤ 2*X+D → N₀ ≤ K → 1 ≤ K →
      Real.sqrt (X:ℝ) ≤ K → 4 ≤ H → H ≤ K →
      ∀ P Q : ℝ, 2 ≤ P → P ≤ Q → 2 ≤ Real.log P → 1 ≤ Real.log Q →
      8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P →
      2 ≤ mrtBaseResolution P Q (1/100) → 2*Q ≤ K →
      ∀ J : ℕ, 1 ≤ J →
      (∀ n : ℕ, K ≤ n → n ≤ 2*X →
        200*Real.log (Real.log n)+1 ≤ Real.log (mrtBandLower P Q J) ∧
        ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log n))) →
      ∀ W : ℝ, 1 ≤ W → W ≤ K → W^9 ≤ mrtBaseResolution P Q (1/100) →
        W^2 ≤ P → W ≤ H → Q/(H:ℝ) ≤ W^7 →
      ∀ F : ℕ → ℂ, F 1=1 → (∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) → OneBounded F →
      ∀ M : ℝ, 0 ≤ M →
      (∀ u : ℝ, |u| ≤ X → M ≤ squaredDistance F (mrtArchimedeanTwist u) X) →
      shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) Y H 0 ≤
        C*(Y:ℝ)*H*(Real.exp (-2*M/5)+
          Real.sqrt (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))+W⁻¹)+(2*(K:ℝ)+D)*H := by
  obtain ⟨C,hC,N₀,hmean⟩ := halasz_typical_global_mean hprime hhigh
  refine ⟨C,hC,N₀,?_⟩
  intro X Y H K D hX hLX hY hKN hK hKX hH hHK P Q hP hPQ hLP hLQ hbudget hres hQK
    J hJ hbands W hW hWK hWR hWP hWH hWQ F hF1 hFc hFb M hM hd
  let R := Real.exp (-2*M/5)+
    Real.sqrt (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))+W⁻¹
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let B := mrtTypicalCoefficient (Icc 1 J)
    (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F
  have hs := halasz_short_truncate_outer B
    (mrtTypicalCoefficient_oneBounded (Icc 1 J)
      (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F hFb) (2*X) Y H D hY
    (C*H*R) (2*(K:ℝ)*H) (by positivity) ?_
  · dsimp only [R,B] at hs
    convert hs using 1
    ring
  intro Z _ hZX
  have hb : ∀ n : ℕ, K ≤ n → 2*n ≤ Z → ∀ k ∈ ({n,2*n}:Finset ℕ),
      200*Real.log (Real.log k)+1 ≤ Real.log (mrtBandLower P Q J) ∧
      ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log k)) := by
    intro n hn hnZ k hk
    simp only [mem_insert,mem_singleton] at hk
    rcases hk with hk | hk
    · subst k
      exact hbands n hn (by omega)
    · subst k
      exact hbands (2*n) (by omega) (by omega)
  have hm := hmean X Z H K hX hLX hZX hKN hK hKX hH hHK
    P Q hP hPQ hLP hLQ hbudget hres hQK J hJ hb W hW hWK hWR hWP hWH hWQ
    F hF1 hFc hFb M hM hd
  convert hm using 1
  dsimp [R]
  ring

end TwoPointCorrelations

end OAI
