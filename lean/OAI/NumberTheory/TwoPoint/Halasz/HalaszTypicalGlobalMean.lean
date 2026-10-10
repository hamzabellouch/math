import OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalShortMeanSharp
import OAI.NumberTheory.TwoPoint.Halasz.HalaszTypicalGlobal
import OAI.NumberTheory.TwoPoint.Halasz.HalaszDyadicScale

namespace OAI

/-! The same literal typical coefficient is retained while summing all
large dyadic origins. The initial interval remains an explicit error. -/
namespace TwoPointCorrelations

open Finset Filter MeasureTheory
open scoped Classical

theorem halasz_typical_global_mean
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ X Y H K : ℕ,
      2 ≤ X → 1 ≤ Real.log (X:ℝ) → Y ≤ 2*X → N₀ ≤ K → 1 ≤ K →
      Real.sqrt (X:ℝ) ≤ K → 4 ≤ H → H ≤ K →
      ∀ P Q : ℝ, 2 ≤ P → P ≤ Q → 2 ≤ Real.log P → 1 ≤ Real.log Q →
      8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P →
      2 ≤ mrtBaseResolution P Q (1/100) → 2*Q ≤ K →
      ∀ J : ℕ, 1 ≤ J →
      (∀ n : ℕ, K ≤ n → 2*n ≤ Y → ∀ k ∈ ({n,2*n}:Finset ℕ),
        200*Real.log (Real.log k)+1 ≤ Real.log (mrtBandLower P Q J) ∧
        ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log k))) →
      ∀ W : ℝ, 1 ≤ W → W ≤ K → W^9 ≤ mrtBaseResolution P Q (1/100) →
        W^2 ≤ P → W ≤ H → Q/(H:ℝ) ≤ W^7 →
      ∀ F : ℕ → ℂ, F 1=1 → (∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) → OneBounded F →
      ∀ M : ℝ, 0 ≤ M →
      (∀ u : ℝ, |u| ≤ X → M ≤ squaredDistance F (mrtArchimedeanTwist u) X) →
      shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) Y H 0 ≤
        C*(Y:ℝ)*H*(Real.exp (-2*M/5)+
          Real.sqrt (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))+W⁻¹)+2*(K:ℝ)*H := by
  obtain ⟨C,hC,hmean⟩ := halasz_typical_short_mean_sharp hprime hhigh
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hmean
  refine ⟨4*(C+1),by positivity,N₀,?_⟩
  intro X Y H K hX hLX hYX hKN hK hKX hH hHK P Q hP hPQ hLP hLQ hbudget hres hQK
    J hJ hbands W hW hWK hWR hWP hWH hWQ F hF1 hFc hFb M hM hd
  let B := mrtTypicalCoefficient (Icc 1 J)
    (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F
  let R := Real.exp (-2*M/5)+Real.sqrt
    (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))+W⁻¹
  let ε := 2*(C+1)*R
  have hW0 : 0 < W := by linarith
  have hRinv : W⁻¹ ≤ R := by
    dsimp only [R]
    linarith [Real.exp_pos (-2*M/5),Real.sqrt_nonneg
      (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))]
  have hR : 0 ≤ R := (inv_pos.mpr hW0).le.trans hRinv
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hRe : R ≤ ε := by dsimp only [ε]; nlinarith
  have hbudget' : 1 ≤ ε*K := by
    have hh : 1 ≤ W⁻¹*(K:ℝ) := by
      have hh : 1 ≤ (K:ℝ)/W := (le_div_iff₀ hW0).mpr (by simpa using hWK)
      simpa only [div_eq_mul_inv,mul_comm] using hh
    exact hh.trans (mul_le_mul_of_nonneg_right (hRinv.trans hRe) (Nat.cast_nonneg K))
  rw [shortExponentialIntegral_eq_sum]
  have hpref := mrt_dyadic_prefix_bound (fun n => ‖shortExponentialSum B H 0 n‖)
    Y K H ε hK (Nat.cast_nonneg H) hε hbudget' (fun _ => norm_nonneg _)
    (fun n => minor_arc_short_sum_trivial B (mrtTypicalCoefficient_oneBounded _ _ F hFb) H n 0) ?_
  · convert hpref using 1
    dsimp [ε,R]
    ring
  intro n hn hny
  have hn0 : 0 < n := by omega
  have hnX : n ≤ X := by omega
  have hnxr : Real.sqrt (X:ℝ) ≤ n := hKX.trans (by exact_mod_cast hn)
  obtain ⟨hXN,hlogn⟩ := halasz_dyadic_original_scale hX hnxr
  have hm := hN₀ n (hKN.trans hn) P Q hP hPQ hLP hLQ hbudget hres J hJ
    (hbands n hn hny) X hnX hXN H hH (hHK.trans hn)
    (hQK.trans (by exact_mod_cast hn)) W hW hWR hWP hWH hWQ F hF1 hFc hFb M hM hd
  have hupper : Real.log (n:ℝ) ≤ Real.log (X:ℝ) :=
    Real.log_le_log (by exact_mod_cast hn0) (by exact_mod_cast hnX)
  have herr := halasz_sharp_root_error_comparison hLX hlogn hupper
  have hcmp : C*(Real.exp (-2*M/5)+Real.sqrt
      (Real.log (Real.log n)/(Real.log n)^(1/80:ℝ))+W⁻¹) ≤ ε := by
    have hr : Real.exp (-2*M/5)+Real.sqrt
        (Real.log (Real.log n)/(Real.log n)^(1/80:ℝ))+W⁻¹ ≤ 2*R := by
      dsimp only [R]
      linarith [Real.exp_pos (-2*M/5),inv_pos.mpr hW0]
    exact (mul_le_mul_of_nonneg_left hr hC.le).trans (by dsimp [ε]; nlinarith)
  rw [halasz_short_dyadic_cells]
  have hs := hm.trans hcmp
  have hnr : (0:ℝ) < n := by exact_mod_cast hn0
  have hhr : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  simpa only [B,mul_assoc] using (div_le_iff₀ (mul_pos hnr hhr)).mp hs

end TwoPointCorrelations

end OAI
