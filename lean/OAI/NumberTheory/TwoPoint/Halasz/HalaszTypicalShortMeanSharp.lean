import OAI.NumberTheory.TwoPoint.Fourier.MajorArcEnergyRoot

namespace OAI

/-! The literal typical L1 short mean with the refined off-center error.
The original pretentious distance cutoff and height are preserved. -/
namespace TwoPointCorrelations

open Finset Filter MeasureTheory

theorem halasz_typical_short_mean_sharp
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ P Q : ℝ, 2 ≤ P → P ≤ Q → 2 ≤ Real.log P → 1 ≤ Real.log Q →
      8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P →
      2 ≤ mrtBaseResolution P Q (1/100) →
      ∀ J : ℕ, 1 ≤ J →
      (∀ k ∈ ({N,2*N}:Finset ℕ),
        200*Real.log (Real.log k)+1 ≤ Real.log (mrtBandLower P Q J) ∧
        ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log k))) →
      ∀ X : ℕ, N ≤ X → X ≤ N^3 → ∀ H : ℕ, 4 ≤ H → H ≤ N → 2*Q ≤ (N:ℝ) →
      ∀ W : ℝ, 1 ≤ W → W^9 ≤ mrtBaseResolution P Q (1/100) →
        W^2 ≤ P → W ≤ (H:ℝ) → Q/(H:ℝ) ≤ W^7 →
      ∀ F : ℕ → ℂ, F 1=1 → (∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) → OneBounded F →
      ∀ M : ℝ, 0 ≤ M →
      (∀ u : ℝ, |u| ≤ X → M ≤ squaredDistance F (mrtArchimedeanTwist u) X) →
      (∫ x in (N:ℝ)..(2*N), ‖shortExponentialSum (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) H 0 x‖)/((N:ℝ)*H) ≤
      K*(Real.exp (-2*M/5)+Real.sqrt
        (Real.log (Real.log N)/(Real.log N)^(1/80:ℝ))+W⁻¹) := by
  obtain ⟨C,hC,henergy⟩ := halasz_typical_short_energy_sharp hprime hhigh
  refine ⟨majorArcEnergyConstant C,major_arc_energy_constant_pos hC.le,?_⟩
  have hl : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [henergy,hl,eventually_ge_atTop 1] with N henergy hl hN
  intro P Q hP hPQ hlP hlQ hbudget hres J hJ hbands X hNX hXN H hH hHN hsize
    W hW hWR hWP hWH hWQ F hF1 hFc hFb M hM hd
  have he := henergy P Q hP hPQ hlP hlQ hbudget hres J hJ hbands
    X hNX hXN H hH hHN hsize F hF1 hFc hFb M hM hd
  have hs := halasz_short_mean_square (mrtTypicalCoefficient (Icc 1 J)
    (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F)
    (show 0 < N by omega) (show 0 < H by omega) 0
  have hmean := Real.le_sqrt_of_sq_le (hs.trans he)
  apply hmean.trans
  exact major_arc_short_energy_root hC.le hW hWR hWP hWH hWQ
    (div_nonneg (Real.log_nonneg hl) (Real.rpow_nonneg (by linarith) _))

end TwoPointCorrelations

end OAI
