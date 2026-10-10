import OAI.NumberTheory.TwoPoint.Halasz.HalaszHighPrimeInput
import OAI.NumberTheory.TwoPoint.Halasz.HalaszCofactorBandCount

namespace OAI

/-! The actual-band cofactor estimate on the entire off-center region,
conditional only on the precisely cited high-frequency prime estimate. -/
namespace TwoPointCorrelations

open Filter Finset

theorem HalaszHighPrimeInput.actual_cofactor (hhigh : HalaszHighPrimeInput) :
    ∃ X₀ : ℝ, ∀ᶠ n : ℕ in atTop,
      ∀ (N : ℕ) (a : ℝ), 1 ≤ a → X₀ ≤ (⌊(N:ℝ)/a⌋₊:ℝ) →
      n = ⌊(2*N:ℝ)/a⌋₊ → ∀ X : ℕ, n ≤ X → X ≤ n^3 →
      ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ (P Q : ℝ) (J : ℕ), 1 ≤ Real.log Q →
      mrtBandUpper Q J ≤ Real.exp (Real.sqrt (Real.log X)) →
      ∀ A : Finset ℕ, (∀ p ∈ A, p.Prime) → ∀ t τ : ℝ,
      |τ| ≤ X →
      (∀ v : ℝ, |v| ≤ X → squaredDistance F (mrtArchimedeanTwist τ) X ≤
        squaredDistance F (mrtArchimedeanTwist v) X) →
      |t|+(Real.log n)^8 ≤ X → (Real.log n)^(1/16:ℝ)/2 ≤ |t-τ| →
      ‖mrtCofactorPolynomial A (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) N a t‖ ≤
        (Real.log n)^(-1/40:ℝ) := by
  obtain ⟨C,K,X₀,hC,hK,hcofactor⟩ := halasz_exceptional_typical_window
  refine ⟨X₀,?_⟩
  have hlog : Tendsto (fun n:ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hhigh.distance_cutoff K,halasz_cofactor_band_count,
    hlog.eventually (halasz_exceptional_decay C hC.le),
    hlog.eventually (eventually_ge_atTop (1:ℝ))] with n hcut hcount hdec hln
  intro N a ha hbase hn X hnX hX F hF1 hFm hFb P Q J hQ hband A hA t τ hτ hmin ht haway
  have hM : 0 ≤ (3/100:ℝ)*Real.log (Real.log n) :=
    mul_nonneg (by norm_num) (Real.log_nonneg hln)
  have hd : ∀ v:ℝ, |v-t| ≤ (Real.log n)^8 → 1/2 ≤ |v-τ| →
      2*((3/100:ℝ)*Real.log (Real.log n))+K ≤
        squaredDistance F (mrtArchimedeanTwist v) n := by
    intro v hv hunit
    have hvX : |v| ≤ X := by
      have hh := abs_add_le (v-t) t
      rw [sub_add_cancel] at hh
      linarith
    exact hcut X hnX hX F hFb v τ hvX hτ hunit (hmin v hvX)
  have hb := hcofactor N a ha hbase F hF1 hFm hFb ℕ (Icc 1 J)
    (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) A
    (fun _ _ _ hp => mrtPrimeBand_prime hp) hA t τ
    ((3/100:ℝ)*Real.log (Real.log n)) hM (by simpa only [← hn] using hd)
  have hsave := hdec ((2:ℝ)^(Icc 1 J).card) (τ-t) (by positivity)
    (hcount X hnX hX Q J hQ hband) (by simpa only [abs_sub_comm] using haway)
  apply hb.trans
  simpa only [← hn,mul_comm C] using hsave

end TwoPointCorrelations

end OAI
