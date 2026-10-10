import OAI.NumberTheory.JointDickman.Analysis.MellinEndpointScales
import OAI.NumberTheory.JointDickman.Arithmetic.GrowingPrimeSamples

namespace OAI

/-! # Sparse samples in each bin of the last selected band -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

theorem last_band_bin_samples (P Q : ℝ) (_hP : 2*Real.exp 1 ≤ P)
    (_hPQ : P ≤ Q) (hlogP : 1 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hH : 2 ≤ mrtBaseResolution P Q (1/12)) :
    ∀ᶠ X : ℝ in atTop, let J := mellinBandCount Q (Real.sqrt (Real.log X)) hQ
      let D := canonicalMellinBands P Q (1/12)
      0 < J ∧ ∀ k ∈ D.bins (J-1), ∀ f : ℕ → ℂ, OneBounded f →
        ∀ U : Finset ℝ, (∀ t ∈ U, |t| ≤ X) →
        (∀ x ∈ U, ∀ y ∈ U, x ≠ y → 1 ≤ |x-y|) →
        (∀ t ∈ U, D.threshold (J-1) k ≤ ‖D.polynomial f (J-1) k t‖) →
        (U.card:ℝ) ≤ X^(5/12:ℝ) := by
  filter_upwards [last_selected_band_lower P Q hlogP hQ,mellin_endpoint_scales,
    growing_prime_samples,eventually_ge_atTop 1] with X hlast hscale hsamples hX1
  let J := mellinBandCount Q (Real.sqrt (Real.log X)) hQ
  let D := canonicalMellinBands P Q (1/12)
  change 8 ≤ J ∧ (Real.log X)^(1/4:ℝ) ≤ Real.log (mrtBandLower P Q J) at hlast
  have hJ : 0 < J := by omega
  have hJid : J-1+1=J := by omega
  refine ⟨hJ,?_⟩
  intro k hk f hf U hU hsep hlarge
  change k ∈ D.bins (J-1) at hk
  change ∀ t ∈ U, D.threshold (J-1) k ≤ ‖D.polynomial f (J-1) k t‖ at hlarge
  let H := mrtResolution P Q (1/12) J
  let L := mrtPrimeLogLower H k
  let M := ⌈2*L⌉₊
  have hH2 : 2 ≤ H := by
    simpa only [hJid] using canonical_resolution_ge_two hH (J-1)
  have hH0 : 0 < H := by linarith
  have hk' : k ∈ mrtLogBins H (mrtBandLower P Q J) (mrtBandUpper Q J) := by
    change k ∈ mrtLogBins (mrtResolution P Q (1/12) (J-1+1))
      (mrtBandLower P Q (J-1+1)) (mrtBandUpper Q (J-1+1)) at hk
    simpa only [hJid] using hk
  have hp0 : 0 < mrtBandLower P Q J := Real.exp_pos _
  have hu1 : 1 ≤ mrtBandUpper Q J := by
    unfold mrtBandUpper
    apply Real.one_le_exp
    positivity
  have hends := mrt_log_bin_endpoints (show 1≤H by linarith) hp0 hu1 hk'
  change Real.exp (-1)*mrtBandLower P Q J ≤ L ∧ L ≤ mrtBandUpper Q J at hends
  have hLl : Real.exp ((Real.log X)^(1/4:ℝ)-1) ≤ L := by
    apply le_trans (b := Real.exp (Real.log (mrtBandLower P Q J)-1))
    · exact Real.exp_le_exp.mpr (by linarith [hlast.2])
    · have he : Real.exp (Real.log (mrtBandLower P Q J)-1) =
          Real.exp (-1)*mrtBandLower P Q J := by
        rw [sub_eq_add_neg,Real.exp_add,Real.exp_log hp0,mul_comm]
      rw [he]
      exact hends.1
  have hLu : L ≤ Real.exp (Real.sqrt (Real.log X)) := hends.2.trans
    (by simpa only [hJid] using mellinBandCount_good Q _ hQ (show J-1<J by omega))
  obtain ⟨hM2,hlogM,hMlarge,hMsmall⟩ := hscale L hLl hLu
  have hMlo : 2*L ≤ (M:ℝ) := Nat.le_ceil _
  have hL1 : 1 ≤ L := mrt_prime_log_lower_one hH0 k
  have hMhi : (M:ℝ) ≤ 3*L := by
    have hh := Nat.ceil_lt_add_one (show 0≤2*L by positivity)
    dsimp [M]
    linarith
  have hV : (M:ℝ)^(-1/6:ℝ) ≤ D.threshold (J-1) k := by
    have hM0 : 0 < (M:ℝ) := by exact_mod_cast (show 0<M by omega)
    have hl0 : 0 ≤ Real.log L := Real.log_nonneg hL1
    have hlM : Real.log L ≤ Real.log (M:ℝ) := Real.log_le_log (by linarith) (by linarith)
    have he := (mrtFrequencyExponent_bounds (by norm_num : (0:ℝ)≤1/12) (J-1)).2
    dsimp only [D,canonicalMellinBands]
    rw [hJid]
    change (M:ℝ)^(-1/6:ℝ) ≤ Real.exp (-mrtFrequencyExponent (1/12) (J-1)*Real.log L)
    rw [Real.rpow_def_of_pos hM0]
    apply Real.exp_le_exp.mpr
    nlinarith
  apply hsamples M hM2 hlogM hMlarge hMsmall
    ((D.primes (J-1)).filter (fun p => D.bin (J-1) p=k)) _ f hf
    (D.threshold (J-1) k) (Real.exp_pos _) hV U hU hsep hlarge
  intro p hp
  obtain ⟨hp,hpk⟩ := mem_filter.mp hp
  have hpprime : p.Prime := mrtPrimeBand_prime hp
  have hb := mrt_log_bin_prime_support hH2 hpprime.one_le
  have hpk' : mrtPrimeLogBin H p=k := by simpa only [D,canonicalMellinBands,hJid,H] using hpk
  rw [hpk'] at hb
  change L ≤ (p:ℝ) ∧ (p:ℝ) ≤ 2*L at hb
  refine ⟨hpprime,by linarith,?_⟩
  exact_mod_cast hb.2.trans hMlo

end JointDickman

end OAI
