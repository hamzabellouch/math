import OAI.NumberTheory.JointDickman.Amplification.LastBandSamples

namespace OAI

/-! # The actual no-small-band class has sparse separated samples -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Classical Topology

lemma last_selected_bin_count (P Q η : ℝ) (hQ : 1 ≤ Real.log Q) :
    ∀ᶠ X : ℝ in atTop, let J := mellinBandCount Q (Real.sqrt (Real.log X)) hQ
      ((canonicalMellinBands P Q η).bins (J-1)).card ≤
        mrtBaseResolution P Q η*(Real.log X)^2+1 := by
  have hJ := (mellinBandCount_tendsto Q hQ).comp
    (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  filter_upwards [hJ.eventually (eventually_ge_atTop 1),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)] with X hJX hlogX
  let J := mellinBandCount Q (Real.sqrt (Real.log X)) hQ
  have hJ1 : 1 ≤ J := hJX
  have hJid : J-1+1=J := by omega
  let U := mrtBandUpper Q J
  let H := mrtResolution P Q η J
  have hH0 : 0 ≤ H := (mrtResolution_pos P Q η hJ1).le
  have hU1 : 1 ≤ U := by
    dsimp [U,mrtBandUpper]
    apply Real.one_le_exp
    positivity
  have hsmallU : U ≤ Real.exp (Real.sqrt (Real.log X)) := by
    simpa only [hJid] using mellinBandCount_good Q _ hQ (show J-1<J by omega)
  have hlogU : Real.log U ≤ Real.sqrt (Real.log X) := by
    have hh := Real.log_le_log (by linarith : 0<U) hsmallU
    simpa only [Real.log_exp] using hh
  have hJs : (J:ℝ) ≤ Real.sqrt (Real.log X) :=
    (mrt_band_index_le_log_upper Q J hJ1 hQ).trans hlogU
  have hJsq : (J:ℝ)^2 ≤ Real.log X := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg J) hJs 2
    simpa only [Real.sq_sqrt (by linarith : 0≤Real.log X)] using hh
  have hsqrt : Real.sqrt (Real.log X) ≤ Real.log X := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · linarith
    · nlinarith
  have hHle : H ≤ mrtBaseResolution P Q η*Real.log X := by
    dsimp [H,mrtResolution]
    nlinarith [mrtBaseResolution_pos P Q η]
  have hc := mrt_log_bin_card (P := mrtBandLower P Q J) hH0 hU1
  change ((Icc ⌊H*Real.log (mrtBandLower P Q J)⌋₊ ⌊H*Real.log U⌋₊).card:ℝ) ≤
    H*Real.log U+1 at hc
  change (((canonicalMellinBands P Q η).bins (J-1)).card:ℝ) ≤ _
  simp only [canonicalMellinBands,hJid]
  change ((Icc ⌊H*Real.log (mrtBandLower P Q J)⌋₊ ⌊H*Real.log U⌋₊).card:ℝ) ≤ _
  apply hc.trans
  have hb := mul_le_mul hHle (hlogU.trans hsqrt) (Real.log_nonneg hU1)
    (mul_nonneg (mrtBaseResolution_pos P Q η).le (by linarith : 0≤Real.log X))
  nlinarith

theorem canonical_exceptional_samples (P Q : ℝ) (hP : 2*Real.exp 1 ≤ P)
    (hPQ : P ≤ Q) (hlogP : 1 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hH : 2 ≤ mrtBaseResolution P Q (1/12)) :
    ∀ᶠ X : ℝ in atTop, let J := mellinBandCount Q (Real.sqrt (Real.log X)) hQ
      let D := canonicalMellinBands P Q (1/12)
      ∀ f : ℕ → ℂ, OneBounded f → ∀ S : Finset ℝ,
      (∀ t ∈ S, |t| ≤ X) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|) →
      (∀ t ∈ S, t ∈ mrtNoSmallBand D.bins (D.polynomial f) D.threshold J) →
      (S.card:ℝ) ≤ (mrtBaseResolution P Q (1/12)*(Real.log X)^2+1)*X^(5/12:ℝ) := by
  filter_upwards [last_band_bin_samples P Q hP hPQ hlogP hQ hH,
    last_selected_bin_count P Q (1/12) hQ, eventually_ge_atTop (1 : ℝ)] with X hbin hcount hX
  let J := mellinBandCount Q (Real.sqrt (Real.log X)) hQ
  let D := canonicalMellinBands P Q (1/12)
  change 0<J ∧ _ at hbin
  dsimp only
  intro f hf S hS hsep hres
  let E := fun k => S.filter (fun t => D.threshold (J-1) k ≤ ‖D.polynomial f (J-1) k t‖)
  have hcover : S ⊆ (D.bins (J-1)).biUnion E := by
    intro t ht
    obtain ⟨k,hk,hkt⟩ := mrt_no_small_band_large_witness D.bins (D.polynomial f) D.threshold
      (show J-1<J by omega) (hres t ht)
    exact mem_biUnion.mpr ⟨k,hk,mem_filter.mpr ⟨ht,hkt.le⟩⟩
  have hbound (k : ℕ) (hk : k ∈ D.bins (J-1)) : ((E k).card:ℝ) ≤ X^(5/12:ℝ) := by
    apply hbin.2 k hk f hf (E k)
    · intro t ht
      exact hS t (mem_filter.mp ht).1
    · intro x hx y hy hxy
      exact hsep x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 hxy
    · intro t ht
      exact (mem_filter.mp ht).2
  calc
    (S.card:ℝ) ≤ (((D.bins (J-1)).biUnion E).card:ℝ) := by exact_mod_cast card_le_card hcover
    _ ≤ ∑ k ∈ D.bins (J-1), ((E k).card:ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ _k ∈ D.bins (J-1), X^(5/12:ℝ) := sum_le_sum hbound
    _ = ((D.bins (J-1)).card:ℝ)*X^(5/12:ℝ) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg (by linarith) _)

end JointDickman

end OAI
