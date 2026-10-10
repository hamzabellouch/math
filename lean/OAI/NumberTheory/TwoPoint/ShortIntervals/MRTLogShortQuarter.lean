import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLogKernelQuarter
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTFiniteWindows

namespace OAI

/-! The literal short sum from quarter-height spectral information for both
dyadic polynomials. The omitted frequencies use only generic mean square. -/

namespace TwoPointCorrelations

open Finset MeasureTheory Set
open scoped Classical

theorem mrt_log_short_energy_quarter (V : ℕ → Finset ℕ) (J : ℕ)
    (hprime : ∀ j ∈ Finset.Icc 1 J, ∀ p ∈ V j, p.Prime)
    (hdis : Set.PairwiseDisjoint (Finset.Icc 1 J : Set ℕ) V)
    {P Q η : ℝ} (hP0 : 0 < P) (hQ0 : 0 < Q)
    (hP : 2 ≤ Real.log P) (hQ : 1 ≤ Real.log Q)
    (hPQ : Real.log P ≤ Real.log Q) (hη : 0 < η) (hη' : η ≤ 1/12)
    (hbudget : 8192*(Real.log (Real.log Q)+1) ≤ η*Real.log P)
    (hres : 2 ≤ mrtBaseResolution P Q η)
    (hrange : ∀ j ∈ Finset.Icc 1 J, ∀ p ∈ V j,
      mrtBandLower P Q j ≤ (p:ℝ) ∧ (p:ℝ) ≤ mrtBandUpper Q j)
    {N H : ℕ} (hH4 : 4 ≤ H) (hHN : H ≤ N) (hsize : 2*Q ≤ (N:ℝ))
    (F : ℕ → ℂ) (hF : Multiplicative F) (hFb : OneBounded F)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hnone : ∀ k ∈ ({N, 2*N} : Finset ℕ), ∀ v : ℝ, (N:ℝ)/H ≤ v → v ≤ (k:ℝ)/4 →
      (∫ t in Ioc (-v) v ∩ mrtNoSmallBand (mrtLogFamilyBins P Q η)
        (mrtLogFamilyPolynomial V F P Q η) (mrtLogFamilyThreshold P Q η) J,
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) k t‖^2) ≤
          δ*(v/k+1)) :
    (∫ x in (N:ℝ)..(2*N),
      ‖shortExponentialSum (mrtTypicalCoefficient (Finset.Icc 1 J) V F) H 0 x‖^2) /
        ((N:ℝ)*(H:ℝ)^2) ≤
      (139968/(2*Real.pi)) *
        (12*(δ + 33792*Real.exp 1*(mrtBaseResolution P Q η)⁻¹ + 2*P⁻¹ +
          1024*Real.exp 2*(mrtBaseResolution P Q η)⁻¹*(1+Q/H)) +
          2048*Real.exp 1/(H:ℝ)^2) := by
  have hH : 0 < H := by omega
  have hN : 0 < N := hH.trans_le hHN
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hHr : (0:ℝ) < H := by exact_mod_cast hH
  have hH1 : (4:ℝ) ≤ H := by exact_mod_cast hH4
  have hTN : (N:ℝ)/H ≤ (N:ℝ)/4 := (div_le_iff₀ hHr).mpr (by nlinarith)
  let ε := δ + 33792*Real.exp 1*(mrtBaseResolution P Q η)⁻¹ + 2*P⁻¹ +
    1024*Real.exp 2*(mrtBaseResolution P Q η)⁻¹*(1+Q/H)
  have hk (k : ℕ) (hkm : k ∈ ({N, 2*N} : Finset ℕ)) :
      (∫ t : ℝ, mrtShortKernel ((N:ℝ)/H) t *
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Finset.Icc 1 J) V F) k t‖^2) ≤
        6*ε+1024*Real.exp 1/(H:ℝ)^2 := by
    have hNk : N ≤ k := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hkm
      omega
    have hNkr : (N:ℝ) ≤ k := by exact_mod_cast hNk
    have hkp : 0 < k := hN.trans_le hNk
    have hb := mrt_log_kernel_quarter_bound V J hprime hdis hP0 hQ0 hP hQ hPQ hη hη'
      hbudget hres hrange hkp (hsize.trans hNkr) F hF hFb (div_pos hNr hHr)
      (hTN.trans (by linarith : (N:ℝ)/4 ≤ (k:ℝ)/4)) hδ (hnone k hkm)
    have hq : ((N:ℝ)/H)*Q/k ≤ Q/H := by
      calc
        _ ≤ ((N:ℝ)/H)*Q/N :=
          div_le_div_of_nonneg_left (by positivity) hNr hNkr
        _ = _ := by field_simp
    have hratio : (((N:ℝ)/H)/k)^2 ≤ 1/(H:ℝ)^2 := by
      have hd : ((N:ℝ)/H)/k ≤ ((N:ℝ)/H)/N :=
        div_le_div_of_nonneg_left (by positivity) hNr hNkr
      have he : (((N:ℝ)/H)/N)^2 = 1/(H:ℝ)^2 := by field_simp
      exact (pow_le_pow_left₀ (by positivity) hd 2).trans_eq he
    have hc : 0 ≤ 1024*Real.exp 2*(mrtBaseResolution P Q η)⁻¹ := by positivity
    have he := mul_le_mul_of_nonneg_left hq hc
    have ht := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 1024*Real.exp 1 by positivity)
    have hterm :
        1024*Real.exp 2*(mrtBaseResolution P Q η)⁻¹*(1+(N:ℝ)/H*Q/k) ≤
        1024*Real.exp 2*(mrtBaseResolution P Q η)⁻¹*(1+Q/H) := by
      nlinarith only [he]
    apply hb.trans
    calc
      _ ≤ 6*(δ + 33792*Real.exp 1*(mrtBaseResolution P Q η)⁻¹ + 2*P⁻¹ +
          1024*Real.exp 2*(mrtBaseResolution P Q η)⁻¹*(1+Q/H)) +
          1024*Real.exp 1*(1/(H:ℝ)^2) :=
        add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl hterm) (by norm_num)) ht
      _ = _ := by dsimp [ε]; ring
  have hs := add_le_add (hk N (by simp)) (hk (2*N) (by simp))
  have hb := mrt_literal_short_energy_dyadic
    (mrtTypicalCoefficient (Finset.Icc 1 J) V F) hH hHN
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  change _ ≤ 12*ε+2048*Real.exp 1/(H:ℝ)^2
  calc
    _ ≤ 6*ε+1024*Real.exp 1/(H:ℝ)^2 + (6*ε+1024*Real.exp 1/(H:ℝ)^2) := hs
    _ = _ := by ring

end TwoPointCorrelations

end OAI
