import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralHarmonicCutoff
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Tests separated from the pressure core are dense in its constrained harmonic domain. -/

open Set MeasureTheory Filter Topology
namespace DefocusingNLS

theorem spectralHarmonicCutoff_core_zero (ell : ℕ) (R l ε : ℝ) (hε : 0 < ε)
    (u : SpectralHarmonicEnergy ell R) :
    (fun r => spectralHarmonicValue ell R (spectralHarmonicCutoff ell R l ε hε u) r)
      =ᵐ[(radialPressureMeasure R).restrict (Iic (l+ε))] 0 := by
  change ∀ᵐ r ∂(radialPressureMeasure R).restrict (Iic (l+ε)),
    spectralHarmonicValue ell R (spectralHarmonicCutoff ell R l ε hε u) r=0
  rw [ae_restrict_iff' measurableSet_Iic]
  filter_upwards [spectralL2ComplexMultiplier_ae (radialPressureMeasure R)
    (spectralCollarWeight R l ε).density (spectralCollarWeight R l ε).radial_measurable
    (spectralCollarWeight R l ε).bound (spectralCollarWeight R l ε).radial_bound
    (spectralHarmonicValue ell R u)] with r hr hrl
  rw [spectralHarmonicCutoff_value,hr]
  change spectralCollarCutoff l ε r • spectralHarmonicValue ell R u r=0
  rw [spectralCollarCutoff_zero l ε r hε hrl,zero_smul]

theorem spectralHarmonicCore_test_dense (ell : ℕ) (R l : ℝ) (hl : 0 < l) (hlR : l < R)
    (u : SpectralHarmonicPair ell R) (hu : u ∈ spectralHarmonicCoreSubspace ell R l) :
    ∃ v : ℕ → SpectralHarmonicPair ell R,
      Tendsto v atTop (𝓝 u) ∧
      ∀ n, ∃ δ : ℝ, 0 < δ ∧ v n ∈ spectralHarmonicCoreSubspace ell R (l+δ) := by
  let ε := fun n : ℕ => ((R-l)/4)*(1/((n : ℝ)+1))
  have he (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hU (n : ℕ) : l+2*ε n ≤ R := by
    have hN : 0 < (n : ℝ)+1 := by positivity
    have hq : 1/((n : ℝ)+1) ≤ 1 := (div_le_one hN).2 (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hm := mul_le_mul_of_nonneg_left hq (show 0 ≤ (R-l)/4 by positivity)
    dsimp [ε]
    nlinarith
  have ht : Tendsto ε atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => ((R-l)/4)*(1/((n : ℝ)+1))) atTop (𝓝 0)
    simpa only [mul_zero] using (tendsto_const_nhds (x := (R-l)/4)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have huc : (fun r => spectralHarmonicValue ell R u.fst r)
      =ᵐ[(radialPressureMeasure R).restrict (Iic l)] 0 :=
    (spectralHarmonicCore_mem ell R l u).mp hu
  have hc := spectralHarmonicCutoff_tendsto ell R l (hl.trans hlR) hl ε he hU ht u.fst huc
  let J := WithLp.prodContinuousLinearEquiv 2 ℂ (SpectralHarmonicEnergy ell R)
    (SpectralHarmonicEnergy ell R)
  let v := fun n => J.symm (spectralHarmonicCutoff ell R l (ε n) (he n) u.fst,u.snd)
  refine ⟨v,?_,fun n => ⟨ε n,he n,?_⟩⟩
  · have hv := J.symm.continuous.continuousAt.tendsto.comp
      (hc.prodMk_nhds (tendsto_const_nhds (x := u.snd)))
    have hJu : J.symm (u.fst,u.snd)=u := rfl
    rw [hJu] at hv
    exact hv
  · apply (spectralHarmonicCore_mem ell R (l+ε n) (v n)).mpr
    exact spectralHarmonicCutoff_core_zero ell R l (ε n) (he n) u.fst

end DefocusingNLS

end OAI
