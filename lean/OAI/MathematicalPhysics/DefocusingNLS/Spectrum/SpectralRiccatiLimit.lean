import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRiccatiBarriers
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace OAI

/-! The normalized forbidden-side logarithmic slope tends to one when its
flux error is bounded by a constant times the inverse square root. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralRiccati_tendsto_one (z D e : ℝ → ℝ) (T C : ℝ)
    (hT : 1≤T) (hz : ContinuousOn z (Ici T))
    (hD : ∀ t, T≤t → HasDerivAt z (D t) t)
    (hz0 : ∀ t, T≤t → 0≤z t)
    (he0 : ∀ t, T≤t → 0≤e t)
    (heC : ∀ t, T≤t → e t≤C/Real.sqrt t)
    (hform : ∀ t, T≤t → D t=Real.sqrt t*(1-(z t)^2)-z t/(2*t)+e t) :
    Tendsto z atTop (𝓝 1) := by
  have htrap (eps : ℝ) (heps : 0<eps) :
      ∃ S : ℝ, ∀ t, S≤t → 1-eps≤z t ∧ z t≤1+eps := by
    let U := max T (max (2*C/eps) (1/eps))
    have hTU : T≤U := le_max_left _ _
    have hU₁ : 2*C/eps≤U := (le_max_left _ _).trans (le_max_right _ _)
    have hU₂ : 1/eps≤U := (le_max_right _ _).trans (le_max_right _ _)
    have hzc : ContinuousOn z (Ici U) := hz.mono (Ici_subset_Ici.mpr hTU)
    have hDz : ∀ t, U≤t → HasDerivAt z (D t) t := fun t ht => hD t (hTU.trans ht)
    have hup (t : ℝ) (ht : U≤t) (hzt : 1+eps≤z t) : D t≤ -(eps/2) := by
      have hTt := hTU.trans ht
      have htt : 1≤t := hT.trans hTt
      have hs : 0<Real.sqrt t := Real.sqrt_pos.mpr (by linarith)
      have hrel : 2*C≤t*eps := (div_le_iff₀ heps).mp (hU₁.trans ht)
      have he : e t≤eps/2*Real.sqrt t := by
        apply (heC t hTt).trans
        apply (div_le_iff₀ hs).mpr
        calc
          C ≤ eps/2*t := by nlinarith
          _ = eps/2*Real.sqrt t*Real.sqrt t := by
            rw [mul_assoc,← pow_two,Real.sq_sqrt (by linarith : 0≤t)]
      rw [hform t hTt]
      simpa only [neg_div] using spectralRiccati_upper (z t) t (e t) eps htt heps hzt he
    have hlo (t : ℝ) (ht : U≤t) (hzt : z t≤1-eps) : eps/2≤D t := by
      have hTt := hTU.trans ht
      have hsmall : 1≤t*eps := (div_le_iff₀ heps).mp (hU₂.trans ht)
      rw [hform t hTt]
      exact spectralRiccati_lower (z t) t (e t) eps (hT.trans hTt) heps
        (hz0 t hTt) hzt (he0 t hTt) (by nlinarith)
    obtain ⟨S₁,_,hS₁⟩ := spectralScalar_eventually_below z D U (1+eps) (eps/2)
      (half_pos heps) hzc hDz hup
    obtain ⟨S₂,_,hS₂⟩ := spectralScalar_eventually_above z D U (1-eps) (eps/2)
      (half_pos heps) hzc hDz hlo
    exact ⟨max S₁ S₂,fun t ht => ⟨hS₂ t ((le_max_right _ _).trans ht),hS₁ t ((le_max_left _ _).trans ht)⟩⟩
  rw [Metric.tendsto_nhds]
  intro eps heps
  obtain ⟨S,hS⟩ := htrap (eps/2) (half_pos heps)
  filter_upwards [eventually_ge_atTop S] with t ht
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith [hS t ht]

end DefocusingNLS

end OAI
