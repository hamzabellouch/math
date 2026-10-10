import Mathlib
import OAI.Geometry.SmoothYau.Estimates.FixedRadialChoice
import OAI.Geometry.SmoothYau.NodalMeasure.ActualProfileSpeedNonneg

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set MeasureTheory Filter
open scoped ENNReal Topology

theorem profile_mass_gain {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (E : Set X) (hE : MeasurableSet E) (ε γ θ : ℝ)
    (hε : 0 ≤ ε) (hγ : 0 ≤ γ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hbase : ∀ᵐ x ∂μ, (1-ε)*f x ≤ g x)
    (hcore : ∀ᵐ x ∂μ, x ∈ E → (1+γ)*f x ≤ g x)
    (hmass : θ*(∫ x, f x ∂μ) ≤ ∫ x in E, f x ∂μ) :
    (1-ε+γ*θ)*(∫ x, f x ∂μ) ≤ ∫ x, g x ∂μ := by
  have hi := hf.indicator hE
  have hpoint : ∀ᵐ x ∂μ, (1-ε)*f x+γ*(E.indicator f x) ≤ g x := by
    filter_upwards [hf0,hbase,hcore] with x hx hb hc
    by_cases he : x ∈ E
    · rw [Set.indicator_of_mem he]
      have hh := hc he
      nlinarith [mul_nonneg hε hx]
    · rw [Set.indicator_of_notMem he,mul_zero,add_zero]
      exact hb
  have hle := integral_mono_ae ((hf.const_mul (1-ε)).add (hi.const_mul γ)) hg hpoint
  simp only [Pi.add_apply] at hle
  rw [integral_add (hf.const_mul (1-ε)) (hi.const_mul γ),integral_const_mul,
    integral_const_mul,integral_indicator hE] at hle
  have hh := mul_le_mul_of_nonneg_left hmass hγ
  nlinarith

theorem profile_cycle_numerics (M P Q t : ℝ) (hM : 0 ≤ M)
    (ht : 0 < t) (ht1 : t ≤ 1)
    (hP : (1-t/16)*M ≤ P) (hQ : (1+3*t/8)*P ≤ Q) :
    (1+t/4)*M ≤ Q := by
  have hp := mul_le_mul_of_nonneg_left hP (show 0 ≤ 1+3*t/8 by positivity)
  have hquad : t^2 ≤ t := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hquad hM
  nlinarith only [hp,hQ,hh,mul_nonneg ht.le hM]


end

open Set MeasureTheory Filter
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

def actualProfileCycleGain : ℝ := fixedRadialChoice.fraction*fixedRadialChoice.g₀/768

lemma actualProfileCycleGain_pos : 0 < actualProfileCycleGain := by
  unfold actualProfileCycleGain
  exact div_pos (mul_pos fixedRadialChoice.fraction_pos fixedRadialChoice.gain_pos) (by norm_num)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem actual_metric_profile_cycle (hdim : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) {u : E → ℝ} (hu : ContDiff ℝ ∞ u)
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (ha : ∀ x ∈ closure Ω, coordinateMetricGradient g u x ≠ 0)
    (hstrict : ∀ x ∈ closure Ω, actualProfileStrict g u x)
    (μ : Measure E) [IsLocallyFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    ∃ v : E → ℝ, ContDiff ℝ ∞ v ∧ HasCompactSupport (fun x => v x-u x) ∧
      tsupport (fun x => v x-u x) ⊆ Ω ∧ (∀ x, |v x-u x| < ε) ∧
      (∀ x ∈ closure Ω, coordinateMetricGradient g v x ≠ 0 ∧ actualProfileStrict g v x) ∧
      (1+actualProfileCycleGain)*actualProfileMass g u μ Ω ≤ actualProfileMass g v μ Ω := by
  let D := fixedRadialChoice
  let θ := D.fraction/192
  let t := θ*D.g₀
  have hθ : 0 < θ := div_pos D.fraction_pos (by norm_num)
  have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith [D.fraction_le]
  have ht : 0 < t := mul_pos hθ D.gain_pos
  have ht1 : t ≤ 1 := (mul_le_mul hθ1 D.gain_le D.gain_pos.le (by norm_num)).trans_eq (by ring)
  have htg : t ≤ D.g₀ := by dsimp [t]; nlinarith [D.gain_pos]
  let ν := μ.restrict Ω
  let M := actualProfileMass g u μ Ω
  have hM : 0 ≤ M := actualProfileMass_nonneg g u μ Ω
  have huI : Integrable (actualProfileSpeed g u) ν := integrableOn_actualProfileSpeed g hu hΩc μ
  have hΩae : ∀ᵐ x ∂ν, x ∈ Ω := ae_restrict_mem hΩ.measurableSet
  let := actualProfileWeightedMeasure_finite g hu hΩc μ
  obtain ⟨ψ,U,hψ,hψc,hψs,hψ0,hψp,hU,hUΩ,hfull,hUm⟩ := actual_metric_preparation
    hdim g hu hΩ hΩc ha hstrict (actualProfileWeightedMeasure g u μ Ω)
    (half_pos hε) (show 0 < t/16 by positivity)
  have hψI : Integrable (actualProfileSpeed g ψ) ν := integrableOn_actualProfileSpeed g hψ hΩc μ
  let P := actualProfileMass g ψ μ Ω
  have hP : 0 ≤ P := actualProfileMass_nonneg g ψ μ Ω
  have hrel : ∀ᵐ x ∂ν, (1-t/16)*actualProfileSpeed g u x ≤ actualProfileSpeed g ψ x ∧
      actualProfileSpeed g ψ x ≤ (1+t/16)*actualProfileSpeed g u x := by
    filter_upwards [hΩae] with x hx
    exact actualProfileSpeed_relative_error g u ψ x (hψp x (subset_closure hx)).2.2
  have hPlow : (1-t/16)*M ≤ P := by
    have hh := integral_mono_ae (huI.const_mul (1-t/16)) hψI (hrel.mono fun _ h => h.1)
    simpa only [integral_const_mul,M,P,actualProfileMass,ν] using hh
  have hPup : P ≤ (1+t/16)*M := by
    have hh := integral_mono_ae hψI (huI.const_mul (1+t/16)) (hrel.mono fun _ h => h.2)
    simpa only [integral_const_mul,M,P,actualProfileMass,ν] using hh
  let Mu := ∫ x in U, actualProfileSpeed g u x ∂ν
  let Pu := ∫ x in U, actualProfileSpeed g ψ x ∂ν
  have hMu : 0 ≤ Mu := integral_nonneg (actualProfileSpeed_nonneg g u)
  have hPu : 0 ≤ Pu := integral_nonneg (actualProfileSpeed_nonneg g ψ)
  have hMupos : M/6 ≤ Mu := by
    rw [actualProfileWeightedMeasure_self g hu hΩc hΩ.measurableSet μ,
      actualProfileWeightedMeasure_apply g hu hΩc μ hU.measurableSet] at hUm
    change ENNReal.ofReal M/6 ≤ ENNReal.ofReal Mu at hUm
    have hh := ENNReal.toReal_mono (by simp) hUm
    simpa only [ENNReal.toReal_div,ENNReal.toReal_ofReal hM,ENNReal.toReal_ofReal hMu,
      ENNReal.toReal_ofNat] using hh
  have hMulow : (1-t/16)*Mu ≤ Pu := by
    have hh := integral_mono_ae (μ:=ν.restrict U) (huI.integrableOn.const_mul (1-t/16)) hψI.integrableOn
      (ae_restrict_of_ae (hrel.mono fun _ h => h.1))
    simpa only [integral_const_mul] using hh
  have hMuLow' : (2/3:ℝ)*Mu ≤ Pu := by nlinarith [mul_nonneg (show 0 ≤ 1/3-t/16 by linarith) hMu]
  have hPup' : P ≤ (4/3:ℝ)*M := by nlinarith [mul_nonneg (show 0 ≤ 1/3-t/16 by linarith) hM]
  have hPufrac : P/12 ≤ Pu := by linarith
  let := actualProfileWeightedMeasure_finite g hψ hΩc μ
  obtain ⟨v,G,hv,hvc,hvs,hv0,hvp,hG,hGU,hGm,hgain⟩ := actual_metric_radial_finite
    hdim g hψ hU hUΩ (fun x hx => (hψp x hx).1) (fun x hx => (hψp x hx).2.1) hfull
    (actualProfileWeightedMeasure g ψ μ Ω) D.smooth D.zero_at_zero D.range_bound
    (r:=1/8) (b:=1/256) (show (0:ℝ) ≤ 1/8 by norm_num) (by norm_num) (by norm_num)
    (by norm_num) D.zero_above D.delta_pos D.speed_pos.le
    (show 0 < t/8 by positivity) (show t/8 < 1 by linarith) (half_pos hε)
    D.Fmax D.S D.K D.Fmax_pos D.S_pos D.K_pos D.coefficients D.smallness
    D.q D.radius_pos D.radius_le D.window
  have hvI : Integrable (actualProfileSpeed g v) ν := integrableOn_actualProfileSpeed g hv hΩc μ
  have hGmass : θ*P ≤ ∫ x in G, actualProfileSpeed g ψ x ∂ν := by
    rw [actualProfileWeightedMeasure_apply g hψ hΩc μ hU.measurableSet,
      actualProfileWeightedMeasure_apply g hψ hΩc μ hG] at hGm
    have hGP : 0 ≤ ∫ x in G, actualProfileSpeed g ψ x ∂ν := integral_nonneg (actualProfileSpeed_nonneg g ψ)
    change ENNReal.ofReal Pu/2 * ENNReal.ofReal D.fraction ≤ ENNReal.ofReal (∫ x in G, actualProfileSpeed g ψ x ∂ν) at hGm
    have hh := ENNReal.toReal_mono (by simp) hGm
    simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_ofReal hPu,
      ENNReal.toReal_ofNat,ENNReal.toReal_ofReal D.fraction_pos.le,ENNReal.toReal_ofReal hGP] at hh
    change Pu/2*D.fraction ≤ _ at hh
    have hm := mul_le_mul_of_nonneg_right hPufrac D.fraction_pos.le
    dsimp [θ]
    nlinarith [mul_nonneg D.fraction_pos.le hP]
  have hbase : ∀ᵐ x ∂ν, (1-t/8)*actualProfileSpeed g ψ x ≤ actualProfileSpeed g v x := by
    filter_upwards [hΩae] with x hx
    exact (hvp x (subset_closure hx)).2.2
  have hcore : ∀ᵐ x ∂ν, x ∈ G → (1+D.g₀/2)*actualProfileSpeed g ψ x ≤ actualProfileSpeed g v x := by
    apply ae_of_all
    intro x hx
    have hh := hgain x hx
    have he := D.gain_eq
    have hp := actualProfileSpeed_nonneg g ψ x
    nlinarith [mul_nonneg (show 0 ≤ D.g₀/2-t/8 by linarith) hp]
  have hQ : (1+3*t/8)*P ≤ actualProfileMass g v μ Ω := by
    have hh := profile_mass_gain ν (actualProfileSpeed g ψ) (actualProfileSpeed g v)
      hψI hvI G hG (t/8) (D.g₀/2) θ (by positivity) (by linarith [D.gain_pos])
      (ae_of_all _ (actualProfileSpeed_nonneg g ψ)) hbase hcore hGmass
    have he : 1-t/8+(D.g₀/2)*θ = 1+3*t/8 := by dsimp [t]; ring
    rw [he] at hh
    exact hh
  refine ⟨v,hv,?_,?_,?_,(fun x hx => ⟨(hvp x hx).1,(hvp x hx).2.1⟩),?_⟩
  · have he : ((fun x => v x-ψ x)+(fun x => ψ x-u x)) = (fun x => v x-u x) := by
      funext x; dsimp; ring
    exact he ▸ hvc.add hψc
  · have hs := (tsupport_add (fun x => v x-ψ x) (fun x => ψ x-u x)).trans
      (union_subset (hvs.trans hUΩ) hψs)
    simpa only [Pi.add_apply,sub_add_sub_cancel] using hs
  · intro x
    calc |v x-u x| = |(v x-ψ x)+(ψ x-u x)| := by congr 1; ring
      _ ≤ |v x-ψ x|+|ψ x-u x| := abs_add_le _ _
      _ < ε/2+ε/2 := add_lt_add (hv0 x) (hψ0 x).1
      _ = ε := by ring
  · have hh := profile_cycle_numerics M P (actualProfileMass g v μ Ω) t hM ht ht1 hPlow hQ
    have he : actualProfileCycleGain = t/4 := by dsimp [actualProfileCycleGain,t,θ,D]; ring
    rwa [he]



end YauCounterexamples
end

end OAI
