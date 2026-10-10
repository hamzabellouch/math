import OAI.Geometry.RCD.Transport.RenyiTreeCompression
import OAI.Geometry.RCD.Transport.ReducedChord

namespace OAI

/-! # Semicontinuity for supported Rényi paths and continuity of the chord -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem continuous_sigma_nonpos_time {K N D : ℝ}
    (hK : K ≤ 0) (hN : 1<N) (hD : 0≤D) : Continuous (fun t : ℝ => sigma K N t D) := by
  by_cases hD0 : D=0
  · simpa only [sigma,hD0,true_or,ite_true] using ENNReal.continuous_ofReal
  by_cases hK0 : K=0
  · simpa only [sigma,hK0,or_true,ite_true] using ENNReal.continuous_ofReal
  have he : (fun t : ℝ => sigma K N t D) =
      fun t => ENNReal.ofReal (Real.sinh (t*D*Real.sqrt (-K/(N-1)))/
        Real.sinh (D*Real.sqrt (-K/(N-1)))) := by
    funext t
    exact sigma_neg_eq (lt_of_le_of_ne hK hK0) hN (lt_of_le_of_ne hD (Ne.symm hD0)) t
  rw [he]
  exact ENNReal.continuous_ofReal.comp (by fun_prop)

theorem continuous_reducedChord {K N D : ℝ}
    (hK : K ≤ 0) (hN : 1<N) (hD : 0≤D)
    {A B : ℝ≥0∞} (hA : A≠∞) (hB : B≠∞) : Continuous (reducedChord K N D A B) := by
  exact ((ENNReal.continuous_mul_const hA).comp
    ((continuous_sigma_nonpos_time hK hN hD).comp (continuous_const.sub continuous_subtype_val))).add
    ((ENNReal.continuous_mul_const hB).comp
      ((continuous_sigma_nonpos_time hK hN hD).comp continuous_subtype_val))

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SeparableSpace X]

theorem upperSemicontinuous_renyiIntegral (μ : Measure X) [IsFiniteMeasure μ]
    {N : ℝ} (hN : 1<N) :
    UpperSemicontinuous (fun ν : ProbabilityMeasure X => renyiIntegral μ (ν:Measure X) N) := by
  have hq0 : 0 < 1-1/N := sub_pos.mpr ((div_lt_one (by linarith : 0<N)).mpr hN)
  have hq1 : 1-1/N < 1 := by have := one_div_pos.mpr (by linarith : 0<N); linarith
  have he (ν : ProbabilityMeasure X) : renyiIntegral μ (ν:Measure X) N =
      ENNReal.ofReal (∫ x, ((ν:Measure X).rnDeriv μ x).toReal^(1-1/N) ∂μ) :=
    rnDeriv_power_lintegral_eq_of_integrable μ (ν:Measure X) hq0.le
      (integrable_density_power μ _ (Measure.measurable_rnDeriv _ _).ennreal_toReal
        Measure.integrable_toReal_rnDeriv (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
        hq0.le hq1.le)
  simpa only [he] using upperSemicontinuous_renyiPower μ hq0 hq1

theorem upperSemicontinuous_supported_renyiPath (μ : Measure X) [SigmaFinite μ]
    {B : Set X} (hB : MeasurableSet B) [IsFiniteMeasure (μ.restrict B)]
    (ν : Time → ProbabilityMeasure X) (hν : Continuous ν)
    (hs : ∀ t, ∀ᵐ x ∂(ν t : Measure X), x∈B) {N : ℝ} (hN : 1<N) :
    UpperSemicontinuous (fun t => renyiIntegral μ (ν t : Measure X) N) := by
  have he (t : Time) := renyiIntegral_localized μ (ν t : Measure X) hB (hs t) hN
  simpa only [Function.comp_def,he] using (upperSemicontinuous_renyiIntegral (μ.restrict B) hN).comp hν

end RegularPointCoordinates

namespace RegularPointCoordinates
open Set Filter MeasureTheory
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X]

theorem renyiIntegral_ne_top_of_support (μ ν : Measure X) [SigmaFinite μ] [IsFiniteMeasure ν]
    {B : Set X} (hB : MeasurableSet B) [IsFiniteMeasure (μ.restrict B)]
    (hs : ∀ᵐ x ∂ν, x∈B) {N : ℝ} (hN : 1<N) : renyiIntegral μ ν N ≠ ∞ := by
  have hq0 : 0<1-1/N := sub_pos.mpr ((div_lt_one (by linarith : 0<N)).mpr hN)
  have hq1 : 1-1/N≤1 := by have := one_div_pos.mpr (by linarith : 0<N); linarith
  rw [renyiIntegral,rnDeriv_power_lintegral_eq_of_integrable μ ν hq0.le
    (renyiPower_localized μ ν hB hs hq0 hq1).1]
  exact ENNReal.ofReal_ne_top

theorem ge_continuous_of_dense {F G : Time → ℝ≥0∞}
    (hF : UpperSemicontinuous F) (hG : Continuous G)
    {S : Set Time} (hS : Dense S) (h : ∀ t∈S, G t≤F t) : ∀ t, G t≤F t := by
  have hc : IsClosed {t | G t≤F t} := hF.IsClosed_hypograph.preimage (continuous_id.prodMk hG)
  have he := closure_minimal h hc
  rw [hS.closure_eq] at he
  exact fun t => he (mem_univ t)

theorem continuousAt_of_upperSemicontinuous_lower {F G : Time → ℝ≥0∞}
    (hF : UpperSemicontinuous F) (hG : Continuous G) (hle : ∀ t, G t≤F t)
    (t : Time) (he : G t=F t) : ContinuousAt F t := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have hb' : b<G t := by rwa [he]
    filter_upwards [(tendsto_order.mp hG.continuousAt).1 b hb'] with s hs
    exact hs.trans_le (hle s)
  · intro b hb
    exact hF t b hb

end RegularPointCoordinates

end

end OAI
