import OAI.Probability.GammaPassage.EndpointTranslationProbability

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.BK Set Finset Filter MeasureTheory ProbabilityTheory
open scoped Topology
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

/-- A single actual scale works simultaneously for every spatial index, and
can also exceed any requested transverse scale and longitudinal aspect ratio. -/
theorem gamma_spatial_rare_scales (henv : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b q₀ η : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) (hη : 0 < η)
    (N : ℕ) (S D : ℝ) :
    ∃ k : ℕ, N < k ∧ S ≤ (2 : ℝ)^k ∧
      D*(2 : ℝ)^k ≤ (characteristicLength P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ k : ℝ) ∧
      ∀ ih : ℤ×ℤ, P.real {ω | (fun e => τ e ω) ∈ spatialRareEvent b
        ((gammaMeanNorm henv hshape hrate) (direction b)) (extremeSlope (gammaMeanNorm henv hshape hrate) b false)
        (extremeSlope (gammaMeanNorm henv hshape hrate) b true) (sourceCrossingK shape rate (gammaMeanNorm henv hshape hrate) b) η k
        (characteristicExponent P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ k) ih} ≤ 2*q₀ := by
  let _ := henv.probability
  let μ := (gammaMeanNorm henv hshape hrate)
  obtain ⟨k₀,k,hkt,_hrec,hend⟩ := gamma_arbitrary_endpoints henv hshape hrate b q₀ hb hq hq1
  have he := hend 4 4 η (by norm_num) (by norm_num) hη (fun _ => 0)
  have hs := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hkt
  have hr := (gamma_characteristic_lengths_ratio henv hshape hrate b q₀ hb hq hq1).comp hkt
  have hc := hkt.eventually (gamma_characteristic_lengths_exist henv hshape hrate b q₀ hb hq)
  obtain ⟨n,hn,hns,hnr,hnc,hne⟩ := ((hkt.eventually (eventually_gt_atTop N)).and
    ((hs.eventually (eventually_ge_atTop S)).and
    ((hr.eventually (eventually_ge_atTop D)).and (hc.and (he.eventually (gt_mem_nhds hq)))))).exists
  refine ⟨k n,hn,hns,(le_div_iff₀ (by positivity : (0 : ℝ) < 2^(k n))).mp hnr,?_⟩
  intro ih
  let m := characteristicExponent P τ shape rate μ b q₀ (k n)
  let v := spatialTranslate b (k n) m ih
  let v' := spatialTranslate b (k n) m (ih+(1,0))
  have hp : P.real {ω | (fun e => τ e ω) ∈ eitherEndpointEvent b (μ (direction b))
      (extremeSlope μ b false) (extremeSlope μ b true) 4 4 η (k n) m v} ≤ q₀ := by
    have heq : P.real {ω | (fun e => τ e ω) ∈ eitherEndpointEvent b (μ (direction b))
        (extremeSlope μ b false) (extremeSlope μ b true) 4 4 η (k n) m v} =
      P.real {ω | (fun e => τ e ω) ∈ eitherEndpointEvent b (μ (direction b))
        (extremeSlope μ b false) (extremeSlope μ b true) 4 4 η (k n) m 0} := by
      unfold Measure.real
      rw [eitherEndpointEvent_probability_translate henv hshape hrate,eitherEndpointEvent_probability_translate henv hshape hrate]
    rw [heq]
    exact hne.le
  have hcross : P.real {ω | (fun e => τ e ω) ∈ crossingEvent b (μ (direction b))
      (sourceCrossingK shape rate μ b) ((2 : ℝ)^(k n)) ((2 : ℤ)^m) v'} ≤ q₀ := by
    unfold Measure.real
    rw [crossingEvent_probability_translate henv]
    exact hnc.2
  have hu := measureReal_union_le (μ := P)
    {ω | (fun e => τ e ω) ∈ eitherEndpointEvent b (μ (direction b))
      (extremeSlope μ b false) (extremeSlope μ b true) 4 4 η (k n) m v}
    {ω | (fun e => τ e ω) ∈ crossingEvent b (μ (direction b))
      (sourceCrossingK shape rate μ b) ((2 : ℝ)^(k n)) ((2 : ℤ)^m) v'}
  change _ ≤ 2*q₀
  exact hu.trans (by linarith)

end GammaFPP.CrossingBridge

end OAI
