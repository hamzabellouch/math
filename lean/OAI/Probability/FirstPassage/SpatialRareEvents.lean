import OAI.Probability.FirstPassage.EndpointTranslation

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable def spatialTranslate (b : ℝ) (k m : ℕ) (ih : ℤ×ℤ) : Vertex :=
  (ih.1*(2 : ℤ)^m,⌊b*(ih.1*(2 : ℤ)^m)⌋+ih.2*(2 : ℤ)^k)

noncomputable def spatialRareEvent (b m₀ am ap K η : ℝ) (k m : ℕ) (ih : ℤ×ℤ) : Set (Edge → ℝ) :=
  eitherEndpointEvent b m₀ am ap 4 4 η k m (spatialTranslate b k m ih) ∪
    crossingEvent b m₀ K ((2 : ℝ)^k) ((2 : ℤ)^m) (spatialTranslate b k m (ih+(1,0)))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem actual_spatial_rare_scales (henv : ExponentialEnvironment P τ)
    (b q₀ η : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) (hη : 0 < η)
    (N : ℕ) (S D : ℝ) :
    ∃ k : ℕ, N < k ∧ S ≤ (2 : ℝ)^k ∧
      D*(2 : ℝ)^k ≤ (characteristicLength P τ actualSourceTimeConstant b q₀ k : ℝ) ∧
      ∀ ih : ℤ×ℤ, P.real {ω | (fun e => τ e ω) ∈ spatialRareEvent b
        (actualSourceTimeConstant (direction b)) (extremeSlope actualSourceTimeConstant b false)
        (extremeSlope actualSourceTimeConstant b true) (sourceCrossingK actualSourceTimeConstant b) η k
        (characteristicExponent P τ actualSourceTimeConstant b q₀ k) ih} ≤ 2*q₀ := by
  let _ := henv.probability
  let μ := actualSourceTimeConstant
  have hμ := actualSourceTimeConstant_norm
  have ht := actualSourceTimeConstant_isTimeConstant henv
  obtain ⟨k₀,k,hkt,_hrec,hend⟩ := actual_arbitrary_endpoints henv b q₀ hb hq hq1
  have he := hend 4 4 η (by norm_num) (by norm_num) hη (fun _ => 0)
  have hs := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp hkt
  have hr := (exponential_characteristic_lengths_ratio henv μ hμ ht b q₀ hb hq hq1).comp hkt
  have hc := hkt.eventually (exponential_characteristic_lengths_exist henv μ hμ ht b q₀ hb hq)
  obtain ⟨n,hn,hns,hnr,hnc,hne⟩ := ((hkt.eventually (eventually_gt_atTop N)).and
    ((hs.eventually (eventually_ge_atTop S)).and
    ((hr.eventually (eventually_ge_atTop D)).and (hc.and (he.eventually (gt_mem_nhds hq)))))).exists
  refine ⟨k n,hn,hns,(le_div_iff₀ (by positivity : (0 : ℝ) < 2^(k n))).mp hnr,?_⟩
  intro ih
  let m := characteristicExponent P τ μ b q₀ (k n)
  let v := spatialTranslate b (k n) m ih
  let v' := spatialTranslate b (k n) m (ih+(1,0))
  have hp : P.real {ω | (fun e => τ e ω) ∈ eitherEndpointEvent b (μ (direction b))
      (extremeSlope μ b false) (extremeSlope μ b true) 4 4 η (k n) m v} ≤ q₀ := by
    have heq : P.real {ω | (fun e => τ e ω) ∈ eitherEndpointEvent b (μ (direction b))
        (extremeSlope μ b false) (extremeSlope μ b true) 4 4 η (k n) m v} =
      P.real {ω | (fun e => τ e ω) ∈ eitherEndpointEvent b (μ (direction b))
        (extremeSlope μ b false) (extremeSlope μ b true) 4 4 η (k n) m 0} := by
      unfold Measure.real
      rw [eitherEndpointEvent_probability_translate henv,eitherEndpointEvent_probability_translate henv]
    rw [heq]
    exact hne.le
  have hcross : P.real {ω | (fun e => τ e ω) ∈ crossingEvent b (μ (direction b))
      (sourceCrossingK μ b) ((2 : ℝ)^(k n)) ((2 : ℤ)^m) v'} ≤ q₀ := by
    unfold Measure.real
    rw [crossingEvent_probability_translate henv]
    exact hnc.2
  have hu := measureReal_union_le (μ := P)
    {ω | (fun e => τ e ω) ∈ eitherEndpointEvent b (μ (direction b))
      (extremeSlope μ b false) (extremeSlope μ b true) 4 4 η (k n) m v}
    {ω | (fun e => τ e ω) ∈ crossingEvent b (μ (direction b))
      (sourceCrossingK μ b) ((2 : ℝ)^(k n)) ((2 : ℤ)^m) v'}
  change _ ≤ 2*q₀
  exact hu.trans (by linarith)

end PlanarFPP

end OAI
