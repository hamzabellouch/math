import OAI.Probability.GammaPassage.EndpointRecords
import OAI.Probability.GammaPassage.SpatialWitnesses

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.BK Set Finset Filter MeasureTheory ProbabilityTheory
open scoped Topology
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

lemma eitherEndpointEvent_probability_translate (henv : GammaEnvironment shape rate P τ)
    (_hshape : 0 < shape) (_hrate : 0 < rate)
    (b m₀ am ap A R ε : ℝ) (k m : ℕ) (t : Vertex) :
    P {ω | (fun e => τ e ω) ∈ eitherEndpointEvent b m₀ am ap A R ε k m t} =
      P {ω | (fun e => τ e ω) ∈
        arbitraryEndpointEvent b m₀ am A R ε k m ∪ arbitraryEndpointEvent b m₀ ap A R ε k m} := by
  exact henv.translated_event_probability t _
    ((measurableSet_arbitraryEndpointEvent ..).union (measurableSet_arbitraryEndpointEvent ..))

/-- Full arbitrary-endpoint lemma, both signs and uniformly translated boxes,
for the deterministic norm supplied by the actual Gamma environment. -/
theorem gamma_arbitrary_endpoints (henv : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b q₀ : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) :
    ∃ k₀ : ℕ, ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧
      (∀ n, n < k n ∧ k₀ ≤ k n ∧
        ∀ j, j ≤ k n-k₀ → (1/16 : ℝ)^j*(characteristicLength P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ (k n) : ℝ) ≤
          (characteristicLength P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ (k n-j) : ℝ)) ∧
      ∀ A R ε : ℝ, 0 < A → 0 < R → 0 < ε → ∀ t : ℕ → Vertex,
        Tendsto (fun n => P.real {ω | (fun e => τ e ω) ∈ eitherEndpointEvent b
          ((gammaMeanNorm henv hshape hrate) (direction b)) (extremeSlope (gammaMeanNorm henv hshape hrate) b false)
          (extremeSlope (gammaMeanNorm henv hshape hrate) b true) A R ε (k n)
          (characteristicExponent P τ shape rate (gammaMeanNorm henv hshape hrate) b q₀ (k n)) (t n)}) atTop (𝓝 0) := by
  let _ := henv.probability
  obtain ⟨k₀,k,hkt,hrec,hl⟩ := gamma_arbitraryEndpoint_record_scales henv hshape hrate b q₀ hb hq hq1
  refine ⟨k₀,k,hkt,hrec,?_⟩
  intro A R ε hA hR hε t
  have hsum := (hl A R ε hA hR hε false).add (hl A R ε hA hR hε true)
  simp only [add_zero] at hsum
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hsum
  intro n
  unfold Measure.real
  rw [eitherEndpointEvent_probability_translate henv hshape hrate]
  exact measureReal_union_le _ _

end GammaFPP.CrossingBridge

end OAI
