import OAI.Probability.FirstPassage.EndpointRecords

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable def translatedArbitraryEndpointEvent (b m₀ a A R ε : ℝ) (k m : ℕ)
    (t : Vertex) : Set (Edge → ℝ) :=
  {w | (fun e => w (shiftEdge t e)) ∈ arbitraryEndpointEvent b m₀ a A R ε k m}

lemma mem_translatedArbitraryEndpointEvent (b m₀ a A R ε : ℝ) (k m : ℕ) (t : Vertex) (w : Edge → ℝ) :
    w ∈ translatedArbitraryEndpointEvent b m₀ a A R ε k m t ↔
      ∃ p ds, PathIn p ds {z | z-t ∈ endpointBox b A R k m} ∧ defect w b m₀ a p ds < -ε*(2 : ℝ)^k := by
  change (fun e => w (shiftEdge t e)) ∈ arbitraryEndpointEvent b m₀ a A R ε k m ↔ _
  rw [mem_arbitraryEndpointEvent]
  have hc (p ds) : defect (fun e => w (shiftEdge t e)) b m₀ a p ds=defect w b m₀ a (t+p) ds := by
    simp only [defect,pathCost_translate]
  constructor
  · rintro ⟨p,ds,hin,hcost⟩
    refine ⟨t+p,ds,?_,by rwa [← hc]⟩
    intro i hi
    have he : t+p+displacement (ds.take i)-t=p+displacement (ds.take i) := by abel
    simpa only [mem_ofPred_eq,he] using hin i hi
  · rintro ⟨p,ds,hin,hcost⟩
    refine ⟨p-t,ds,?_,?_⟩
    · intro i hi
      have he : p-t+displacement (ds.take i)=p+displacement (ds.take i)-t := by abel
      simpa only [mem_ofPred_eq,he] using hin i hi
    · rw [hc,add_sub_cancel]
      exact hcost

noncomputable def eitherEndpointEvent (b m₀ am ap A R ε : ℝ) (k m : ℕ) (t : Vertex) : Set (Edge → ℝ) :=
  translatedArbitraryEndpointEvent b m₀ am A R ε k m t ∪
    translatedArbitraryEndpointEvent b m₀ ap A R ε k m t

lemma mem_eitherEndpointEvent (b m₀ am ap A R ε : ℝ) (k m : ℕ) (t : Vertex) (w : Edge → ℝ) :
    w ∈ eitherEndpointEvent b m₀ am ap A R ε k m t ↔
      ∃ p ds, PathIn p ds {z | z-t ∈ endpointBox b A R k m} ∧
        (defect w b m₀ am p ds < -ε*(2 : ℝ)^k ∨ defect w b m₀ ap p ds < -ε*(2 : ℝ)^k) := by
  simp only [eitherEndpointEvent,mem_union,mem_translatedArbitraryEndpointEvent]
  constructor
  · rintro (⟨p,ds,hin,hc⟩ | ⟨p,ds,hin,hc⟩)
    · exact ⟨p,ds,hin,Or.inl hc⟩
    · exact ⟨p,ds,hin,Or.inr hc⟩
  · rintro ⟨p,ds,hin,hc | hc⟩
    · exact Or.inl ⟨p,ds,hin,hc⟩
    · exact Or.inr ⟨p,ds,hin,hc⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

lemma eitherEndpointEvent_probability_translate (henv : ExponentialEnvironment P τ)
    (b m₀ am ap A R ε : ℝ) (k m : ℕ) (t : Vertex) :
    P {ω | (fun e => τ e ω) ∈ eitherEndpointEvent b m₀ am ap A R ε k m t} =
      P {ω | (fun e => τ e ω) ∈
        arbitraryEndpointEvent b m₀ am A R ε k m ∪ arbitraryEndpointEvent b m₀ ap A R ε k m} := by
  exact translated_event_probability henv t _
    ((measurableSet_arbitraryEndpointEvent ..).union (measurableSet_arbitraryEndpointEvent ..))

theorem actual_arbitrary_endpoints (henv : ExponentialEnvironment P τ)
    (b q₀ : ℝ) (hb : |b| ≤ 1) (hq : 0 < q₀) (hq1 : q₀ < 1) :
    ∃ k₀ : ℕ, ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧
      (∀ n, n < k n ∧ k₀ ≤ k n ∧
        ∀ j, j ≤ k n-k₀ → (1/16 : ℝ)^j*(characteristicLength P τ actualSourceTimeConstant b q₀ (k n) : ℝ) ≤
          (characteristicLength P τ actualSourceTimeConstant b q₀ (k n-j) : ℝ)) ∧
      ∀ A R ε : ℝ, 0 < A → 0 < R → 0 < ε → ∀ t : ℕ → Vertex,
        Tendsto (fun n => P.real {ω | (fun e => τ e ω) ∈ eitherEndpointEvent b
          (actualSourceTimeConstant (direction b)) (extremeSlope actualSourceTimeConstant b false)
          (extremeSlope actualSourceTimeConstant b true) A R ε (k n)
          (characteristicExponent P τ actualSourceTimeConstant b q₀ (k n)) (t n)}) atTop (𝓝 0) := by
  let _ := henv.probability
  obtain ⟨k₀,k,hkt,hrec,hl⟩ := actual_arbitraryEndpoint_record_scales henv b q₀ hb hq hq1
  refine ⟨k₀,k,hkt,hrec,?_⟩
  intro A R ε hA hR hε t
  have hsum := (hl A R ε hA hR hε false).add (hl A R ε hA hR hε true)
  simp only [add_zero] at hsum
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hsum
  intro n
  unfold Measure.real
  rw [eitherEndpointEvent_probability_translate henv]
  exact measureReal_union_le _ _

end PlanarFPP

end OAI
