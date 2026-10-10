import OAI.Probability.SLE.SausageCharge

namespace OAI

/-! Measurability of the actual all-time cell visits and terminal-sausage
candidate tests used by the dense cover. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

local instance coverEventPathMeasurableSpace : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance coverEventPathBorelSpace : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

lemma isClosed_compact_time_hit (s t : ℝ≥0) {A : Set ℂ} (hA : IsClosed A) :
    IsClosed {f : C(ℝ≥0, ℂ) | ∃ u ∈ Icc s t, f u ∈ A} := by
  have hf : Continuous (fun p : C(ℝ≥0, ℂ) × Icc s t => p.1 p.2) :=
    continuous_eval.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))
  have hc := isClosedMap_fst_of_compactSpace _ (hA.preimage hf)
  convert hc using 1
  ext f
  simp only [mem_ofPred_eq, mem_image, Prod.exists]
  constructor
  · rintro ⟨u, hu, hfu⟩
    exact ⟨f, ⟨u, hu⟩, hfu, rfl⟩
  · rintro ⟨g, u, hgu, rfl⟩
    exact ⟨u, u.property, hgu⟩

lemma measurableSet_whole_time_hit {A : Set ℂ} (hA : IsClosed A) :
    MeasurableSet {f : C(ℝ≥0, ℂ) | ∃ u : ℝ≥0, f u ∈ A} := by
  have he : {f : C(ℝ≥0, ℂ) | ∃ u : ℝ≥0, f u ∈ A} =
      ⋃ n : ℕ, {f | ∃ u ∈ Icc 0 (n : ℝ≥0), f u ∈ A} := by
    ext f
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨n, hn⟩ := exists_nat_ge u
      exact ⟨n, u, ⟨zero_le, hn⟩, hu⟩
    · rintro ⟨n, u, _, hu⟩
      exact ⟨u, hu⟩
  rw [he]
  exact MeasurableSet.iUnion (fun n => (isClosed_compact_time_hit 0 n hA).measurableSet)

lemma measurableSet_trace_hits_closed
    {Ω : Type*} [MeasurableSpace Ω] (f : Ω → C(ℝ≥0, ℂ)) (hf : Measurable f)
    {A : Set ℂ} (hA : IsClosed A) :
    MeasurableSet {ω | ∃ u : ℝ≥0, f ω u ∈ A} :=
  hf (measurableSet_whole_time_hit hA)

lemma measurableSet_sausage_candidate
    {Ω : Type*} [MeasurableSpace Ω] (f : Ω → C(ℝ≥0, ℂ)) (hf : Measurable f)
    (κ v b : ℝ) (D : Set ℂ) :
    MeasurableSet {ω | ENNReal.ofReal b ≤ wholeSausageCharge κ (f ω) v D} :=
  measurableSet_le measurable_const ((wholeSausageCharge_measurable κ v D).comp hf)

/-- Both visit and no-candidate information is terminal information. The
finite change of law is applied later only to an adapted containing event. -/
lemma measurableSet_visited_without_candidate
    {Ω ι : Type*} [MeasurableSpace Ω]
    (f : Ω → C(ℝ≥0, ℂ)) (hf : Measurable f)
    (κ v : ℝ) (I : Finset ι) (D : ι → Set ℂ) (b : ι → ℝ)
    {Q : Set ℂ} (hQ : IsClosed Q) :
    MeasurableSet {ω | (∃ u : ℝ≥0, f ω u ∈ Q) ∧
      ∀ i ∈ I, wholeSausageCharge κ (f ω) v (D i) < ENNReal.ofReal (b i)} := by
  apply (measurableSet_trace_hits_closed f hf hQ).inter
  have hm : MeasurableSet (⋂ i ∈ I,
      {ω | wholeSausageCharge κ (f ω) v (D i) < ENNReal.ofReal (b i)}) :=
    I.measurableSet_biInter (fun i _ =>
      measurableSet_lt ((wholeSausageCharge_measurable κ v (D i)).comp hf) measurable_const)
  have he : {ω | ∀ i ∈ I,
      wholeSausageCharge κ (f ω) v (D i) < ENNReal.ofReal (b i)} =
      ⋂ i ∈ I, {ω | wholeSausageCharge κ (f ω) v (D i) < ENNReal.ofReal (b i)} := by
    ext ω
    simp only [mem_iInter, mem_ofPred_eq]
  change MeasurableSet {ω | ∀ i ∈ I,
    wholeSausageCharge κ (f ω) v (D i) < ENNReal.ofReal (b i)}
  rw [he]
  exact hm

end SLEExactGauge

end

end OAI
