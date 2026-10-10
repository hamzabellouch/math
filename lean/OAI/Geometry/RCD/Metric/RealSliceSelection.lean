import OAI.Geometry.RCD.Metric.IntervalMassDrop

namespace OAI

/-! # A positive fraction of the mass lies in one uniform real slice -/

open Set Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {Ω : Type*} [MeasurableSpace Ω]

theorem exists_large_real_slice (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) {a b : ℝ} (hab : a ≤ b)
    (hs : ∀ᵐ z ∂μ, a ≤ f z ∧ f z < b) {n : ℕ} (hn : 0 < n) :
    ∃ k < n, μ.real univ/(n:ℝ) ≤
      μ.real {z | intervalGrid a b n k ≤ f z ∧ f z < intervalGrid a b n (k+1)} := by
  let B := fun t : ℝ => {z | t ≤ f z}
  have hB (t : ℝ) : MeasurableSet (B t) := measurableSet_le measurable_const hf
  have hmono : Antitone B := fun _ _ hij _ hz => hij.trans hz
  obtain ⟨k,hk,hdrop⟩ := exists_large_nested_mass_drop μ hB hmono hab hn
  have hBa : μ (B a)=μ univ := by
    apply measure_congr
    filter_upwards [hs] with z hz
    simp only [B,mem_ofPred_eq,mem_univ,hz.1]
  have hBb : μ (B b)=0 := by
    simpa only [B,not_lt] using ae_iff.mp (hs.mono fun _ hz => hz.2)
  have hdiff : B (intervalGrid a b n k) \ B (intervalGrid a b n (k+1))=
      {z | intervalGrid a b n k ≤ f z ∧ f z < intervalGrid a b n (k+1)} := by
    ext z
    simp [B]
  refine ⟨k,hk,?_⟩
  simpa only [Measure.real,hBa,hBb,ENNReal.toReal_zero,sub_zero,hdiff] using hdrop

end RegularPointCoordinates

end

end OAI
