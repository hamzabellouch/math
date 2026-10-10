import OAI.Probability.SLE.Geometry.PublishedInputs

namespace OAI

/-! The open-tube consequence of the SLE support theorem.

Tran–Yuan, *A support theorem for SLE curves*, Electron. J. Probab. 25
(2020), paper 18, Proposition 6.4 (printed page 18), as used in Theorem 1.1
and Corollary 1.2, DOI 10.1214/20-EJP425. Proposition 6.4 places every
simple capacity-parametrized curve in the uniform support.
Only positive probabilities of their uniform neighborhoods are assumed below;
there is no uniform bound over curves or stopped pasts in this input.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace SLEExactGauge

/-- The simple-curve inclusion in the published support theorem, restricted
to finite deterministic capacity intervals. -/
def PublishedSimpleTraceSupport {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : Ω → ℝ≥0 → ℂ) : Prop :=
  ∀ (T : ℝ≥0), 0 < T → ∀ (β : ℝ≥0 → ℂ) (U : ℝ≥0 → ℝ),
    Continuous U → IsCapacityTwoTrace U β →
    InjOn β (Icc 0 T) → (∀ t ∈ Ioc 0 T, β t ∈ upperHalfPlane) →
    ∀ ε : ℝ, 0 < ε → 0 < P {ω | ∀ t ∈ Icc 0 T, dist (γ ω t) (β t) < ε}

/-- The pointwise support input yields the exact passage event used in the
ribbon proof: containment in an open tube and a visit to the terminal target. -/
theorem slit_tube_support_of_published_support
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ : Ω → ℝ≥0 → ℂ) (hpublished : PublishedSimpleTraceSupport P γ)
    (T : ℝ≥0) (hT : 0 < T) (β : ℝ≥0 → ℂ) (U : ℝ≥0 → ℝ)
    (hU : Continuous U) (hβ : IsCapacityTwoTrace U β)
    (hinj : InjOn β (Icc 0 T)) (hinterior : ∀ t ∈ Ioc 0 T, β t ∈ upperHalfPlane)
    (N V : Set ℂ) (hN : IsOpen N) (hV : IsOpen V)
    (hsub : β '' Icc 0 T ⊆ N) (hend : β T ∈ V) :
    0 < P {ω | (∀ t ∈ Icc 0 T, γ ω t ∈ N) ∧ γ ω T ∈ V} := by
  obtain ⟨G, F, hw⟩ := hβ
  have hc : IsCompact (β '' Icc 0 T) := isCompact_Icc.image hw.1
  obtain ⟨ε, hε, hεN⟩ := hc.exists_thickening_subset_open hN hsub
  obtain ⟨η, hη, hηV⟩ := Metric.isOpen_iff.mp hV (β T) hend
  have hp := hpublished T hT β U hU ⟨G, F, hw⟩ hinj hinterior
    (min ε η) (lt_min hε hη)
  apply hp.trans_le
  apply measure_mono
  intro ω hω
  constructor
  · intro t ht
    apply hεN
    apply mem_thickening_iff.mpr
    exact ⟨β t, mem_image_of_mem β ht, (hω t ht).trans_le (min_le_left _ _)⟩
  · apply hηV
    exact (hω T (mem_Icc.mpr ⟨zero_le, le_rfl⟩)).trans_le (min_le_right _ _)

end SLEExactGauge

end

end OAI
