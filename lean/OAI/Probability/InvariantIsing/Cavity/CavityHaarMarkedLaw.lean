import OAI.Probability.InvariantIsing.Cavity.CavityHaarJointLaw
import OAI.Probability.InvariantIsing.Cavity.CavityGaussianMarkedLaw

namespace OAI

/-! Joint probability laws for the physical fresh Haar marks. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

variable {m r q : ℕ} {N : Fin m → ℕ} {X L : Type*}
  [MeasurableSpace X] [MetricSpace L] [MeasurableSpace L]
  [BorelSpace L] [SecondCountableTopology L]

def cavityHaarMarkedMap (l : X → L)
    (v : X → (a : Fin m) → Fin r → Fin (N a) → ℝ)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (p : X × ((a : Fin m) → Orthogonal (N a))) :
    L × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) :=
  (l p.1, cavityGroupMatrixProjection (v p.1) (cavityGroupHaarFrames A₀ p.2))

omit [MetricSpace L] [BorelSpace L] [SecondCountableTopology L] in
lemma measurable_cavityHaarMarkedMap (l : X → L) (hl : Measurable l)
    (v : X → (a : Fin m) → Fin r → Fin (N a) → ℝ) (hv : Measurable v)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) :
    Measurable (cavityHaarMarkedMap l v A₀) := by
  let : OpensMeasurableSpace
      (((a : Fin m) → Fin r → Fin (N a) → ℝ) ×
        ((a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)) :=
    inferInstanceAs (OpensMeasurableSpace
      (((a : Fin m) → Fin r → Fin (N a) → ℝ) ×
        ((a : Fin m) → Fin (N a) → Fin q → ℝ)))
  have hc : Continuous (fun p :
      ((a : Fin m) → Fin r → Fin (N a) → ℝ) ×
        ((a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) =>
      cavityGroupMatrixProjection p.1 p.2) := by
    unfold cavityGroupMatrixProjection
    fun_prop
  exact (hl.comp measurable_fst).prodMk (hc.measurable.comp
    ((hv.comp measurable_fst).prodMk
      ((measurable_cavityGroupHaarFrames A₀).comp measurable_snd)))

def cavityHaarMarkedLaw (P : Measure X) [IsProbabilityMeasure P]
    (μ : (a : Fin m) → Measure (Orthogonal (N a))) [∀ a, IsProbabilityMeasure (μ a)]
    (l : X → L) (hl : Measurable l)
    (v : X → (a : Fin m) → Fin r → Fin (N a) → ℝ) (hv : Measurable v)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ) :
    ProbabilityMeasure (L × EuclideanSpace ℝ (Fin m × (Fin r × Fin q))) :=
  ⟨(P.prod (Measure.pi μ)).map (cavityHaarMarkedMap l v A₀),
    (Measure.isProbabilityMeasure_map_iff
      (measurable_cavityHaarMarkedMap l hl v hv A₀).aemeasurable).mpr inferInstance⟩

omit [MetricSpace L] [BorelSpace L] [SecondCountableTopology L] in
lemma cavityHaarMarkedLaw_integral (P : Measure X) [IsProbabilityMeasure P]
    (μ : (a : Fin m) → Measure (Orthogonal (N a))) [∀ a, IsProbabilityMeasure (μ a)]
    (l : X → L) (hl : Measurable l)
    (v : X → (a : Fin m) → Fin r → Fin (N a) → ℝ) (hv : Measurable v)
    (A₀ : (a : Fin m) → Matrix (Fin (N a)) (Fin q) ℝ)
    (f : L × EuclideanSpace ℝ (Fin m × (Fin r × Fin q)) → ℝ)
    (hf : Measurable f) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, f x ∂(cavityHaarMarkedLaw P μ l hl v hv A₀ : Measure _)) =
      ∫ x, ∫ U, f (l x, cavityGroupMatrixProjection (v x) (cavityGroupHaarFrames A₀ U))
        ∂Measure.pi μ ∂P := by
  have hi : Integrable (fun p => f (cavityHaarMarkedMap l v A₀ p))
      (P.prod (Measure.pi μ)) :=
    Integrable.of_bound ((hf.comp (measurable_cavityHaarMarkedMap l hl v hv A₀)).aestronglyMeasurable)
      C (ae_of_all _ fun p => hb _)
  change (∫ x, f x ∂(P.prod (Measure.pi μ)).map (cavityHaarMarkedMap l v A₀)) = _
  rw [integral_map
    (measurable_cavityHaarMarkedMap l hl v hv A₀).aemeasurable hf.aestronglyMeasurable,
    integral_prod _ hi]
  rfl

end InvariantIsing

end

end OAI
