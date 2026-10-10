import OAI.Probability.InvariantIsing.Cavity.CavityProjectorJointHaar
import OAI.Probability.InvariantIsing.Cavity.CavityProjectorHaarMean

namespace OAI

/-! The exact joint law of physical compression matrices and base
projectors.  This also transports measurable logarithmic observables. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_labeled_projector_joint_law {N n m d : ℕ}
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i = a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (l u : Fin m → ℕ)
    (hg : ∀ a i, g i=a ↔ l a ≤ i.val ∧ i.val < u a)
    (hln : ∀ a, l a+n ≤ u a) (hu : ∀ a, u a ≤ N+n)
    (μ : Measure (Orthogonal (N+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    :
    μ.map (fun U => (cavityCompressionGrams g U,
      cavityPhysicalLabeledProjectors g (cavityConcreteComplement es B₀) a₀ U)) =
    (μ.prod ν).map (fun p => (cavityCompressionGrams g p.1,
      cavityLabeledProjectorAction p.2 (cavityCanonicalProjectorFrame k e a₀))) := by
  let Y := (Fin m → Matrix (Fin n) (Fin n) ℝ) × CavityProjectorFrame N m d
  let : BorelSpace (CavityProjectorFrame N m d) := inferInstanceAs
    (BorelSpace ((Fin m → Fin N → Fin N → ℝ) × (Fin N → Fin d → ℝ)))
  let : BorelSpace (Fin m → Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (BorelSpace (Fin m → Fin n → Fin n → ℝ))
  let : SecondCountableTopology (CavityProjectorFrame N m d) := inferInstanceAs
    (SecondCountableTopology ((Fin m → Fin N → Fin N → ℝ) × (Fin N → Fin d → ℝ)))
  let : SecondCountableTopology (Fin m → Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → Fin n → ℝ))
  let : BorelSpace Y := inferInstanceAs
    (BorelSpace ((Fin m → Matrix (Fin n) (Fin n) ℝ) × CavityProjectorFrame N m d))
  let : HasOuterApproxClosed Y := inferInstanceAs
    (HasOuterApproxClosed ((Fin m → Fin n → Fin n → ℝ) ×
      ((Fin m → Fin N → Fin N → ℝ) × (Fin N → Fin d → ℝ))))
  let F : Orthogonal (N+n) → Y := fun U => (cavityCompressionGrams g U,
    cavityPhysicalLabeledProjectors g (cavityConcreteComplement es B₀) a₀ U)
  let G : Orthogonal (N+n) × Orthogonal N → Y := fun p => (cavityCompressionGrams g p.1,
    cavityLabeledProjectorAction p.2 (cavityCanonicalProjectorFrame k e a₀))
  have hF : Measurable F := (measurable_cavityCompressionGrams g).prodMk
    (measurable_cavityPhysicalLabeledProjectors g _ (measurable_cavityConcreteComplement es B₀) a₀)
  have hG : Measurable G := ((measurable_cavityCompressionGrams g).comp measurable_fst).prodMk
    ((measurable_cavityCanonicalProjectorAction k e a₀).comp measurable_snd)
  change μ.map F = (μ.prod ν).map G
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hi : Integrable (fun p => f (G p)) (μ.prod ν) :=
    Integrable.of_bound (f.continuous.measurable.comp hG).aestronglyMeasurable ‖f‖
      (ae_of_all _ fun p => f.norm_coe_le_norm _)
  rw [integral_map hF.aemeasurable f.continuous.aestronglyMeasurable,
    integral_map hG.aemeasurable f.continuous.aestronglyMeasurable, integral_prod _ hi]
  exact cavity_labeled_projector_joint_haar g k ek e es B₀ a₀ l u hg hln hu μ ν
    f f.continuous.measurable ‖f‖ (fun p => f.norm_coe_le_norm p)

theorem cavity_labeled_projector_joint_integral {N n m d : ℕ}
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i = a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (l u : Fin m → ℕ)
    (hg : ∀ a i, g i=a ↔ l a ≤ i.val ∧ i.val < u a)
    (hln : ∀ a, l a+n ≤ u a) (hu : ∀ a, u a ≤ N+n)
    (μ : Measure (Orthogonal (N+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    (f : (Fin m → Matrix (Fin n) (Fin n) ℝ) × CavityProjectorFrame N m d → ℝ)
    (hf : Measurable f) :
    (∫ U, f (cavityCompressionGrams g U,
      cavityPhysicalLabeledProjectors g (cavityConcreteComplement es B₀) a₀ U) ∂μ) =
    ∫ p, f (cavityCompressionGrams g p.1,
      cavityLabeledProjectorAction p.2 (cavityCanonicalProjectorFrame k e a₀)) ∂μ.prod ν := by
  have hF := (measurable_cavityCompressionGrams g).prodMk
    (measurable_cavityPhysicalLabeledProjectors g _ (measurable_cavityConcreteComplement es B₀) a₀)
  have hG := ((measurable_cavityCompressionGrams g).comp measurable_fst).prodMk
    ((measurable_cavityCanonicalProjectorAction k e a₀).comp measurable_snd)
  simp only [Function.comp_def] at hG
  rw [← integral_map hF.aemeasurable hf.aestronglyMeasurable,
    cavity_labeled_projector_joint_law g k ek e es B₀ a₀ l u hg hln hu μ ν,
    integral_map hG.aemeasurable hf.aestronglyMeasurable]

end InvariantIsing

end

end OAI
