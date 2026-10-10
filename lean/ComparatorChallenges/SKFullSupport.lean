import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace ZeroTemperatureSK

abbrev Time := Set.Ico (0 : ℝ) 1

def extend (γ : Time → ℝ) (t : ℝ) : ℝ :=
  if ht : t ∈ Set.Ico (0 : ℝ) 1 then γ ⟨t, ht⟩ else 0

structure OrderParameter where
  val : Time → ℝ
  nonneg : ∀ t, 0 ≤ val t
  monotone : Monotone val
  right_continuous : ∀ t, ContinuousWithinAt val (Set.Ici t) t
  integrable : Integrable (extend val)

structure BrownianSystem (Ω : Type*) [MeasurableSpace Ω] where
  law : Measure Ω
  isProbability : IsProbabilityMeasure law
  B : ℝ≥0 → Ω → ℝ
  measurable : ∀ t, Measurable (B t)
  brownian : IsBrownianReal B law

variable {Ω : Type*} [MeasurableSpace Ω]

def incrementFiltration (W : BrownianSystem Ω) (t : ℝ≥0) :
    Filtration ℝ≥0 ‹MeasurableSpace Ω› :=
  Filtration.natural (fun s ω => W.B (t + s) ω - W.B t ω)
    (fun s => ((W.measurable (t + s)).sub (W.measurable t)).stronglyMeasurable)

structure Control (W : BrownianSystem Ω) (t : ℝ≥0) where
  val : ℝ≥0 → Ω → ℝ
  progressive : IsProgressive (incrementFiltration W t) val
  bound : ∀ s ω, |val s ω| ≤ 1

def controlPayoff (W : BrownianSystem Ω) (γ : OrderParameter) (t x : ℝ)
    (α : Control W (Real.toNNReal t)) (ω : Ω) : ℝ :=
  |x + W.B 1 ω - W.B (Real.toNNReal t) ω +
      ∫ s in t..1, extend γ.val s * α.val (Real.toNNReal (s - t)) ω| -
    (1 / 2 : ℝ) * ∫ s in t..1, extend γ.val s * (α.val (Real.toNNReal (s - t)) ω)^2

def value (W : BrownianSystem Ω) (γ : OrderParameter) (t x : ℝ) : ℝ :=
  sSup (Set.range (fun α : Control W (Real.toNNReal t) =>
    ∫ ω, controlPayoff W γ t x α ω ∂W.law))

def gradient (W : BrownianSystem Ω) (γ : OrderParameter) (t x : ℝ) : ℝ :=
  deriv (value W γ t) x

def curvature (W : BrownianSystem Ω) (γ : OrderParameter) (t x : ℝ) : ℝ :=
  deriv (gradient W γ t) x

def parisi (W : BrownianSystem Ω) (γ : OrderParameter) : ℝ :=
  value W γ 0 0 - (1 / 2 : ℝ) * ∫ t in (0 : ℝ)..1, t * extend γ.val t

def IsMinimizer (W : BrownianSystem Ω) (γ : OrderParameter) : Prop :=
  ∀ η : OrderParameter, parisi W γ ≤ parisi W η

def IsStieltjesMeasure (γ : OrderParameter) (μ : Measure Time) : Prop :=
  ∀ t : Time, μ (Set.Iic t) = ENNReal.ofReal (γ.val t)

def IsDiffusion (W : BrownianSystem Ω) (γ : OrderParameter)
    (X : ℝ≥0 → Ω → ℝ) : Prop :=
  IsProgressive (Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable)) X ∧
  (∀ᵐ ω ∂W.law, ContinuousOn (fun t : ℝ => X (Real.toNNReal t) ω) (Set.Icc 0 1) ∧
    X 0 ω = 0 ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1,
      X (Real.toNNReal t) ω = W.B (Real.toNNReal t) ω +
        ∫ s in (0 : ℝ)..t, extend γ.val s *
          gradient W γ s (X (Real.toNNReal s) ω))

def squareMoment (W : BrownianSystem Ω) (γ : OrderParameter)
    (X : ℝ≥0 → Ω → ℝ) (t : ℝ) : ℝ :=
  ∫ ω, (gradient W γ t (X (Real.toNNReal t) ω))^2 ∂W.law

def FullSupportConclusion (W : BrownianSystem Ω) (γ : OrderParameter) : Prop :=
  (∃ μ : Measure Time, IsStieltjesMeasure γ μ) ∧
  (∃ X : ℝ≥0 → Ω → ℝ, IsDiffusion W γ X) ∧
  (∀ μ : Measure Time, IsStieltjesMeasure γ μ → μ.support = Set.univ) ∧
  (∀ a b : Time, a < b → γ.val a < γ.val b) ∧
  ∀ X : ℝ≥0 → Ω → ℝ, IsDiffusion W γ X → ∀ t : Time,
    squareMoment W γ X t = (t : ℝ) ∧
    (∫ ω, (curvature W γ t (X (Real.toNNReal t) ω))^2 ∂W.law) = 1

theorem full_support (W : BrownianSystem Ω) (γ : OrderParameter)
    (hmin : IsMinimizer W γ) : FullSupportConclusion W γ := by
  sorry

end ZeroTemperatureSK

end

end OAI
