import OAI.Probability.PosteriorReplicas.Model

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression

structure Learner (d M T : ℕ) (Ω : Type u) where
  initialChoice : Ω → Bool × State M
  transition : ℕ → Ω → State M → (Vector d × ℝ) → Bool × State M
  output : ℕ → Ω → State M → UnitSphere d

namespace Learner

def start {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω) (ω : Ω) :
    RunStatus M :=
  let a := L.initialChoice ω
  if a.1 then .inr (0, a.2) else .inl a.2

def run {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s : UnitSphere d) (ω : Ω) (x : Samples d T) : ℕ → RunStatus M
  | 0 => L.start ω
  | n + 1 =>
    match L.run s ω x n with
    | .inr done => .inr done
    | .inl state =>
      if hn : n < T then
        let row := x ⟨n, hn⟩
        let a := L.transition (n + 1) ω state (row, ⟪row, s.val⟫)
        if a.1 then .inr (n + 1, a.2) else .inl a.2
      else .inl state

def terminal {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s : UnitSphere d) (ω : Ω) (x : Samples d T) : ℕ × State M :=
  match L.run s ω x T with
  | .inl state => (T, state)
  | .inr done => done

def estimate {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)
    (s : UnitSphere d) (ω : Ω) (x : Samples d T) : UnitSphere d :=
  let a := L.terminal s ω x
  L.output a.1 ω a.2

structure Admissible {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) : Prop where
  initialChoice : AEMeasurable L.initialChoice ρ
  transition : ∀ t a, AEMeasurable (fun z : Ω × (Vector d × ℝ) =>
    L.transition t z.1 a z.2) (ρ.prod (observationReference d))
  output : ∀ t a, AEMeasurable (fun ω => L.output t ω a) ρ
  fixed_experiment : ∀ s, AEMeasurable (fun z : Ω × Samples d T =>
    L.estimate s z.1 z.2) (ρ.prod (sampleLaw d T))
  uniform_experiment : AEMeasurable
    (fun z : UnitSphere d × (Ω × Samples d T) => L.estimate z.1 z.2.1 z.2.2)
    ((uniformSphere d).prod (ρ.prod (sampleLaw d T)))

def success {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) (s : UnitSphere d) : ℝ≥0∞ :=
  (ρ.prod (sampleLaw d T))
    {z | angularError s (L.estimate s z.1 z.2) ≤ ε}

def uniformSuccess {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) : ℝ≥0∞ :=
  ((uniformSphere d).prod (ρ.prod (sampleLaw d T)))
    {z | angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}

end Learner

def SubquadraticMemory : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ → ℕ,
    Asymptotics.IsLittleO atTop (fun d => (M d : ℝ)) (fun d => (d : ℝ) ^ 2) →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
    0 < ε → ε ≤ 1 / 10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Learner d (M d) T Ω, L.Admissible ρ →
    ((2 / 3 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε ∨
      ∀ s, (2 / 3 : ℝ≥0∞) ≤ L.success ρ ε s) →
    c * (d : ℝ) * Real.log (1 / ε) ≤ (T : ℝ)

def FixedQuadraticMemory : Prop :=
  ∀ A₀ : ℝ, 0 < A₀ → ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ,
    ∀ d : ℕ, d₀ ≤ d → ∀ M T : ℕ, (M : ℝ) ≤ A₀ * (d : ℝ) ^ 2 →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Learner d M T Ω, L.Admissible ρ →
    (2 / 3 : ℝ≥0∞) ≤ L.uniformSuccess ρ ε →
    c * (d : ℝ) * Real.log (1 / ε) ≤ (T : ℝ)

open scoped Topology

end PosteriorRegression
end

end OAI
