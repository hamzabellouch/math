import Mathlib

namespace OAI

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace DilutedSpinGlass

abbrev Spin := Bool

def spin (s : Spin) : ℝ := if s then 1 else -1

abbrev Interaction (p : ℕ) := (Fin p → Spin) → ℝ

/-- One interaction together with its factorization witness: theta,a,b,f. -/
abbrev InteractionSample (p : ℕ) :=
  Interaction p × ℝ × ℝ × (Fin p → Spin → ℝ)

structure Model (p : ℕ) where
  alpha : ℝ≥0
  disorder : ProbabilityMeasure (InteractionSample p)
  field : ProbabilityMeasure ℝ

/-- Exactly the standing hypotheses (model:integrability through positivity).
`norm` on the finite function space is max_s |theta(s)|. -/
structure Admissible {p : ℕ} (M : Model p) : Prop where
  arity : 2 ≤ p
  even : Even p
  density : 0 < M.alpha
  interaction_integrable : Integrable (fun z : InteractionSample p => ‖z.1‖)
    M.disorder.toMeasure
  field_integrable : Integrable (fun h : ℝ => |h|) M.field.toMeasure
  factorization : ∀ᵐ z ∂M.disorder.toMeasure,
    0 < z.2.1 ∧ ∀ s : Fin p → Spin,
      Real.exp (z.1 s) = z.2.1 * (1 + z.2.2.1 * ∏ l, z.2.2.2 l (s l)) ∧
      |z.2.2.1 * ∏ l, z.2.2.2 l (s l)| < 1
  independent_f : iIndepFun (fun l (z : InteractionSample p) => z.2.2.2 l)
    M.disorder.toMeasure
  identically_distributed_f : ∀ l j : Fin p,
    IdentDistrib (fun z : InteractionSample p => z.2.2.2 l)
      (fun z : InteractionSample p => z.2.2.2 j)
      M.disorder.toMeasure M.disorder.toMeasure
  independent_b : IndepFun (fun z : InteractionSample p => z.2.2.1)
    (fun z : InteractionSample p => z.2.2.2) M.disorder.toMeasure
  finite_b_moments : ∀ n : ℕ, 1 ≤ n →
    Integrable (fun z : InteractionSample p => (-z.2.2.1) ^ n) M.disorder.toMeasure
  positivity : ∀ n : ℕ, 1 ≤ n →
    0 ≤ ∫ z : InteractionSample p, (-z.2.2.1) ^ n ∂M.disorder.toMeasure

/-- Minus the Hamiltonian, with all index choices including repetitions. -/
noncomputable def logWeight {p N k : ℕ} (theta : Fin k → InteractionSample p)
    (h : Fin N → ℝ) (indices : Fin k → Fin p → Fin N) (σ : Fin N → Spin) : ℝ :=
  (∑ j, (theta j).1 (fun l => σ (indices j l))) + ∑ i, h i * spin (σ i)

noncomputable def logPartition {p N k : ℕ} (theta : Fin k → InteractionSample p)
    (h : Fin N → ℝ) (indices : Fin k → Fin p → Fin N) : ℝ :=
  Real.log (∑ σ : Fin N → Spin, Real.exp (logWeight theta h indices σ))

/-- F_N, using an explicit uniform average over the independent index labels.
The value at N=0 is irrelevant to the limit; valid system sizes are N>=1. -/
noncomputable def pressure {p : ℕ} (M : Model p) (N : ℕ) : ℝ :=
  (∫ k : ℕ,
    ∫ theta : Fin k → InteractionSample p,
      ∫ h : Fin N → ℝ,
        ((∑ indices : Fin k → Fin p → Fin N, logPartition theta h indices) /
          (Fintype.card (Fin k → Fin p → Fin N) : ℝ))
      ∂Measure.pi (fun _ : Fin N => M.field.toMeasure)
    ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure)
  ∂poissonMeasure (M.alpha * N)) / N

noncomputable def q (x : ℝ) (s : Spin) : ℝ :=
  Real.exp (x * spin s) / (2 * Real.cosh x)

noncomputable def edge {p : ℕ} (theta : Interaction p) (x : Fin p → ℝ) : ℝ :=
  ∑ s : Fin p → Spin, Real.exp (theta s) * ∏ l, q (x l) (s l)

/-- Append the distinguished cavity spin in the last position. -/
def appendSpin {p : ℕ} (s : Fin (p - 1) → Spin) (ε : Spin) (l : Fin p) : Spin :=
  if h : l.val < p - 1 then s ⟨l.val, h⟩ else ε

noncomputable def message {p : ℕ} (theta : Interaction p)
    (x : Fin (p - 1) → ℝ) (ε : Spin) : ℝ :=
  Real.log (∑ s : Fin (p - 1) → Spin,
    Real.exp (theta (appendSpin s ε)) * ∏ l, q (x l) (s l))

noncomputable def siteLog {p k : ℕ} (theta : Fin k → InteractionSample p)
    (h : ℝ) (x : (Fin k × Fin (p - 1)) → ℝ) : ℝ :=
  Real.log ((∑ ε : Spin, Real.exp
    (h * spin ε + ∑ j, message (theta j).1 (fun l => x (j, l)) ε)) / 2)

/-- Use literally the Borel sigma-field of the weak topology at each level,
as stipulated in model.tex. -/
local instance instMeasurableSpaceCarrier_challenge (X : TopCat) : MeasurableSpace X := borel X
local instance instBorelSpaceCarrier_challenge (X : TopCat) : BorelSpace X := ⟨rfl⟩

/-- Nested probability laws: H_0=R and H_{j+1}=P(H_j), with weak topologies. -/
noncomputable def Hierarchy : ℕ → TopCat
  | 0 => TopCat.of ℝ
  | r + 1 => TopCat.of (ProbabilityMeasure (Hierarchy r))

/-- Logarithmic form of the conditional power means T_0 using independent
message labels. The current eta's are held fixed; only their descendants
are integrated. Physical disorder is a fixed argument of g throughout. -/
noncomputable def logMean {ι : Type} [Fintype ι] :
    (r : ℕ) → ((ι → ℝ) → ℝ) → (Fin r → ℝ) → (ι → Hierarchy r) → ℝ
  | 0, g, _, x => g x
  | r + 1, g, m, eta =>
    Real.log (∫ x : ι → Hierarchy r,
      Real.exp (m 0 * logMean r g (fun i => m i.succ) x)
      ∂Measure.pi (fun i => (eta i).toMeasure)) / m 0

/-- Expectation over the root laws eta_0 of each independent message label.
This also gives the r=0 convention (iid real messages, no power means). -/
noncomputable def trialLog {ι : Type} [Fintype ι] (r : ℕ)
    (ζ : Hierarchy (r + 1)) (m : Fin r → ℝ) (g : (ι → ℝ) → ℝ) : ℝ :=
  ∫ eta : ι → Hierarchy r, logMean r g m eta
    ∂Measure.pi (fun _ : ι => ζ.toMeasure)

/-- Admissible exponents 0<m_1<...<m_r<1; vacuous at r=0. -/
def Exponents {r : ℕ} (m : Fin r → ℝ) : Prop :=
  StrictMono m ∧ ∀ i, 0 < m i ∧ m i < 1

/-- The exact finite-depth cavity functional B_r. -/
noncomputable def functional {p : ℕ} (M : Model p) (r : ℕ)
    (ζ : Hierarchy (r + 1)) (m : Fin r → ℝ) : ℝ :=
  Real.log 2 +
    (∫ k : ℕ,
      ∫ theta : Fin k → InteractionSample p,
        ∫ h : ℝ, trialLog r ζ m (siteLog theta h) ∂M.field.toMeasure
      ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure)
    ∂poissonMeasure (M.alpha * p)) -
    (M.alpha : ℝ) * (p - 1 : ℕ) *
      (∫ theta : InteractionSample p,
        trialLog r ζ m (fun x => Real.log (edge theta.1 x)) ∂M.disorder.toMeasure)

noncomputable def phi {p : ℕ} (M : Model p) (r : ℕ) : ℝ :=
  sInf {v : ℝ | ∃ (ζ : Hierarchy (r + 1)) (m : Fin r → ℝ),
    Exponents m ∧ v = functional M r ζ m}

noncomputable def variationalValue {p : ℕ} (M : Model p) : ℝ :=
  ⨅ r : ℕ, phi M r

/-- main:theorem. No boundedness of interactions, fields, or messages is added.
Existence of the thermodynamic limit is part of this convergence assertion. -/
theorem mezard_parisi {p : ℕ} (M : Model p) (hM : Admissible M) :
    Tendsto (pressure M) atTop (𝓝 (variationalValue M)) := by
  sorry

end DilutedSpinGlass

end OAI
