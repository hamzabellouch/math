import OAI.Probability.MatroidProphet.Main
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

namespace MatroidProphet.General

open MeasureTheory ProbabilityTheory

/-- A decision uses only the entire initial seed, the initially observed vector,
and the label/value history through the current arrival. -/
structure OnlineRule (n : ℕ) (R : Type*) [MeasurableSpace R] where
  decide : (k : Fin n) → R → Weights n → History n k → Bool
  measurable_decide : ∀ k, Measurable
    (fun x : R × (Weights n × History n k) => decide k x.1 x.2.1 x.2.2)

def decisionAt {n : ℕ} {R : Type*} [MeasurableSpace R]
    (A : OnlineRule n R) (r : R) (s v : Weights n)
    (π : ArrivalOrder n) (k : Fin n) : Bool :=
  A.decide k r s (history v π k)

noncomputable def acceptedThrough {n : ℕ} {R : Type*} [MeasurableSpace R]
    (A : OnlineRule n R) (r : R) (s v : Weights n)
    (π : ArrivalOrder n) (t : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun e =>
    (π.symm e).val < t ∧ decisionAt A r s v π (π.symm e) = true

noncomputable def reward {n : ℕ} {R : Type*} [MeasurableSpace R]
    (A : OnlineRule n R) (r : R) (s v : Weights n) (π : ArrivalOrder n) : ℝ :=
  ∑ e ∈ acceptedThrough A r s v π n, v e

def Feasible {n : ℕ} {R : Type*} [MeasurableSpace R]
    (M : Matroid (Fin n)) (A : OnlineRule n R) : Prop :=
  ∀ (r : R) (s v : Weights n) (π : ArrivalOrder n) (t : ℕ),
    (∀ e, 0 ≤ s e) → (∀ e, 0 ≤ v e) →
    M.Indep (acceptedThrough A r s v π t : Set (Fin n))

/-- The observation mask is a measurable function of the seed alone. -/
structure HiddenRule (n : ℕ) (R : Type*) [MeasurableSpace R] where
  mask : R → Finset (Fin n)
  measurable_mask : Measurable mask
  core : OnlineRule n R

noncomputable def observed {n : ℕ} {R : Type*} [MeasurableSpace R]
    (A : HiddenRule n R) (r : R) (w : Weights n) : Weights n := by
  classical
  exact fun e => if e ∈ A.mask r then w e else 0

noncomputable def hiddenAcceptedThrough {n : ℕ} {R : Type*} [MeasurableSpace R]
    (A : HiddenRule n R) (r : R) (w : Weights n)
    (π : ArrivalOrder n) (t : ℕ) : Finset (Fin n) :=
  acceptedThrough A.core r (observed A r w) w π t \ A.mask r

noncomputable def hiddenReward {n : ℕ} {R : Type*} [MeasurableSpace R]
    (A : HiddenRule n R) (r : R) (w : Weights n) (π : ArrivalOrder n) : ℝ :=
  ∑ e ∈ hiddenAcceptedThrough A r w π n, w e

noncomputable def hiddenWorstReward {n : ℕ} {R : Type*} [MeasurableSpace R]
    (A : HiddenRule n R) (w : Weights n) (r : R) : ℝ := by
  classical
  exact Finset.univ.inf' Finset.univ_nonempty (hiddenReward A r w)

def HiddenFeasible {n : ℕ} {R : Type*} [MeasurableSpace R]
    (M : Matroid (Fin n)) (A : HiddenRule n R) : Prop :=
  ∀ (w : Weights n), (∀ e, 0 ≤ w e) →
    ∀ (r : R) (π : ArrivalOrder n) (t : ℕ),
      M.Indep (hiddenAcceptedThrough A r w π t : Set (Fin n))

/-- Sample values on the sacrificed mask, and realized values elsewhere. -/
noncomputable def glue {n : ℕ} (mask : Finset (Fin n)) (s v : Weights n) : Weights n := by
  classical
  exact fun e => if e ∈ mask then s e else v e

noncomputable def simulationHistory {n : ℕ} {R : Type*} [MeasurableSpace R]
    (A : HiddenRule n R) (r : R) (s : Weights n)
    {k : Fin n} (h : History n k) : History n k := by
  classical
  exact fun j => ((h j).1, if (h j).1 ∈ A.mask r then s (h j).1 else (h j).2)

 

noncomputable def simulationDecision {n : ℕ} {R : Type*} [MeasurableSpace R]
    (A : HiddenRule n R) (k : Fin n) (r : R) (s : Weights n)
    (h : History n k) : Bool := by
  classical
  exact if (h ⟨k.val, Nat.lt_succ_self _⟩).1 ∈ A.mask r then false
    else A.core.decide k r (observed A r s) (simulationHistory A r s h)

/-- Full source contract for `lem:simulation`, with arbitrary measurable seed
and probability spaces.  The simulator is constructed before the distributions
and adversary are supplied.  Its decision function is specified concretely;
the conjunction includes exact execution, feasibility, the seed/glued-vector
joint law, integrability, and preservation of the same competitive ratio. -/
def SimulationContract.{u, v} : Prop :=
  ∀ (n : ℕ) (R : Type v) [MeasurableSpace R]
    (M : Matroid (Fin n)) (A : HiddenRule n R)
    (ν : Measure R), IsProbabilityMeasure ν →
    ∀ (c : ℝ), HiddenFeasible M A →
    (∀ (w : Weights n), (∀ e, 0 ≤ w e) →
      c * optimum M w ≤ ∫ r, hiddenWorstReward A w r ∂ν) →
    ∃ B : OnlineRule n R,
      (∀ (k : Fin n) (r : R) (s : Weights n) (h : History n k),
        B.decide k r s h = simulationDecision A k r s h) ∧
      Feasible M B ∧
      (∀ (r : R) (s v : Weights n) (π : ArrivalOrder n) (t : ℕ),
        acceptedThrough B r s v π t =
          hiddenAcceptedThrough A r (glue (A.mask r) s v) π t) ∧
      (∀ (r : R) (s v : Weights n) (π : ArrivalOrder n),
        reward B r s v π = hiddenReward A r (glue (A.mask r) s v) π) ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (S V : Ω → Weights n) (seed : Ω → R),
        Measurable S → Measurable V → Measurable seed →
        (∀ᵐ ω ∂μ, ∀ e, 0 ≤ S ω e) →
        (∀ᵐ ω ∂μ, ∀ e, 0 ≤ V ω e) →
        iIndepFun (pairedCoordinates S V) μ →
        (∀ e, μ.map (fun ω => S ω e) = μ.map (fun ω => V ω e)) →
        IndepFun (fun ω => (S ω, V ω)) seed μ → μ.map seed = ν →
        Integrable (fun ω => optimum M (V ω)) μ →
        ∀ (π : Ω → ArrivalOrder n), Measurable π →
          MeasurePreserving (fun ω => (seed ω, glue (A.mask (seed ω)) (S ω) (V ω)))
            μ (ν.prod (μ.map V)) ∧
          Integrable (fun ω => reward B (seed ω) (S ω) (V ω) (π ω)) μ ∧
          c * (∫ ω, optimum M (V ω) ∂μ) ≤
            ∫ ω, reward B (seed ω) (S ω) (V ω) (π ω) ∂μ

end MatroidProphet.General

end OAI
