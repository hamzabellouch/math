import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.IntermediateValue

namespace OAI

/-!
# Material trajectories under an onto clock

The change of clock used in §6 of *Universal Computation with Eventually
Stationary Navier–Stokes Forcing* and in *Scalar Potentials and Slow Clocks
for Forced Fluid Computation*. These lemmas concern the actual ODE and
observation event; no computation/flow correspondence is postulated here.
-/

namespace ForcedComputation

section Trajectories

variable {E : Type*}

/-- The nonnegative-time particle observation used in the manuscripts. -/
def Reaches (X : ℝ → E) (O : Set E) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ X t ∈ O

/-- A clock visits every nonnegative internal time and never visits a negative one. -/
def OntoClock (τ : ℝ → ℝ) : Prop :=
  (∀ t, 0 ≤ t → 0 ≤ τ t) ∧ ∀ s, 0 ≤ s → ∃ t, 0 ≤ t ∧ τ t = s

theorem reaches_comp_iff {τ : ℝ → ℝ} (hτ : OntoClock τ)
    (X : ℝ → E) (O : Set E) : Reaches (X ∘ τ) O ↔ Reaches X O := by
  constructor
  · rintro ⟨t, ht, hO⟩
    exact ⟨τ t, hτ.1 t ht, hO⟩
  · rintro ⟨s, hs, hO⟩
    obtain ⟨t, ht, he⟩ := hτ.2 s hs
    exact ⟨t, ht, by simpa only [Function.comp_apply, he] using hO⟩

/-- Chain rule for the material ODE, including the initial condition. -/
theorem trajectory_reparametrization [NormedAddCommGroup E] [NormedSpace ℝ E]
    {V : ℝ → E → E} {X : ℝ → E}
    {τ a : ℝ → ℝ} {x₀ : E}
    (hX₀ : X 0 = x₀) (hτ₀ : τ 0 = 0)
    (hX : ∀ s, 0 ≤ s → HasDerivAt X (V s (X s)) s)
    (hτ : ∀ t, 0 ≤ t → HasDerivAt τ (a t) t)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ τ t) :
    (X ∘ τ) 0 = x₀ ∧
      ∀ t, 0 ≤ t → HasDerivAt (X ∘ τ)
        (a t • V (τ t) ((X ∘ τ) t)) t := by
  refine ⟨by simp only [Function.comp_apply, hτ₀, hX₀], ?_⟩
  intro t ht
  exact (hX (τ t) (hnonneg t ht)).scomp t (hτ t ht)

end Trajectories

/-- The logarithmic slowdown traverses infinitely many periods. -/
noncomputable def logClock (t : ℝ) : ℝ := Real.log (1 + t)

theorem logClock_onto : OntoClock logClock := by
  constructor
  · intro t ht
    exact Real.log_nonneg (by linarith)
  · intro s hs
    refine ⟨Real.exp s - 1, sub_nonneg.mpr (Real.one_le_exp_iff.mpr hs), ?_⟩
    simp [logClock]

theorem logClock_hasDerivAt {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt logClock (1 / (1 + t)) t := by
  have hp : 0 < 1 + t := by linarith
  change HasDerivAt (fun s : ℝ => Real.log (1 + s)) (1 / (1 + t)) t
  simpa only [id_eq] using ((hasDerivAt_id t).const_add 1).log hp.ne'

theorem logClock_reaches_iff {E : Type*} (X : ℝ → E) (O : Set E) :
    Reaches (X ∘ logClock) O ↔ Reaches X O :=
  reaches_comp_iff logClock_onto X O

end ForcedComputation

end OAI
