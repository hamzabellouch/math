import OAI.Probability.FirstPassage.ProbabilityFoundations
import Mathlib.Probability.Distributions.Gamma

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory

/-- An independent, identically distributed edge environment with marginal law `ν`. -/
structure IidEnvironment {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure ℝ) (P : Measure Ω) (τ : PlanarFPP.Edge → Ω → ℝ) : Prop where
  probability : IsProbabilityMeasure P
  measurable : ∀ e, Measurable (τ e)
  independent : iIndepFun τ P
  marginal : ∀ e, Measure.map (τ e) P = ν

/-- An iid edge environment with Gamma marginal law. -/
abbrev GammaEnvironment {Ω : Type*} [MeasurableSpace Ω]
    (shape rate : ℝ) (P : Measure Ω) (τ : PlanarFPP.Edge → Ω → ℝ) :=
  IidEnvironment (gammaMeasure shape rate) P τ

/-- The product law of the edge weights. -/
noncomputable def iidProductLaw (ν : Measure ℝ) : Measure (PlanarFPP.Edge → ℝ) :=
  Measure.infinitePi (fun _ : PlanarFPP.Edge => ν)

/-- The passage-time limit predicate on the product probability space with marginal `ν`. -/
def HasTimeConstantFor (ν : Measure ℝ) (μ : PlanarFPP.Plane → ℝ) : Prop :=
  PlanarFPP.IsTimeConstant (iidProductLaw ν) (fun e ω => ω e) μ

/-- The coordinate evaluations form an iid environment under the product law. -/
theorem iidProductLaw_environment (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IidEnvironment ν (iidProductLaw ν) (fun e ω => ω e) where
  probability := inferInstanceAs
    (IsProbabilityMeasure (Measure.infinitePi (fun _ : PlanarFPP.Edge => ν)))
  measurable := measurable_pi_apply
  independent := iIndepFun_infinitePi (X := fun _ (x : ℝ) => x)
    (fun _ => measurable_id)
  marginal := Measure.infinitePi_map_eval _

/-- Gamma product environments exist for every positive shape and rate. -/
theorem gammaProductLaw_environment (shape rate : ℝ)
    (hshape : 0 < shape) (hrate : 0 < rate) :
    GammaEnvironment shape rate (iidProductLaw (gammaMeasure shape rate))
      (fun e ω => ω e) := by
  let : IsProbabilityMeasure (gammaMeasure shape rate) :=
    isProbabilityMeasure_gammaMeasure hshape hrate
  exact iidProductLaw_environment (gammaMeasure shape rate)

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ν : Measure ℝ} {P : Measure Ω} {τ : PlanarFPP.Edge → Ω → ℝ}

/-- The joint law on a finite set of edges, including the empty set. -/
theorem IidEnvironment.finiteJointLaw (h : IidEnvironment ν P τ)
    (S : Finset PlanarFPP.Edge) :
    P.map (fun ω (e : S) => τ e ω) = Measure.pi (fun _ : S => ν) := by
  have hi := h.independent.precomp
    (Subtype.val_injective : Function.Injective (fun e : S => (e : PlanarFPP.Edge)))
  rw [iIndepFun.map_fun_eq_pi_map (fun e : S => (h.measurable e).aemeasurable) hi]
  simp only [h.marginal]

/-- Passage time is measurable in an iid edge environment. -/
theorem IidEnvironment.measurable_passageTime (h : IidEnvironment ν P τ)
    (p q : PlanarFPP.Vertex) :
    Measurable (fun ω => PlanarFPP.passageTime (fun e => τ e ω) p q) :=
  PlanarFPP.measurable_passageTime h.measurable p q

/-- The exponential environment with rate one is the corresponding iid environment. -/
theorem iid_expOne_iff :
    IidEnvironment (expMeasure 1) P τ ↔ PlanarFPP.ExponentialEnvironment P τ := by
  constructor
  · intro h
    exact ⟨h.probability, h.measurable, h.independent, h.marginal⟩
  · intro h
    exact ⟨h.probability, h.measurable, h.independent, h.marginal⟩

end GammaFPP

end OAI
