import OAI.Analysis.RCDHeat.DynamicalPlan
import Mathlib.Topology.Sequences

namespace OAI

/-! # One full-measure set for all times of continuous observables -/

open Set Filter MeasureTheory TopologicalSpace
noncomputable section
namespace RegularPointCoordinates
variable {A : Type*} [MeasurableSpace A] (μ : Measure A)

theorem ae_eq_all_time_of_continuous (F G : A → Time → ℝ)
    (hF : ∀ᵐ a ∂μ, Continuous (F a)) (hG : ∀ᵐ a ∂μ, Continuous (G a))
    (heq : ∀ t : Time, ∀ᵐ a ∂μ, F a t=G a t) :
    ∀ᵐ a ∂μ, ∀ t : Time, F a t=G a t := by
  have hseq : ∀ᵐ a ∂μ, ∀ k : ℕ, F a (denseSeq Time k)=G a (denseSeq Time k) :=
    ae_all_iff.mpr (fun k => heq (denseSeq Time k))
  filter_upwards [hF,hG,hseq] with a hf hg he
  have hfun : F a=G a := Continuous.ext_on (denseRange_denseSeq Time) hf hg (by
    rintro _ ⟨k,rfl⟩
    exact he k)
  exact congrFun hfun

end RegularPointCoordinates

end

end OAI
