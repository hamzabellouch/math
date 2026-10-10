import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.AngularMoment
import OAI.MeasureTheory.FalconerCompletion.Graphs.NearGrid

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4Near
open Set MeasureTheory
open scoped ENNReal
variable {V : Type*} [MeasurableSpace V]

lemma sourceAngularHND_trivial_bound (d : ℕ) (μ : Measure V) [IsFiniteMeasure μ]
    (a v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Integrable Ψ)
    {U W : ℝ × V → ℂ} (hU : Measurable U) (hW : Measurable W)
    {C D : ℝ} (hbU : ∀ r, ∀ᵐ w ∂μ, ‖U (r,w)‖≤C)
    (hbW : ∀ r, ∀ᵐ w ∂μ, ‖W (r,w)‖≤D) :
    sourceAngularHND d μ a v Ψ U W ≤
      (2:ℝ)^((d:ℝ)*(v-a))*(∫ r, |Ψ r|)*(C^2*μ.real univ)*(D^2*μ.real univ) := by
  rw [sourceAngularHND_normalized]
  let U' := fun p : ℝ × V => U ((2:ℝ)^v*p.1,p.2)
  let W' := fun p : ℝ × V => W ((2:ℝ)^v*p.1,p.2)
  have hu' : Measurable U' := hU.comp ((measurable_const.mul measurable_fst).prodMk measurable_snd)
  have hw' : Measurable W' := hW.comp ((measurable_const.mul measurable_fst).prodMk measurable_snd)
  have hi := graph_weighted_moments_integrableND μ hu' hw' (C := C) (D := D)
    (fun r => hbU ((2:ℝ)^v*r)) (fun r => hbW ((2:ℝ)^v*r)) hΨ
  have hi' : Integrable (fun r => |Ψ r| *(C^2*μ.real univ)*(D^2*μ.real univ)) :=
    (hΨ.abs.mul_const _).mul_const _
  have hp (r : ℝ) : Ψ r*sourceAngularMomentND μ U' r*sourceAngularMomentND μ W' r ≤
      |Ψ r| *(C^2*μ.real univ)*(D^2*μ.real univ) := by
    have h₁ := sourceAngularMomentND_nonneg μ U' r
    have h₂ := sourceAngularMomentND_nonneg μ W' r
    calc
      _ ≤ |Ψ r| *sourceAngularMomentND μ U' r*sourceAngularMomentND μ W' r := by
        gcongr
        exact le_abs_self _
      _ ≤ _ := by
        gcongr
        · exact sourceAngularMomentND_bound μ U' r (hbU ((2:ℝ)^v*r))
        · exact sourceAngularMomentND_bound μ W' r (hbW ((2:ℝ)^v*r))
  have hie := integral_mono hi hi' hp
  simp only [integral_mul_const] at hie
  have hm := mul_le_mul_of_nonneg_left hie (by positivity : 0≤(2:ℝ)^((d:ℝ)*(v-a)))
  simpa only [U',W',sourceAngularMomentND,mul_assoc] using hm
end Attempt4Near
end GraphLiteralSupport
end
end

end OAI
