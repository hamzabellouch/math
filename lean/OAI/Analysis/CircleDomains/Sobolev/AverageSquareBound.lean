import OAI.Analysis.CircleDomains.Modulus.AverageOscillation

namespace OAI

/-! The square of a real average is bounded by the average of the square. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma sq_average_le_average_sq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] [NeZero μ] {g : X → ℝ} (hg : Integrable g μ)
    (hg2 : Integrable (fun x => g x^2) μ) :
    (⨍ x, g x ∂μ)^2 ≤ ⨍ x, g x^2 ∂μ := by
  let a := ⨍ x, g x ∂μ
  have hp : (fun x => (g x-a)^2) = (fun x => g x^2-(2*a)*g x+a^2) := by
    funext x
    ring
  have hn : 0 ≤ (⨍ x, (g x-a)^2 ∂μ) := average_nonneg (fun x => sq_nonneg (g x-a))
  have he1 := average_add (hg2.sub (hg.const_mul (2*a)))
    (integrable_const (a^2) : Integrable (fun _ : X => a^2) μ)
  have he2 := average_sub hg2 (hg.const_mul (2*a))
  simp only [Pi.add_apply, Pi.sub_apply] at he1 he2
  rw [hp, he1, he2, average_const_mul, average_const] at hn
  dsimp only [a] at hn
  nlinarith

end CircleDomainRigidity

end

end OAI
