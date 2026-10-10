import Mathlib
import OAI.Computability.MinUncut.Estimates.FaceUpdateSelf

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Slice
open BinaryFourier
open scoped BigOperators
variable {W : Type*} [Fintype W] [AddCommGroup W] [Module F₂ W]
local instance oddMaxTranslateDualFintype : Fintype (Module.Dual F₂ W) := BinaryFourier.dualFintype

lemma oddMax_translate (one : W) (v : W → ℝ) (a : W) :
    oddMax one (fun b => v (a+b))=oddMax one v := by
  unfold oddMax
  congr 1
  funext α
  rw [coefficient_translate, abs_mul, character_abs, one_mul]

lemma processed_translate (H γ A : ℝ) (one : W) (v : W → ℝ) (a b : W) :
    processed H γ A one (fun t => v (a+t)) b=processed H γ A one v (a+b) := by
  unfold processed
  rw [expect_translate (fun t => (v t)^2) a, oddMax_translate]
end MinUncut.Slice

end

end OAI
