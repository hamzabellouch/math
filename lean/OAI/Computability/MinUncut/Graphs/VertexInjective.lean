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
namespace MinUncut.CubeRows
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] [Nonempty A]

omit [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] [Nonempty A] in
lemma vertex_injective (x y : ι → A) (hxy : ∀ i, x i≠y i) :
    Function.Injective (fun ν : ι → Bool => vertex ν x y) := by
  intro ν ω he
  funext i
  exact bool_choice_injective (hxy i) (congrFun he i)

omit [DecidableEq A] [Nonempty A] in
lemma independent_points (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (V : (ι → A) → ℝ → ℝ) (hV : ∀ x, Measurable (V x))
    (x y : ι → A) (hxy : ∀ i, x i≠y i) :
    (∫ c, ∏ ν : ι → Bool, V (vertex ν x y) (c (vertex ν x y)) ∂Measure.pi (fun _ : ι → A => μ)) =
      ∏ ν : ι → Bool, ∫ t, V (vertex ν x y) t ∂μ := by
  have hi := (iIndepFun_pi (μ := fun _ : ι → A => μ) (X := fun z t => V z t)
    (fun z => (hV z).aemeasurable)).precomp (vertex_injective x y hxy)
  rw [hi.integral_fun_prod_eq_prod_integral (fun ν => ((hV _).comp (measurable_pi_apply _)).aestronglyMeasurable)]
  apply Finset.prod_congr rfl
  intro ν _
  have hh := integral_map (μ := Measure.pi (fun _ : ι → A => μ))
    (measurable_pi_apply (vertex ν x y)).aemeasurable (hV (vertex ν x y)).aestronglyMeasurable
  rw [(measurePreserving_eval (fun _ : ι → A => μ) (vertex ν x y)).map_eq] at hh
  exact hh.symm

omit [DecidableEq A] [Nonempty A] in
lemma centered_point_cube_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (V : (ι → A) → ℝ → ℝ) (hV : ∀ x, Measurable (V x))
    (hmean : ∀ x, (∫ t, V x t ∂μ)=0) (x y : ι → A) (hxy : ∀ i, x i≠y i) :
    (∫ c, ∏ ν : ι → Bool, V (vertex ν x y) (c (vertex ν x y)) ∂Measure.pi (fun _ : ι → A => μ))=0 := by
  rw [independent_points μ V hV x y hxy]
  apply Finset.prod_eq_zero (Finset.mem_univ (fun _ => false))
  exact hmean _
end MinUncut.CubeRows

end

end OAI
