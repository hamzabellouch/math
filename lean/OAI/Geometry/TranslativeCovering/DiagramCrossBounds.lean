import OAI.Geometry.TranslativeCovering.MatchingBounds

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2 u_3

namespace PoissonDiagrams
open MeasureTheory CellMatching MatchingBounds
open scoped Classical BigOperators
variable {Ω : Type u_1} {I : Type u_2} {J : Type u_3} [MeasurableSpace Ω] [Fintype I] [Fintype J]

lemma cross_bound (μ : Measure Ω) (E : I → Set Ω) (F : J → Set Ω) :
    diagram μ E F ≤ (∏ i, μ.real (E i))*(∏ j, μ.real (F j)) *
      (Real.exp (∑ i, ∑ j, μ.real (E i ∩ F j)/(μ.real (E i)*μ.real (F j))) - 1) := by
  unfold diagram
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Fintype.sum_prod_type] using cross_matching_bound
    (fun e : I × J => μ.real (E e.1 ∩ F e.2)/(μ.real (E e.1)*μ.real (F e.2)))
    (fun e => by positivity)

end PoissonDiagrams

end OAI
