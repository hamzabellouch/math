import OAI.Probability.ContinuumTransition.Regroup

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma three_vertex_support {p : ℝ} (hp : 0 < p) (i : Fin 3) :
    SupportOn pressureDomain (threeMeanField p (firstMass p)) initialPoint (triangleVertex p i) := by
  intro y hy
  rw [threeMeanField_initial hp]
  have hap := firstMass_mul hp
  have hap2 : firstMass p*p^2=3*p/2 := by linear_combination p*hap
  have hap2y := congrArg (fun z : ℝ => y.1*z) hap2
  have h0 : 0 ≤ threeMeanField p (firstMass p) y := le_max_left _ _
  have h1 : p*y.2+y.1*firstMass p*p^2/2 ≤ threeMeanField p (firstMass p) y :=
    (le_max_left _ _).trans (le_max_right _ _)
  have h2 : 4*p*y.2-9*p+y.1*firstMass p*(4*p)^2/2 ≤ threeMeanField p (firstMass p) y :=
    (le_max_right _ _).trans (le_max_right _ _)
  fin_cases i <;> norm_num [triangleVertex,initialPoint,pDot,show (2:Fin 3) ≠ 0 by decide,show (2:Fin 3) ≠ 1 by decide]
  · exact h0
  · nlinarith only [h1,hap2y]
  · nlinarith only [h2,hap2y]

lemma three_support_contains_triangle {p : ℝ} (hp : 0 < p) :
    convexHull ℝ (range (triangleVertex p)) ⊆ subgradients pressureDomain (threeMeanField p (firstMass p)) initialPoint :=
  convexHull_min (range_subset_iff.mpr (three_vertex_support hp)) (subgradients_convex _ _ _)

end ContinuumTemperature
end
end

end OAI
