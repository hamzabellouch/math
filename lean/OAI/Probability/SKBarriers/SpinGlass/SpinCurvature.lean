import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.CascadeRecursion
import OAI.Probability.SKBarriers.Scalar.ThermalMoments

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
section SpinCurvature
variable {E S : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype S] [Nonempty S]

theorem cascadeAffine_gradient (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (L : S → CascadeSpace E n →L[ℝ] ℝ) (x u : E) :
    fderiv ℝ (cascadePressure n m (affineLogPartition c L)) x u =
      cascadeMoment n m (affineLogPartition c L)
        (affineMoment c L (fun s => L s (cascadeLift n u))) x := by
  rw [cascadePressure_gradient n m _ (affineLogPartition_boundedDerivs c L)]
  simp_rw [fderiv_affineLogPartition_apply]

theorem cascadeAffine_curvature (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (L : S → CascadeSpace E n →L[ℝ] ℝ) {lower : ℝ}
    (hl : lower ≤ 1) (hm : ∀ i, lower ≤ m i) (hmu : ∀ i, m i ≤ 1)
    (hmono : Monotone m) (x u : E) :
    let f := affineLogPartition c L
    let M := cascadeMoment n m f (affineMoment c L (fun s => L s (cascadeLift n u))) x
    let A := cascadeMoment n m f (affineMoment c L (fun s => (L s (cascadeLift n u))^2)) x
    0 ≤ A-M^2 ∧ lower*(A-M^2) ≤ fderiv ℝ (fderiv ℝ (cascadePressure n m f)) x u u := by
  classical
  let g : S → ℝ := fun s => L s (cascadeLift n u)
  let C : ℝ := ∑ s, (g s)^2
  have hC : 0 ≤ C := Finset.sum_nonneg (fun s _ => sq_nonneg _)
  have hg (s : S) : ‖(g s)^2‖ ≤ C := by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum (fun t _ => sq_nonneg (g t)) (Finset.mem_univ s)
  have H := cascade_curvature_domination n m (affineLogPartition c L)
    (affineLogPartition_boundedDerivs c L) (affineMoment c L (fun s => (g s)^2))
    (affineMoment_continuous c L _) hC (affineMoment_norm_le c L _ hg) hl hm hmu hmono u
    (fun z => by rw [fderiv_affineLogPartition_apply]; exact affineMoment_variance_nonneg c L g z)
    (fun z => by
      rw [fderiv_fderiv_affineLogPartition_apply,fderiv_affineLogPartition_apply]
      simp only [one_mul,pow_two,g]
      exact le_rfl) x
  rw [cascadeAffine_gradient] at H
  exact H

end SpinCurvature
end SK.Analytic

end
end
end
end
end
end
end

end OAI
