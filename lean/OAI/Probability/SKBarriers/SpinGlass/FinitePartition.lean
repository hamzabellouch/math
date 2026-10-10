import Mathlib
import OAI.Probability.SKBarriers.Gaussian.LogDerivatives

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
namespace SK.Analytic
section FinitePartition
variable {E S : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype S] [Nonempty S]

def affineLogPartition (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (x : E) : ℝ :=
  Real.log (∑ s, Real.exp (c s+L s x))

theorem affineLogPartition_convex (c : S → ℝ) (L : S → E →L[ℝ] ℝ) :
    ConvexOn ℝ univ (affineLogPartition c L) := by
  let : MeasurableSpace S := ⊤
  have hc : ∀ s, ConvexOn ℝ univ (fun x => c s+L s x) := by
    intro s
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    simp only [map_add, map_smul, smul_eq_mul]
    nlinarith [congrArg (fun t : ℝ => t * c s) hab]
  have h := convexOn_log_integral_exp (Measure.count : Measure S)
    (fun x s => c s+L s x) (fun _ => Integrable.of_finite) hc
  change ConvexOn ℝ univ (fun x => Real.log (∑ s, Real.exp (c s+L s x)))
  simpa only [integral_count] using h

theorem affineLogPartition_boundedDerivs (c : S → ℝ) (L : S → E →L[ℝ] ℝ) :
    BoundedDerivs (affineLogPartition c L) := by
  classical
  let Z : E → ℝ := fun x => ∑ s, Real.exp (c s+L s x)
  let Z₁ : E → E →L[ℝ] ℝ := fun x => ∑ s, Real.exp (c s+L s x) • L s
  let Z₂ : E → E →L[ℝ] E →L[ℝ] ℝ := fun x =>
    ∑ s, (Real.exp (c s+L s x) • L s).smulRight (L s)
  have hd (s : S) (x : E) : HasFDerivAt (fun x => c s+L s x) (L s) x := by
    simpa only [zero_add] using (hasFDerivAt_const (c s) x).fun_add (L s).hasFDerivAt
  have hz₁ (x : E) : HasFDerivAt Z (Z₁ x) x := by
    exact HasFDerivAt.fun_sum (fun s _ => (hd s x).exp)
  have hz₂ (x : E) : HasFDerivAt Z₁ (Z₂ x) x := by
    exact HasFDerivAt.fun_sum (fun s _ => (hd s x).exp.smul_const (L s))
  have he : fderiv ℝ Z = Z₁ := funext (fun x => (hz₁ x).fderiv)
  have he₂ : fderiv ℝ (fderiv ℝ Z) = Z₂ := by
    rw [he]
    exact funext (fun x => (hz₂ x).fderiv)
  have hc : ContDiff ℝ 2 Z := by
    apply ContDiff.sum
    intro s _
    exact (contDiff_const.add (L s).contDiff).exp
  have hp (x : E) : 0 < Z x := Finset.sum_pos (fun s _ => Real.exp_pos _) Finset.univ_nonempty
  let C : ℝ := ∑ s, ‖L s‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun s _ => norm_nonneg _
  have hL (s : S) : ‖L s‖ ≤ C := Finset.single_le_sum (fun t _ => norm_nonneg (L t)) (Finset.mem_univ s)
  change BoundedDerivs (fun x => Real.log (Z x))
  apply log_boundedDerivs_of_relative_bounds Z hc hp hC (mul_nonneg hC hC)
  · intro x
    rw [he]
    apply (norm_sum_le _ _).trans
    change (∑ s, ‖Real.exp (c s+L s x) • L s‖) ≤ C*∑ s, Real.exp (c s+L s x)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (hL s) (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  · intro x
    rw [he₂]
    apply (norm_sum_le Finset.univ (fun s : S =>
      (Real.exp (c s+L s x) • L s).smulRight (L s))).trans
    change (∑ s, ‖(Real.exp (c s+L s x) • L s).smulRight (L s)‖) ≤
      (C*C)*∑ s, Real.exp (c s+L s x)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (Real.exp (c s+L s x)*C)*C := by gcongr <;> exact hL s
      _ = _ := by ring

end FinitePartition
end SK.Analytic

end
end
end
end
end
end

end OAI
