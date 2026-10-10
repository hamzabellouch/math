import Mathlib
import OAI.Probability.SKBarriers.Calculus.ParameterSpace
import OAI.Probability.SKBarriers.Scalar.ThermalMoments

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section
variable {E S : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype S] [Nonempty S]

omit [Nonempty S] in
theorem affineMoment_const_mul (c : S → ℝ) (U : S → E →L[ℝ] ℝ)
    (g : S → ℝ) (a : ℝ) :
    affineMoment c U (fun s => a*g s) = fun x => a*affineMoment c U g x := by
  funext x
  simp only [affineMoment,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem affineMoment_contDiff (c : S → ℝ) (U : S → E →L[ℝ] ℝ) (g : S → ℝ) :
    ContDiff ℝ 1 (affineMoment c U g) := by
  unfold affineMoment affineGibbs
  apply ContDiff.sum
  intro s _
  exact (((contDiff_const.add (U s).contDiff).exp).div
    (ContDiff.sum (fun t _ => (contDiff_const.add (U t).contDiff).exp))
    (fun x => (affinePartition_pos c U x).ne')).mul contDiff_const

theorem fderiv_affineMoment_apply (c : S → ℝ) (U : S → E →L[ℝ] ℝ)
    (g : S → ℝ) (x u : E) :
    fderiv ℝ (affineMoment c U g) x u =
      affineMoment c U (fun s => g s*U s u) x -
        affineMoment c U g x*affineMoment c U (fun s => U s u) x := by
  classical
  let Z : E → ℝ := fun x => ∑ s, Real.exp (c s+U s x)
  let K : E → ℝ := fun x => ∑ s, Real.exp (c s+U s x)*g s
  have hz : HasFDerivAt Z (∑ s, Real.exp (c s+U s x) • U s) x := by
    apply HasFDerivAt.fun_sum
    intro s _
    simpa only [zero_add] using ((hasFDerivAt_const (c s) x).fun_add (U s).hasFDerivAt).exp
  have hk : HasFDerivAt K (∑ s, g s • (Real.exp (c s+U s x) • U s)) x := by
    apply HasFDerivAt.fun_sum
    intro s _
    simpa only [zero_add] using (((hasFDerivAt_const (c s) x).fun_add (U s).hasFDerivAt).exp).mul_const (g s)
  have he : affineMoment c U g = fun x => K x / Z x := by
    ext x
    simp only [affineMoment,affineGibbs,K,Z,Finset.sum_div,mul_div_assoc]
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hi : HasFDerivAt (fun y => (Z y)⁻¹)
      (-(Z x ^ 2)⁻¹ • (∑ s, Real.exp (c s+U s x) • U s)) x := by
    convert (hasDerivAt_inv (affinePartition_pos c U x).ne').comp_hasFDerivAt x hz using 1
    all_goals rfl
  have hq := hk.fun_mul hi
  rw [he]
  simp only [div_eq_mul_inv]
  rw [hq.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,sum_apply]
  have hZ : Z x ≠ 0 := (affinePartition_pos c U x).ne'
  have h1 : affineMoment c U (fun s => g s*U s u) x =
      (∑ s, g s*(Real.exp (c s+U s x)*U s u))/Z x := by
    simp only [affineMoment,affineGibbs,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s _
    change _ = _ / Z x
    dsimp only [Z]
    ring
  have h2 : affineMoment c U (fun s => U s u) x =
      (∑ s, Real.exp (c s+U s x)*U s u)/Z x := by
    simp only [affineMoment,affineGibbs,Z,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [h1,h2]
  change _ = _ - K x / Z x * _
  field_simp
  ring

theorem affineMoment_fderiv_bounded (c : S → ℝ) (U : S → E →L[ℝ] ℝ)
    (g : S → ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖fderiv ℝ (affineMoment c U g) x‖ ≤ C := by
  classical
  let B := ∑ s, ‖g s‖
  let M := ∑ s, ‖U s‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hb (s : S) : ‖g s‖ ≤ B := Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ s)
  have hm (s : S) : ‖U s‖ ≤ M := Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ s)
  refine ⟨2*B*M,by positivity,fun x => ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun u => ?_)⟩
  rw [fderiv_affineMoment_apply]
  have Hu : ∀ s, ‖U s u‖ ≤ M*‖u‖ := fun s =>
    ((U s).le_opNorm u).trans (mul_le_mul_of_nonneg_right (hm s) (norm_nonneg _))
  have HgU : ∀ s, ‖g s*U s u‖ ≤ B*(M*‖u‖) := fun s => by
    rw [norm_mul]
    exact mul_le_mul (hb s) (Hu s) (norm_nonneg _) hB
  calc
    _ ≤ ‖affineMoment c U (fun s => g s*U s u) x‖ +
        ‖affineMoment c U g x*affineMoment c U (fun s => U s u) x‖ := norm_sub_le _ _
    _ ≤ B*(M*‖u‖)+B*(M*‖u‖) := add_le_add (affineMoment_norm_le c U _ HgU x)
      (by
        rw [norm_mul]
        exact mul_le_mul (affineMoment_norm_le c U g hb x)
          (affineMoment_norm_le c U _ Hu x) (norm_nonneg _) hB)
    _ = _ := by ring

end
end SK.Analytic

end
end

end OAI
