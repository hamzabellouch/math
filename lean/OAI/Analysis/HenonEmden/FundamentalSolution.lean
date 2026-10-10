import OAI.Analysis.HenonEmden.NewtonBounds

namespace OAI

universe uE

section FundamentalSolution

open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open Set Filter Topology
open scoped ContDiff
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
open Set Filter Topology MeasureTheory
open Set Filter Topology
open MeasureTheory
open scoped Convolution
open Set Filter Topology
open MeasureTheory Set Filter Topology
open scoped ContDiff
noncomputable section


namespace HenonLaneEmden.WeakPDE
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
open SphereCalculus

omit [Nontrivial E] in
lemma locallyIntegrable_newtonKernel (hn : 1 ≤ Module.finrank ℝ E) :
    LocallyIntegrable (fun x : E => ‖x‖^(2-(Module.finrank ℝ E:ℝ))) := by
  apply locallyIntegrable_of_norm_le_rpow hn (α := (Module.finrank ℝ E:ℝ)-2) (C := 1)
    (by linarith) _ (measurable_norm.pow_const _).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _),one_mul]
  rw [show -((Module.finrank ℝ E:ℝ)-2) = 2-(Module.finrank ℝ E:ℝ) by ring]

lemma kernel_integral_polar (hn : 3 ≤ Module.finrank ℝ E) {w : E → ℝ}
    (hw : Continuous w) (hwc : HasCompactSupport w) :
    (∫ x : E, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*w x) = ∫ r in Ioi (0:ℝ), r*mean w r := by
  have hi := (locallyIntegrable_newtonKernel (by omega : 1 ≤ Module.finrank ℝ E)).integrable_smul_right_of_hasCompactSupport hw hwc
  change Integrable (fun x : E => ‖x‖^(2-(Module.finrank ℝ E:ℝ))*w x) volume at hi
  rw [Polar.integral_polar volume _ hi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  simp_rw [norm_smul_sphere hr.le,integral_const_mul]
  change r^(Module.finrank ℝ E-1)*(r^(2-(Module.finrank ℝ E:ℝ))*mean w r) = r*mean w r
  rw [← mul_assoc]
  congr 1
  rw [← Real.rpow_natCast,← Real.rpow_add hr]
  have hc : ((Module.finrank ℝ E-1:ℕ):ℝ)+(2-(Module.finrank ℝ E:ℝ)) = 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ Module.finrank ℝ E),Nat.cast_one]
    ring
  rw [hc,Real.rpow_one]

lemma mean_ode_global (hn : 2 ≤ Module.finrank ℝ E) {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    {r : ℝ} (hr : 0 < r) :
    r*meanDD φ r+((Module.finrank ℝ E:ℝ)-1)*meanD φ r = r*mean (Laplacian.laplacian φ) r := by
  have h := mean_laplacian_ode hφ.contDiffOn (continuous_laplacian hφ).continuousOn
    (fun _ _ => rfl) hr
  have hp : r^(Module.finrank ℝ E-1) = r^(Module.finrank ℝ E-2)*r := by
    rw [show Module.finrank ℝ E-1 = Module.finrank ℝ E-2+1 by omega,pow_succ]
  rw [hp,Nat.cast_sub (by omega : 1 ≤ Module.finrank ℝ E),Nat.cast_one] at h
  apply mul_left_cancel₀ (pow_ne_zero (Module.finrank ℝ E-2) hr.ne')
  nlinarith [h]

omit [Nontrivial E] in
lemma mean_at_large_zero {φ : E → ℝ} {R : ℝ}
    (hR : 0 < R) (hbound : ∀ x ∈ tsupport φ, ‖x‖ < R) {r : ℝ} (hr : R ≤ r) :
    mean φ r = 0 ∧ meanD φ r = 0 ∧ mean (Laplacian.laplacian φ) r = 0 := by
  have hs (θ : UnitSphere E) : r • (θ:E) ∉ tsupport φ := by
    intro hx
    have hh := hbound _ hx
    rw [norm_smul_sphere (hR.le.trans hr)] at hh
    linarith
  refine ⟨?_,?_,?_⟩
  · unfold mean
    have he : (fun θ : UnitSphere E => φ (r • (θ:E))) = 0 := by
      ext θ
      exact image_eq_zero_of_notMem_tsupport (hs θ)
    rw [he]
    exact integral_zero _ _
  · unfold meanD
    simp_rw [fderiv_of_notMem_tsupport ℝ (hs _),_root_.zero_apply]
    exact integral_zero _ _
  · unfold mean
    simp_rw [laplacian_zero_of_notMem_tsupport (hs _)]
    exact integral_zero _ _

lemma integral_kernel_laplacian (hn : 3 ≤ Module.finrank ℝ E) {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    (∫ x : E, ‖x‖^(2-(Module.finrank ℝ E:ℝ))*Laplacian.laplacian φ x) =
      -((Module.finrank ℝ E:ℝ)-2)*((volume : Measure E).toSphere univ).toReal*φ 0 := by
  obtain ⟨R,hR,hbound⟩ := hφc.isBounded.exists_pos_norm_lt
  rw [kernel_integral_polar hn (continuous_laplacian hφ) (compactSupport_laplacian hφc)]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self (s := Ioc 0 R)
    (fun r hr => by
      have hRr : R ≤ r := le_of_not_gt (fun h => hr.2 ⟨hr.1,h.le⟩)
      rw [(mean_at_large_zero hR hbound hRr).2.2,mul_zero])]
  rw [← intervalIntegral.integral_of_le hR.le]
  let H (r : ℝ) := r*meanD φ r+((Module.finrank ℝ E:ℝ)-2)*mean φ r
  have hH : Continuous H := (continuous_id.mul (continuous_meanD_global hφ)).add ((continuous_mean hφ.continuous).const_mul _)
  have hHd (r : ℝ) (hr : r ∈ Ioo 0 R) : HasDerivAt H (r*mean (Laplacian.laplacian φ) r) r := by
    convert! (((hasDerivAt_id r).mul (hasDerivAt_meanD hφ.contDiffOn hr.1)).add
      ((hasDerivAt_mean hφ.contDiffOn hr.1).const_mul ((Module.finrank ℝ E:ℝ)-2))) using 1
    simp only [id_eq,one_mul]
    nlinarith [mean_ode_global (by omega) hφ hr.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR.le hH.continuousOn hHd
    ((continuous_id.mul (continuous_mean (continuous_laplacian hφ))).intervalIntegrable _ _)]
  obtain ⟨h0,h1,_⟩ := mean_at_large_zero hR hbound le_rfl
  dsimp [H]
  rw [h0,h1,mean_zero]
  ring
end HenonLaneEmden.WeakPDE

end
end FundamentalSolution

end OAI
