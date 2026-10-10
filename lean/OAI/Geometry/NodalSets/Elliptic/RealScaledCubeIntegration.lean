import Mathlib.MeasureTheory.Function.Jacobian
import OAI.Geometry.NodalSets.Elliptic.RealCubeL2EmbeddingLemmas

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set Function Metric
noncomputable section

def realScaledCube (n : ℕ) (c : Fin n → ℝ) (r : ℝ) : Set (Fin n → ℝ) :=
  (fun x ↦ c+r • x) '' realFinCube n

lemma realScaledCube_isCompact (n : ℕ) (c : Fin n → ℝ) (r : ℝ) :
    IsCompact (realScaledCube n c r) :=
  (realFinCube_isCompact n).image (continuous_const.add (continuous_id.const_smul r))

lemma realScaledCube_integral (n : ℕ) (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (F : (Fin n → ℝ) → ℝ) :
    (∫ y in realScaledCube n c r, F y) = r^n*(∫ x in realFinCube n, F (c+r • x)) := by
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := r • ContinuousLinearMap.id ℝ (Fin n → ℝ)
  have hd (x : Fin n → ℝ) : HasFDerivAt (fun y ↦ c+r • y) L x :=
    L.hasFDerivAt.const_add c
  have hi : Injective (fun x : Fin n → ℝ ↦ c+r • x) := by
    intro x y h
    exact (smul_right_injective (Fin n → ℝ) hr.ne') (add_left_cancel h)
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume
    (realFinCube_isCompact n).measurableSet (fun x _ ↦ (hd x).hasFDerivWithinAt) hi.injOn F
  have hdet : |L.det|=r^n := by
    simp [L,ContinuousLinearMap.det,LinearMap.det_smul,abs_of_pos hr]
  simpa only [realScaledCube,hdet,smul_eq_mul,integral_const_mul] using h

lemma realScaledCube_eq_closedBall (n : ℕ) (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    realScaledCube n c r = closedBall c r := by
  have hunit : realFinCube n = closedBall (0 : Fin n → ℝ) 1 := by
    rw [closedBall_pi _ (by norm_num : (0:ℝ) ≤ 1)]
    simp [realFinCube,Real.closedBall_eq_Icc]
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    rw [hunit,mem_closedBall,dist_zero_right] at hx
    rw [mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,
      Real.norm_eq_abs,abs_of_pos hr]
    nlinarith
  · intro hy
    refine ⟨r⁻¹ • (y-c),?_,?_⟩
    · rw [hunit,mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hr)]
      have h : ‖y-c‖ ≤ r := by simpa only [mem_closedBall,dist_eq_norm] using hy
      exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hr.le)).trans_eq
        (inv_mul_cancel₀ hr.ne')
    · dsimp
      rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul,add_sub_cancel]

lemma realScaledCube_mass (n : ℕ) (c : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    (volume.restrict (realScaledCube n c r)).real univ = (2*r)^n := by
  have h := realScaledCube_integral n c hr (fun _ ↦ (1:ℝ))
  simpa only [integral_const,smul_eq_mul,mul_one,one_mul,realFinCube_mass,mul_pow,mul_comm] using h

end
end Yau.Geometry

end OAI
