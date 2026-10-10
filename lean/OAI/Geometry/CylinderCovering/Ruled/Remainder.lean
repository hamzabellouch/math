import OAI.Geometry.CylinderCovering.Ruled.LogarithmicLocalDefinitions
import OAI.Geometry.CylinderCovering.Ruled.LocalEndpoint
import OAI.Geometry.CylinderCovering.Convexity.QuadraticTaylorBound

namespace OAI

noncomputable section
open Set Metric
namespace CylinderCovering.ProductLocal
open RuledApproximation

lemma euclidean_pair_norm_le_twice (e : ℝ × ℝ) :
    ‖vec2 e.1 e.2‖ ≤ 2*‖e‖ := by
  have h1 : |e.1| ≤ ‖e‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le e
  have h2 : |e.2| ≤ ‖e‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le e
  have h := plane_norm_le_sum (vec2 e.1 e.2)
  simp only [vec2_apply_zero, vec2_apply_one] at h
  linarith

theorem logarithmic_remainder_proof : LogarithmicRemainderStatement := by
  intro X k D v hX hk hD hv hH m hm
  obtain ⟨a,b,_,hDU,hv2⟩ := hv
  let U : Set Plane := {p | ∀ i, p i ∈ Ioo (a i) (b i)}
  have hU : IsOpen U := by
    have he : U = ⋂ i : Fin 2, (fun p : Plane => p i) ⁻¹' Ioo (a i) (b i) := by
      ext p; simp [U]
    rw [he]
    exact isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (by fun_prop))
  have hv1 : ContDiffOn ℝ 1 v U := hv2.of_le (by norm_num)
  have hder : ContinuousOn (fderiv ℝ v) D := by
    intro p hp
    exact ((hv1.contDiffAt (hU.mem_nhds (hDU hp))).continuousAt_fderiv
      (by norm_num)).continuousWithinAt
  obtain ⟨N,hN,hNall⟩ := compact_uniform_eigenframe_inverse hD hder
    (fun p hp => (hH p hp).1) (fun p hp => (hH p hp).2)
  obtain ⟨r,C,hr,hC,hrem⟩ := QuadraticTaylor.exists_uniform_taylor_norm_bound_near
    hD ⟨U,hU,hDU,hv2⟩
  have hm0 : 0 < m := lt_trans zero_lt_one hm
  refine ⟨r/(2*m),8*N*X*k*C*m^2,by positivity,by positivity,?_⟩
  intro p hp lam L hlam hL t ht htr s hs x hx
  let q := p+t • L s
  have hqdist : ‖q-p‖ ≤ 2*m*t := by
    have hf : ‖L s‖ ≤ 2*m := (frame_norm_le hL s).trans (by linarith [hs.1,hs.2.1])
    calc ‖q-p‖ = t*‖L s‖ := by
          simp only [q,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
      _ ≤ t*(2*m) := mul_le_mul_of_nonneg_left hf ht.le
      _ = 2*m*t := by ring
  have hqr : ‖q-p‖ ≤ r := by
    have ht2 := (lt_div_iff₀ (by positivity : 0 < 2*m)).mp htr
    linarith
  let w := v q-v p-fderiv ℝ v p (q-p)
  have hw : ‖w‖ ≤ C*(2*m*t)^2 := by
    exact (hrem p hp q hqr).trans
      (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hqdist) hC.le)
  let e : ℝ × ℝ := ((x*k)/t) • L.symm w
  have he : ‖e‖ ≤ (4*N*X*k*C*m^2)*t := by
    calc ‖e‖ = ((|x| * k)/t) * ‖L.symm w‖ := by
          simp only [e,norm_smul,Real.norm_eq_abs,abs_div,abs_mul,abs_of_pos hk,abs_of_pos ht]
      _ ≤ ((X*k)/t) * (N*(C*(2*m*t)^2)) := by
          gcongr
          exact (hNall p hp lam L hlam hL).2 w |>.trans
            (mul_le_mul_of_nonneg_left hw hN.le)
      _ = (4*N*X*k*C*m^2)*t := by field_simp; ring
  refine ⟨e,?_,?_⟩
  · exact intercept_identity v p t (x*k) lam L hL ht.ne' s
  · calc ‖vec2 e.1 e.2‖ ≤ 2*‖e‖ := euclidean_pair_norm_le_twice e
         _ ≤ 2*((4*N*X*k*C*m^2)*t) := mul_le_mul_of_nonneg_left he (by norm_num)
         _ = (8*N*X*k*C*m^2)*t := by ring

end CylinderCovering.ProductLocal

end

end OAI
