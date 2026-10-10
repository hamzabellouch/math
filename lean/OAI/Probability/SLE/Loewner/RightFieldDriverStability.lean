import OAI.Probability.SLE.NearRealContraction

namespace OAI

/-! Stability of the clipped right-half-plane flow under perturbations of
the driver. This also applies arbitrarily close to the real boundary. -/
noncomputable section
open Set Filter Complex Metric
open scoped Topology NNReal

namespace SLEExactGauge

lemma rightCenter_driver_dist (a u v : ℝ) (z : ℂ) :
    dist (rightCenter a u z) (rightCenter a v z) ≤ |u-v| := by
  have he : rightCenter a u z-rightCenter a v z =
      ((max a (z.re-u)-max a (z.re-v) : ℝ) : ℂ) := by
    simp only [rightCenter,Complex.ofReal_sub]
    ring
  rw [dist_eq_norm,he,Complex.norm_real,Real.norm_eq_abs]
  have hh := ((LipschitzWith.id : LipschitzWith 1 (fun x : ℝ => x)).const_max a).dist_le_mul
    (z.re-u) (z.re-v)
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul,id_eq,sub_sub_sub_cancel_left,
    abs_sub_comm v u] using hh

lemma rightField_driver_dist {a : ℝ} (ha : 0 < a) (u v : ℝ) (z : ℂ) :
    dist (rightField a u z) (rightField a v z) ≤ 2*a⁻¹^2*|u-v| := by
  have hu : ‖(rightCenter a u z)⁻¹‖ ≤ a⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ ha (rightCenter_norm a u z)
  have hv : ‖(rightCenter a v z)⁻¹‖ ≤ a⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ ha (rightCenter_norm a v z)
  rw [dist_eq_norm,rightField,rightField,← mul_sub,norm_mul,norm_ofNat,
    inv_sub_inv' (rightCenter_ne_zero ha _ _) (rightCenter_ne_zero ha _ _),
    norm_mul,norm_mul]
  calc
    _ ≤ 2*(a⁻¹*|u-v| * a⁻¹) := by
      gcongr
      simpa only [← dist_eq_norm,dist_comm] using rightCenter_driver_dist a u v z
    _ = _ := by ring

lemma right_flow_driver_distance {a : ℝ} (ha : 0 < a)
    (U V : ℝ → ℝ) (Z Q : ℝ → ℂ) (T : ℝ) (_hT : 0 ≤ T)
    (hZ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Z
      (rightField a (U t) (Z t)) (Icc 0 T) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Q
      (rightField a (V t) (Q t)) (Icc 0 T) t)
    (δ : ℝ) (hinit : dist (Z 0) (Q 0) ≤ δ)
    (hUV : ∀ t ∈ Icc 0 T, |U t-V t| ≤ δ) :
    ∀ t ∈ Icc 0 T, dist (Z t) (Q t) ≤
      gronwallBound δ (4*a⁻¹^2) (2*a⁻¹^2*δ) t := by
  intro t ht
  have he := dist_le_of_approx_trajectories_ODE
    (K := (⟨4*a⁻¹^2,by positivity⟩ : ℝ≥0))
    (v := fun s => rightField a (U s)) (fun _ => rightField_lipschitz ha _)
    (f := Z) (fun s hs => (hZ s hs).continuousWithinAt)
    (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hZ s ⟨hs.1,hs.2.le⟩))
    (εf := 0) (fun _ _ => by simp)
    (g := Q) (fun s hs => (hQ s hs).continuousWithinAt)
    (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hQ s ⟨hs.1,hs.2.le⟩))
    (εg := 2*a⁻¹^2*δ) (fun s hs => ?_) hinit t ht
  · change dist (Z t) (Q t) ≤ gronwallBound δ (4*a⁻¹^2) (0+2*a⁻¹^2*δ) (t-0) at he
    simpa only [zero_add,sub_zero] using he
  · rw [dist_comm]
    exact (rightField_driver_dist ha _ _ _).trans
      (mul_le_mul_of_nonneg_left (hUV s (Ico_subset_Icc_self hs)) (by positivity))

end SLEExactGauge

end

end OAI
