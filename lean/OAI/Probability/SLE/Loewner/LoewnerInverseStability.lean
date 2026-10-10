import OAI.Probability.SLE.Loewner.LoewnerDriverBounds

namespace OAI

/-! Uniform perturbation estimates for inverse maps above a positive height.
They require no regularity of a boundary trace beyond the capacity witness. -/
noncomputable section
open Set Filter Complex
open scoped Topology NNReal

namespace SLEExactGauge

lemma reverseField_driver_dist {a : ℝ} (ha : 0 < a) (u v : ℝ) (z : ℂ) :
    dist (reverseField a u z) (reverseField a v z) ≤ 2 * a⁻¹ ^ 2 * |u-v| := by
  have hc : reverseCenter a v z - reverseCenter a u z = ((u-v : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [reverseCenter]
  have hu : ‖(reverseCenter a u z)⁻¹‖ ≤ a⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ ha (reverseCenter_norm a u z)
  have hv : ‖(reverseCenter a v z)⁻¹‖ ≤ a⁻¹ := by
    rw [norm_inv]
    exact inv_anti₀ ha (reverseCenter_norm a v z)
  rw [dist_eq_norm,reverseField,reverseField,← mul_sub,norm_mul,norm_neg,norm_ofNat,
    inv_sub_inv' (reverseCenter_ne_zero ha _ _) (reverseCenter_ne_zero ha _ _),
    norm_mul,norm_mul,hc,Complex.norm_real,Real.norm_eq_abs]
  calc
    2 * (‖(reverseCenter a u z)⁻¹‖ * |u-v| * ‖(reverseCenter a v z)⁻¹‖) ≤
        2 * (a⁻¹ * |u-v| * a⁻¹) := by gcongr
    _ = _ := by ring

lemma IsCapacityTwoWitness.inverse_approximation_bound
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) {a : ℝ} (ha : 0 < a)
    (w : ℂ) (haw : a ≤ w.im) (V : ℝ≥0 → ℝ) (δ : ℝ)
    (hUV : ∀ t ∈ Icc 0 T, |U t-V t| ≤ δ)
    (Q : ℝ → ℂ) (hQ0 : Q 0=w)
    (hQ : ∀ s ∈ Icc 0 (T : ℝ), HasDerivWithinAt Q
      (reverseField a (V ((T:ℝ)-s).toNNReal) (Q s)) (Icc 0 (T:ℝ)) s) :
    dist (F T w) (Q T) ≤ gronwallBound 0 (4*a⁻¹^2) (2*a⁻¹^2*δ) T := by
  let q (s : ℝ) := G ((T:ℝ)-s).toNNReal (F T w)
  have hq (s : ℝ) (hs : s ∈ Icc 0 (T:ℝ)) :=
    h.reverse_path_derivative T w ha haw s hs
  have hq0 : q 0=w := by
    simp only [q,sub_zero,Real.toNNReal_coe]
    exact h.2.2.2.2.2.2.2.2.1 T w (ha.trans_le haw)
  have hqT : q T=F T w := by
    simp only [q,sub_self,Real.toNNReal_zero]
    exact h.initial_value _ (h.2.2.2.2.2.2.1 T (ha.trans_le haw)).1.1
  have he := dist_le_of_approx_trajectories_ODE
    (K := (⟨4*a⁻¹^2, by positivity⟩ : ℝ≥0))
    (v := fun s => reverseField a (U ((T:ℝ)-s).toNNReal))
    (fun _ => reverseField_lipschitz ha _)
    (f := q) (fun s hs => (hq s hs).continuousWithinAt)
    (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hq s ⟨hs.1,hs.2.le⟩))
    (εf := 0) (fun _ _ => by simp [q])
    (g := Q) (fun s hs => (hQ s hs).continuousWithinAt)
    (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hQ s ⟨hs.1,hs.2.le⟩))
    (εg := 2*a⁻¹^2*δ) (fun s hs => ?_)
    (δ := 0) (by rw [hq0,hQ0,dist_self])
    T ⟨T.coe_nonneg,le_rfl⟩
  · change dist (q T) (Q T) ≤
      gronwallBound 0 (4*a⁻¹^2) (0+2*a⁻¹^2*δ) ((T:ℝ)-0) at he
    simpa only [hqT,zero_add,sub_zero] using he
  · have ht : ((T:ℝ)-s).toNNReal ∈ Icc 0 T := by
      refine ⟨zero_le,?_⟩
      exact_mod_cast (show (((T:ℝ)-s).toNNReal : ℝ) ≤ T by
        rw [Real.coe_toNNReal _ (by linarith [hs.2])]; linarith [hs.1])
    rw [dist_comm]
    exact (reverseField_driver_dist ha _ _ _).trans
      (mul_le_mul_of_nonneg_left (hUV _ ht) (by positivity))

lemma IsCapacityTwoWitness.inverse_displacement_bound
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) {a : ℝ} (ha : 0 < a)
    (w : ℂ) (haw : a ≤ w.im) : dist (F T w) w ≤ (2*a⁻¹)*T := by
  let q (s : ℝ) := G ((T:ℝ)-s).toNNReal (F T w)
  have hq (s : ℝ) (hs : s ∈ Icc 0 (T:ℝ)) :=
    h.reverse_path_derivative T w ha haw s hs
  have hb := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s hs => hq s hs) (fun s _ => reverseField_bound ha _ _) T
    ⟨T.coe_nonneg,le_rfl⟩
  have hq0 : q 0=w := by
    simp only [q,sub_zero,Real.toNNReal_coe]
    exact h.2.2.2.2.2.2.2.2.1 T w (ha.trans_le haw)
  have hqT : q T=F T w := by
    simp only [q,sub_self,Real.toNNReal_zero]
    exact h.initial_value _ (h.2.2.2.2.2.2.1 T (ha.trans_le haw)).1.1
  change ‖q T-q 0‖ ≤ _ at hb
  simpa only [hqT,hq0,sub_zero,dist_eq_norm] using hb

end SLEExactGauge

end

end OAI
