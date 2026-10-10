import OAI.Probability.SLE.Loewner.LoewnerInverseStability

namespace OAI

/-! Stability of raw reverse trajectories, including dependence on their
initial point. This is used before a geometric trace has been constructed. -/
noncomputable section
open Set Filter Complex Metric
open scoped Topology NNReal

namespace SLEExactGauge

lemma reverse_flow_driver_distance {a : ℝ} (ha : 0 < a)
    (U V : ℝ → ℝ) (Z Q : ℝ → ℂ) (T : ℝ)
    (hZ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Z
      (reverseField a (U t) (Z t)) (Icc 0 T) t)
    (hQ : ∀ t ∈ Icc 0 T, HasDerivWithinAt Q
      (reverseField a (V t) (Q t)) (Icc 0 T) t)
    (δ : ℝ) (hinit : dist (Z 0) (Q 0) ≤ δ)
    (hUV : ∀ t ∈ Icc 0 T, |U t-V t| ≤ δ) :
    ∀ t ∈ Icc 0 T, dist (Z t) (Q t) ≤
      gronwallBound δ (4*a⁻¹^2) (2*a⁻¹^2*δ) t := by
  intro t ht
  have he := dist_le_of_approx_trajectories_ODE
    (K := (⟨4*a⁻¹^2,by positivity⟩ : ℝ≥0))
    (v := fun s => reverseField a (U s)) (fun _ => reverseField_lipschitz ha _)
    (f := Z) (fun s hs => (hZ s hs).continuousWithinAt)
    (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hZ s ⟨hs.1,hs.2.le⟩))
    (εf := 0) (fun _ _ => by simp)
    (g := Q) (fun s hs => (hQ s hs).continuousWithinAt)
    (fun s hs => hasDerivWithinAt_Ici_of_Icc hs (hQ s ⟨hs.1,hs.2.le⟩))
    (εg := 2*a⁻¹^2*δ) (fun s hs => ?_) hinit t ht
  · change dist (Z t) (Q t) ≤ gronwallBound δ (4*a⁻¹^2) (0+2*a⁻¹^2*δ) (t-0) at he
    simpa only [zero_add,sub_zero] using he
  · rw [dist_comm]
    exact (reverseField_driver_dist ha _ _ _).trans
      (mul_le_mul_of_nonneg_left (hUV s (Ico_subset_Icc_self hs)) (by positivity))

lemma reverse_flow_lipschitz {a : ℝ} (ha : 0 < a)
    (U : ℝ → ℝ) (Q : ℝ → ℂ)
    (hQ : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt Q
      (reverseField a (U t) (Q t)) (Ici 0) t) :
    LipschitzOnWith ⟨2*a⁻¹,by positivity⟩ Q (Ici 0) := by
  apply (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hQ
  intro t ht
  exact_mod_cast reverseField_bound ha (U t) (Q t)

end SLEExactGauge

end

end OAI
