import OAI.Probability.SLE.Loewner.SmoothRawInverse
import OAI.Probability.SLE.Loewner.LoewnerInverseStability

namespace OAI

/-! A geometric inverse witness approaches the raw inverse under a
uniform driver perturbation. The reference driver needs no trace. -/
noncomputable section
open Set Filter Metric Complex
open scoped Topology NNReal

namespace SLEExactGauge

theorem IsCapacityTwoWitness.raw_inverse_driver_distance
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (b : Target.Driver) (T : ℝ≥0)
    {a : ℝ} (ha : 0 < a) (w : ℂ) (haw : a ≤ w.im)
    (δ : ℝ) (hUb : ∀ t ∈ Icc 0 T, |U t-b t| ≤ δ) :
    dist (F T w) (Target.inverseFlow 1 b T w) ≤
      gronwallBound 0 (4*a⁻¹^2) (2*a⁻¹^2*δ) T := by
  obtain ⟨q,hq0,hheight,hqd,he⟩ := Target.exists_raw_reverse_trajectory b T w (ha.trans_le haw)
  rw [he]
  apply h.inverse_approximation_bound T ha w haw b δ hUb q hq0
  intro s hs
  have hh := (hqd s hs.1).mono (show Icc 0 (T : ℝ) ⊆ Ici 0 from Icc_subset_Ici_self)
  have hr : reverseField a (b ((T : ℝ)-s).toNNReal) (q s) =
      -2/(q s-(Target.driverValue b ((T : ℝ)-s) : ℂ)) := by
    rw [reverseField,reverseCenter_eq (haw.trans (hheight s hs.1))]
    rfl
  rw [hr]
  exact hh

theorem raw_inverse_limit_of_witness_drivers
    (U : ℕ → ℝ≥0 → ℝ) (γ : ℕ → ℝ≥0 → ℂ) (G F : ℕ → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ n, IsCapacityTwoWitness (U n) (γ n) (G n) (F n))
    (b : Target.Driver) (T : ℝ≥0) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hUb : ∀ n t, t ∈ Icc 0 T → |U n t-b t| ≤ δ n)
    {w : ℂ} (hwH : w ∈ upperHalfPlane) :
    Tendsto (fun n => F n T w) atTop (𝓝 (Target.inverseFlow 1 b T w)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hb := fun n => (hw n).raw_inverse_driver_distance b T hwH w le_rfl (δ n) (hUb n)
  have ht := (gronwallBound_continuous_ε 0 (4*w.im⁻¹^2) T).continuousAt.tendsto.comp
    (hδ.const_mul (2*w.im⁻¹^2))
  simp only [Function.comp_def,mul_zero,gronwallBound_ε0_δ0] at ht
  exact squeeze_zero (fun _ => dist_nonneg) hb ht

end SLEExactGauge

end

end OAI
