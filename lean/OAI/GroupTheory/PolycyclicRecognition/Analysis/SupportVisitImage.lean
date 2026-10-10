import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportVisitPaths

namespace OAI

/-! # Image control on a visit between two good sheets

Only the outward and return sheets require a prescribed profile. The short
root switch is controlled from its first endpoint by Lipschitz continuity.
-/

noncomputable section

namespace PolycyclicRecognition

open Set
open scoped NNReal

variable {G W : Type*} [Group G] [PseudoMetricSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The metric estimate for the actual visit does not require any height
homomorphism or restriction on the initial sheet. -/
theorem supportVisitPath_metric_bound
    (d : ℝ → G) (hd : Continuous d) (hzero : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → ∀ n d₀ : G,
      ∀ (f : ℝ → G) (hf : Continuous f) (hf₀ : f 0 = 1) (b κ : ℝ), 0 ≤ κ →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (n * f (s * b) * (d₀ * d r)) (n * f (t * b) * (d₀ * d r)) ≤ κ) →
      PathMetricBound (supportVisitPath d hd hzero f hf hf₀ n d₀ r b)
        (4 * C * r) (4 * (C + κ)) := by
  obtain ⟨C, hC, hb⟩ := exists_flowLeg_coarse_bound d hd hzero hmul
  refine ⟨C, hC, ?_⟩
  intro r hr n d₀ f hf hf₀ b κ hκ hswitch
  let p₀ := flowPath d hd hzero (n * d₀) r
  let p₁ := flowPath d hd hzero (n * f b * d₀) r
  let q : Path ((n * d₀) * d r) ((n * f b * d₀) * d r) := {
    toFun := fun t => n * f ((t : ℝ) * b) * (d₀ * d r)
    continuous_toFun := (continuous_const.mul
      (hf.comp (continuous_subtype_val.mul continuous_const))).mul continuous_const
    source' := by simp [hf₀, mul_assoc]
    target' := by simp [mul_assoc] }
  have hleg (y : G) : PathMetricBound (flowPath d hd hzero y r) (C * r) (C + κ) := by
    intro s t
    have hh := hb y r hr (s : ℝ) (t : ℝ)
    change dist (flowPath d hd hzero y r s) (flowPath d hd hzero y r t) ≤
      C * r * |(t : ℝ) - s| + C at hh
    rw [abs_sub_comm] at hh
    linarith
  have hq : PathMetricBound q (C * r) (C + κ) := by
    intro s t
    have hh := hswitch s s.property t t.property
    change dist (q s) (q t) ≤ κ at hh
    have := mul_nonneg (mul_nonneg hC hr) (abs_nonneg ((s : ℝ) - t))
    linarith
  have hback : PathMetricBound p₁.symm (2 * (C * r)) (2 * (C + κ)) :=
    (hleg (n * f b * d₀)).symm.mono (by nlinarith [mul_nonneg hC hr]) (by linarith)
  have hh := ((hleg (n * d₀)).trans (add_nonneg hC hκ) hq).trans
    (by positivity) hback
  convert hh using 1 <;> first | rfl | ring

omit [IsIsometricSMul G G] in
/-- An arbitrary Lipschitz observable has controlled image on the whole
visit once both endpoint sheets have controlled images along the support leg. -/
theorem supportVisitPath_image_bound
    (d : ℝ → G) (hd : Continuous d) (hzero : d 0 = 1)
    (f : ℝ → G) (hf : Continuous f) (hf₀ : f 0 = 1)
    (J : G → W) {K : ℝ≥0} (hJ : LipschitzWith K J)
    (n d₀ : G) (r b : ℝ) (center : W) (E : Set W) {B κ : ℝ}
    (hκ : 0 ≤ κ)
    (hout : ∀ t : unitInterval, ∃ w ∈ E,
      ‖J ((n * d₀) * d (r * t)) - center - r • w‖ ≤ B)
    (hback : ∀ t : unitInterval, ∃ w ∈ E,
      ‖J ((n * f b * d₀) * d (r * t)) - center - r • w‖ ≤ B)
    (hswitch : ∀ t : unitInterval,
      dist (n * f ((t : ℝ) * b) * (d₀ * d r)) ((n * d₀) * d r) ≤ κ) :
    ∀ t, ∃ w ∈ E,
      ‖J (supportVisitPath d hd hzero f hf hf₀ n d₀ r b t) - center - r • w‖ ≤
        B + K * κ := by
  let S := {g : G | ∃ w ∈ E, ‖J g - center - r • w‖ ≤ B + K * κ}
  have hsmall : 0 ≤ (K : ℝ) * κ := mul_nonneg K.coe_nonneg hκ
  have hp₀ : ∀ t, flowPath d hd hzero (n * d₀) r t ∈ S := by
    intro t
    obtain ⟨w, hw, hh⟩ := hout t
    exact ⟨w, hw, hh.trans (le_add_of_nonneg_right hsmall)⟩
  have hp₁ : ∀ t, (flowPath d hd hzero (n * f b * d₀) r).symm t ∈ S := by
    intro t
    obtain ⟨w, hw, hh⟩ := hback (unitInterval.symm t)
    exact ⟨w, hw, hh.trans (le_add_of_nonneg_right hsmall)⟩
  let q : Path ((n * d₀) * d r) ((n * f b * d₀) * d r) := {
    toFun := fun t => n * f ((t : ℝ) * b) * (d₀ * d r)
    continuous_toFun := (continuous_const.mul
      (hf.comp (continuous_subtype_val.mul continuous_const))).mul continuous_const
    source' := by simp [hf₀, mul_assoc]
    target' := by simp [mul_assoc] }
  apply path_trans_range_mem (q := (flowPath d hd hzero (n * f b * d₀) r).symm)
    (path_trans_range_mem (q := q) hp₀ ?_) hp₁
  intro t
  obtain ⟨w, hw, hh⟩ := hout 1
  refine ⟨w, hw, ?_⟩
  have hdist := (hJ.dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left (hswitch t) K.coe_nonneg)
  have he : J (n * f ((t : ℝ) * b) * (d₀ * d r)) - center - r • w =
      (J (n * f ((t : ℝ) * b) * (d₀ * d r)) - J ((n * d₀) * d r)) +
        (J ((n * d₀) * d r) - center - r • w) := by abel
  change ‖J (n * f ((t : ℝ) * b) * (d₀ * d r)) - center - r • w‖ ≤ _
  rw [he]
  have hh' : ‖J ((n * d₀) * d r) - center - r • w‖ ≤ B := by simpa using hh
  calc
    _ ≤ ‖J (n * f ((t : ℝ) * b) * (d₀ * d r)) - J ((n * d₀) * d r)‖ +
        ‖J ((n * d₀) * d r) - center - r • w‖ := norm_add_le _ _
    _ ≤ K * κ + B := add_le_add (by simpa only [dist_eq_norm] using hdist) hh'
    _ = _ := add_comm _ _

end PolycyclicRecognition

end

end OAI
