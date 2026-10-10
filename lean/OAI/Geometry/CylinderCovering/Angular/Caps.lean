import OAI.Geometry.CylinderCovering.Angular.CapsDefinitions

namespace OAI

open Set

noncomputable section

namespace AngularCaps

theorem sqrt_quarter_bounds {z : ℝ} (hz : 0 ≤ z) :
    1 / 2 ≤ Real.sqrt (1 / 4 + z) ∧
      Real.sqrt (1 / 4 + z) ≤ 1 / 2 + z ∧
      |Real.sqrt (1 / 4 + z) - (1 / 2 + z)| ≤ z ^ 2 := by
  let t := Real.sqrt (1 / 4 + z)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = 1 / 4 + z := Real.sq_sqrt (by linarith)
  have ht : 1 / 2 ≤ t := by nlinarith
  have hupper : t ≤ 1 / 2 + z := by nlinarith [sq_nonneg (t - 1 / 2)]
  refine ⟨ht, hupper, ?_⟩
  change |t - (1 / 2 + z)| ≤ z ^ 2
  rw [abs_of_nonpos (by linarith)]
  have hsq : (t - 1 / 2) ^ 2 ≤ z ^ 2 :=
    (sq_le_sq₀ (by linarith) hz).2 (by linarith)
  nlinarith

theorem d_nonneg (q : ℝ) : 0 ≤ d q := by
  unfold d
  positivity

theorem d_le_one_eighth {q : ℝ} (hq : |q| ≤ 1) : d q ≤ 1 / 8 := by
  have hq2 : q ^ 2 ≤ 1 := by nlinarith [abs_le.mp hq, sq_abs q]
  have hq4 : q ^ 4 ≤ 1 := by
    nlinarith [sq_nonneg q, mul_self_le_mul_self (sq_nonneg q) hq2]
  unfold d
  linarith

theorem continuous_d : Continuous d := by
  unfold d
  fun_prop

theorem continuous_squaredRadius (τ η : ℝ) : Continuous (squaredRadius τ η) := by
  unfold squaredRadius
  exact Real.continuous_sqrt.comp (continuous_const.add
    (continuous_const.mul (continuous_d.add continuous_const)))

theorem squaredRadius_pos {τ η q : ℝ} (hη : 0 ≤ η) :
    0 < squaredRadius τ η q := by
  have h := sqrt_quarter_bounds (mul_nonneg (sq_nonneg τ) (add_nonneg (d_nonneg q) hη))
  change 0 < Real.sqrt (1 / 4 + τ ^ 2 * (d q + η))
  linarith [h.1]

theorem squaredRadius_expansion {τ η q : ℝ} (hη : 0 ≤ η) (hq : |q| ≤ 1) :
    |squaredRadius τ η q - (1 / 2 + τ ^ 2 * (d q + η))| ≤
      (1 / 8 + η) ^ 2 * τ ^ 4 := by
  have h := (sqrt_quarter_bounds
    (mul_nonneg (sq_nonneg τ) (add_nonneg (d_nonneg q) hη))).2.2
  have hcoeff : (d q + η) ^ 2 ≤ (1 / 8 + η) ^ 2 :=
    (sq_le_sq₀ (add_nonneg (d_nonneg q) hη) (by linarith)).2
      (by linarith [d_le_one_eighth hq])
  change |Real.sqrt (1 / 4 + τ ^ 2 * (d q + η)) -
    (1 / 2 + τ ^ 2 * (d q + η))| ≤ _
  calc
    _ ≤ (τ ^ 2 * (d q + η)) ^ 2 := h
    _ = (d q + η) ^ 2 * τ ^ 4 := by ring
    _ ≤ (1 / 8 + η) ^ 2 * τ ^ 4 :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)

theorem radialParameterSet_eq_image {l r : ℝ} {R : ℝ → ℝ}
    (hR : ∀ q ∈ Icc l r, 0 ≤ R q) :
    radialParameterSet l r R =
      (fun p : ℝ × ℝ => (p.1, p.2 * R p.1)) '' (Icc l r ×ˢ Icc 0 1) := by
  ext p
  constructor
  · rintro ⟨hpq, hps⟩
    by_cases hz : R p.1 = 0
    · have hs : p.2 = 0 := by rw [hz] at hps; exact le_antisymm hps.2 hps.1
      refine ⟨(p.1, 0), ⟨hpq, by norm_num⟩, ?_⟩
      apply Prod.ext
      · rfl
      · simpa using hs.symm
    · have hpos : 0 < R p.1 := lt_of_le_of_ne (hR p.1 hpq) (Ne.symm hz)
      refine ⟨(p.1, p.2 / R p.1), ⟨hpq, ?_⟩, ?_⟩
      · exact ⟨div_nonneg hps.1 hpos.le, (div_le_one hpos).2 hps.2⟩
      · simp [div_mul_cancel₀ _ hz]
  · rintro ⟨p, hp, rfl⟩
    refine ⟨hp.1, mul_nonneg hp.2.1 (hR p.1 hp.1), ?_⟩
    exact mul_le_of_le_one_left (hR p.1 hp.1) hp.2.2

theorem isCompact_radialParameterSet {l r : ℝ} {R : ℝ → ℝ}
    (hRcont : ContinuousOn R (Icc l r)) (hR : ∀ q ∈ Icc l r, 0 ≤ R q) :
    IsCompact (radialParameterSet l r R) := by
  rw [radialParameterSet_eq_image hR]
  apply (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn
  exact continuous_fst.continuousOn.prodMk
    (continuous_snd.continuousOn.mul
      (hRcont.comp continuous_fst.continuousOn (fun _ hp => hp.1)))

theorem isCompact_radialSector_image {E : Type*} [TopologicalSpace E]
    {l r : ℝ} {R : ℝ → ℝ} {F : (ℝ × ℝ) → E}
    (hRcont : ContinuousOn R (Icc l r)) (hR : ∀ q ∈ Icc l r, 0 ≤ R q)
    (hF : ContinuousOn F (radialParameterSet l r R)) :
    IsCompact (F '' radialParameterSet l r R) :=
  (isCompact_radialParameterSet hRcont hR).image_of_continuousOn hF

theorem isCompact_squaredRadius_parameters (l r τ η : ℝ) (hη : 0 ≤ η) :
    IsCompact (radialParameterSet l r (squaredRadius τ η)) :=
  isCompact_radialParameterSet (continuous_squaredRadius τ η).continuousOn
    (fun _ _ => (squaredRadius_pos hη).le)

end AngularCaps

end

end OAI
