import OAI.Analysis.Daugavet.Diameter

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

universe uX u_1

namespace ExactModuli
variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma half_envelope (t : ℝ) : (t + max 0 (t - 2)) / 2 = max (t / 2) (t - 1) := by
  by_cases h : t ≤ 2
  · rw [max_eq_left (sub_nonpos.mpr h), max_eq_left (by linarith)]
    ring
  · rw [max_eq_right (sub_nonneg.mpr (le_of_not_ge h)), max_eq_right (by linarith)]
    ring

lemma cofinite_direction_upper (hsp : UnitSliceProperty X) {x : X} (hx : ‖x‖ = 1)
    {F : Submodule ℝ X} (hF : Cofinite F) {ε t : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2)
    (ht : 0 ≤ t) :
    ∃ y ∈ F, ‖y‖ = 1 ∧ ‖x + t • y‖ ≤ 1 + max 0 (t - 2) + 3 * ε := by
  obtain ⟨z, hzF, hzlo, hzhi, hend⟩ := cofinite_antipodal_endpoint hsp hx hF hε
  have hL : 0 < ‖z‖ := by linarith
  have hz : z ≠ 0 := norm_pos_iff.mp hL
  let y := ‖z‖⁻¹ • z
  have hy : ‖y‖ = 1 := norm_smul_inv_norm hz
  have hid : ‖z‖ • y = z := by
    dsimp [y]
    rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  have hb := norm_ray_endpoint_bound hx hy hL hε.le ht (show ‖x + ‖z‖ • y‖ ≤ 1 + ε by rwa [hid])
  have hmax : max 0 (t - ‖z‖) ≤ max 0 (t - 2) + 2 * ε := by
    apply max_le
    · linarith [le_max_left (0 : ℝ) (t - 2)]
    · linarith [le_max_right (0 : ℝ) (t - 2)]
  exact ⟨y, F.smul_mem _ hzF, hy, by linarith⟩

/-- Matching averaged upper curve, from one family of cofinite directions. -/
theorem averaged_upper_bound (hsp : UnitSliceProperty X) {x : X} (hx : ‖x‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) : H (normSeminorm ℝ X) x t ≤ max (t / 2) (t - 1) := by
  unfold H
  refine csSup_le ?_ ?_
  · exact ⟨_, ⊤, cofinite_top, rfl⟩
  rintro a ⟨F, hF, rfl⟩
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε := min (1 / 4 : ℝ) (δ / 6)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε < 1 / 2 := (min_le_left _ _).trans_lt (by norm_num)
  have hεδ : ε ≤ δ / 6 := min_le_right _ _
  obtain ⟨y, hyF, hy, hplus⟩ := cofinite_direction_upper hsp hx hF hε hε1 ht
  have hinf := csInf_le (averageValues_bddBelow x t F) ⟨y, hyF, hy.ge, rfl⟩
  have hminus := norm_sub_le x (t • y)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hx, hy, mul_one] at hminus
  change sInf (averageValues x t F) ≤ _
  change sInf (averageValues x t F) ≤ (‖x + t • y‖ + ‖x - t • y‖) / 2 - 1 at hinf
  rw [← half_envelope]
  linarith

/-- Matching one-sided upper curve, including the radius-two corner. -/
theorem oneSided_upper_bound (hsp : UnitSliceProperty X) {x : X} (hx : ‖x‖ = 1)
    {t : ℝ} (ht : 0 ≤ t) : D (normSeminorm ℝ X) x t ≤ max 0 (t - 2) := by
  unfold D
  refine csSup_le ?_ ?_
  · exact ⟨_, ⊤, cofinite_top, rfl⟩
  rintro a ⟨F, hF, rfl⟩
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε := min (1 / 4 : ℝ) (δ / 6)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε < 1 / 2 := (min_le_left _ _).trans_lt (by norm_num)
  have hεδ : ε ≤ δ / 6 := min_le_right _ _
  obtain ⟨y, hyF, hy, hplus⟩ := cofinite_direction_upper hsp hx hF hε hε1 ht
  have hinf := csInf_le (oneSidedValues_bddBelow x t F) ⟨y, hyF, hy, rfl⟩
  change sInf (oneSidedValues x t F) ≤ _
  linarith

variable {Ω : Type u_1} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem exact_pointwise (E : Submodule ℝ (Lp ℝ 1 μ))
    (hdim : ¬ FiniteDimensional ℝ E) (hpre : MeasurePrecompactBall μ E) (hd : Daugavet E)
    {x : E} (hx : ‖x‖ = 1) {t : ℝ} (ht : 0 < t) :
    H (normSeminorm ℝ E) x t = max (t / 2) (t - 1) ∧
    D (normSeminorm ℝ E) x t = max 0 (t - 2) := by
  exact ⟨le_antisymm (averaged_upper_bound (daugavet_unitSlice hd) hx ht.le)
      (clipping_lower_bound E hdim hpre hx ht),
    le_antisymm (oneSided_upper_bound (daugavet_unitSlice hd) hx ht.le)
      (oneSided_lower_bound hdim hx ht.le)⟩

/-- The infimum over centers is a separate conclusion, not an identification of definitions. -/
theorem exact_center_infima (E : Submodule ℝ (Lp ℝ 1 μ))
    (hdim : ¬ FiniteDimensional ℝ E) (hpre : MeasurePrecompactBall μ E) (hd : Daugavet E)
    {t : ℝ} (ht : 0 < t) :
    averagedModulus (normSeminorm ℝ E) t = max (t / 2) (t - 1) ∧
    oneSidedModulus (normSeminorm ℝ E) t = max 0 (t - 2) := by
  obtain ⟨x, _, hx⟩ := cofinite_has_unit hdim (cofinite_top (X := E))
  have hH : {r | ∃ x : E, ‖x‖ = 1 ∧ r = H (normSeminorm ℝ E) x t} =
      {max (t / 2) (t - 1)} := by
    apply eq_singleton_iff_unique_mem.mpr
    refine ⟨⟨x, hx, (exact_pointwise E hdim hpre hd hx ht).1.symm⟩, ?_⟩
    rintro r ⟨y, hy, rfl⟩
    exact (exact_pointwise E hdim hpre hd hy ht).1
  have hD : {r | ∃ x : E, ‖x‖ = 1 ∧ r = D (normSeminorm ℝ E) x t} =
      {max 0 (t - 2)} := by
    apply eq_singleton_iff_unique_mem.mpr
    refine ⟨⟨x, hx, (exact_pointwise E hdim hpre hd hx ht).2.symm⟩, ?_⟩
    rintro r ⟨y, hy, rfl⟩
    exact (exact_pointwise E hdim hpre hd hy ht).2
  constructor
  · change sInf {r | ∃ x : E, ‖x‖ = 1 ∧ r = H (normSeminorm ℝ E) x t} = _
    rw [hH, csInf_singleton]
  · change sInf {r | ∃ x : E, ‖x‖ = 1 ∧ r = D (normSeminorm ℝ E) x t} = _
    rw [hD, csInf_singleton]

end ExactModuli

end

end OAI
