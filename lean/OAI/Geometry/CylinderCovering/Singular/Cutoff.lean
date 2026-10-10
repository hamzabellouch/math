import OAI.Geometry.CylinderCovering.Singular.CutoffDefinitions

namespace OAI

open Filter Topology Asymptotics

namespace CylinderCovering.SingularCutoff

lemma tendsto_rpow_zero {r : ℝ} (hr : 0 < r) :
    Tendsto (fun c : ℝ => c ^ r) (𝓝[>] 0) (𝓝 0) := by
  have h := ((Real.continuous_rpow_const hr.le).tendsto 0).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  simpa only [Real.zero_rpow hr.ne'] using h

lemma rpow_isLittleO_rpow {r s : ℝ} (hrs : s < r) :
    (fun c : ℝ => c ^ r) =o[𝓝[>] 0] (fun c => c ^ s) := by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · apply (tendsto_rpow_zero (sub_pos.mpr hrs)).congr'
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact Real.rpow_sub (show 0 < c from hc) r s
  · filter_upwards [self_mem_nhdsWithin] with c hc
    exact fun h => False.elim ((Real.rpow_pos_of_pos (show 0 < c from hc) s).ne' h)

lemma powerCutoff_littleO {A β : ℝ} (hA : 0 < A) (hβ : 1 < β) :
    powerCutoff A β =o[𝓝[>] 0] (fun c => c) := by
  have h := (rpow_isLittleO_rpow hβ).const_mul_left (A ^ β)
  apply h.congr'
  · filter_upwards [self_mem_nhdsWithin] with c hc
    exact (Real.mul_rpow hA.le (show 0 ≤ c from le_of_lt hc)).symm
  · exact Filter.Eventually.of_forall (fun c => Real.rpow_one c)

lemma powerCutoff_derivative_small {A p β : ℝ} (hA : 0 < A)
    (hβp : 0 < 1 + β * (p - 2)) :
    Tendsto (fun c => c * (powerCutoff A β c) ^ (p - 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := (tendsto_rpow_zero hβp).const_mul (A ^ (β * (p - 2)))
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hc : 0 < c := hc
  unfold powerCutoff
  rw [← Real.rpow_mul (mul_pos hA hc).le, Real.mul_rpow hA.le hc.le,
    Real.rpow_add hc, Real.rpow_one]
  ring

lemma powerPadding_littleO_square {A B η : ℝ} (hA : 0 < A) (hη : 2 < η) :
    powerPadding A B η =o[𝓝[>] 0] (fun c => c ^ (2 : ℕ)) := by
  have h := (rpow_isLittleO_rpow hη).const_mul_left (B * A ^ η)
  apply h.congr'
  · filter_upwards [self_mem_nhdsWithin] with c hc
    unfold powerPadding
    rw [Real.mul_rpow hA.le (show 0 ≤ c from le_of_lt hc)]
    ring
  · exact Filter.Eventually.of_forall (fun c => Real.rpow_natCast c 2)

lemma cube_littleO_powerPadding {A B η : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hη : η < 3) :
    (fun c => c ^ (3 : ℕ)) =o[𝓝[>] (0 : ℝ)] powerPadding A B η := by
  have h := (rpow_isLittleO_rpow hη).const_mul_right
    (mul_pos hB (Real.rpow_pos_of_pos hA η)).ne'
  apply h.congr'
  · exact Filter.Eventually.of_forall (fun c => Real.rpow_natCast c 3)
  · filter_upwards [self_mem_nhdsWithin] with c hc
    unfold powerPadding
    rw [Real.mul_rpow hA.le (show 0 ≤ c from le_of_lt hc)]
    ring

theorem power_admissible {A B p β η : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hβ : 1 < β) (hβp : 0 < 1 + β * (p - 2)) (hη₂ : 2 < η) (hη₃ : η < 3) :
    Admissible p (powerCutoff A β) (powerPadding A B η) := by
  refine ⟨?_, powerCutoff_littleO hA hβ, powerCutoff_derivative_small hA hβp,
    powerPadding_littleO_square hA hη₂, cube_littleO_powerPadding hA hB hη₃⟩
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact ⟨Real.rpow_pos_of_pos (mul_pos hA hc) β,
    mul_pos hB (Real.rpow_pos_of_pos (mul_pos hA hc) η)⟩

theorem edge_one_alternative_admissible {p β : ℝ} (hp : p < 2)
    (hβ : 1 < β) (hβp : β < 1 / (2 - p)) :
    Admissible p (powerCutoff 4 β) (powerPadding 4 1 (5 / 2)) := by
  apply power_admissible (by norm_num) (by norm_num) hβ _ (by norm_num) (by norm_num)
  have h := (lt_div_iff₀ (sub_pos.mpr hp)).mp hβp
  nlinarith

lemma cutoff_tendsto_zero {p : ℝ} {ρ q : ℝ → ℝ} (h : Admissible p ρ q) :
    Tendsto ρ (𝓝[>] 0) (𝓝 0) :=
  h.2.1.tendsto_zero_of_tendsto (tendsto_id.mono_left nhdsWithin_le_nhds)

lemma padding_tendsto_zero {p : ℝ} {ρ q : ℝ → ℝ} (h : Admissible p ρ q) :
    Tendsto q (𝓝[>] 0) (𝓝 0) := by
  have h0 : Tendsto (fun c : ℝ => c) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  exact h.2.2.2.1.tendsto_zero_of_tendsto (h0.pow 2)

lemma tip_area_littleO {p : ℝ} {ρ q : ℝ → ℝ} (h : Admissible p ρ q) :
    (fun c => (ρ c) ^ (2 : ℕ)) =o[𝓝[>] 0] (fun c => c ^ (2 : ℕ)) :=
  h.2.1.pow (by norm_num)

lemma overlap_error_eventually {p : ℝ} {ρ q : ℝ → ℝ}
    (h : Admissible p ρ q) (K : ℝ) :
    ∀ᶠ c in 𝓝[>] (0 : ℝ), 16 * K ^ 2 * c ^ 3 ≤ 2 * q c := by
  have ht := h.2.2.2.2.tendsto_div_nhds_zero.const_mul (16 * K ^ 2)
  simp only [mul_zero] at ht
  filter_upwards [h.1, ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 2))]
    with c hc he
  have hq : 0 < q c := hc.2
  have he' : (16 * K ^ 2 * c ^ 3) / q c < 2 := by
    rw [mul_div_assoc]
    exact he
  exact ((div_lt_iff₀ hq).mp he').le

lemma edge_one_coefficient_identity {p : ℝ} (hp : p ≠ 0) :
    boundaryCoefficient p - energyCoefficient p = edgeOneCoefficient p := by
  unfold boundaryCoefficient energyCoefficient edgeOneCoefficient
  field_simp
  ring

lemma edge_one_coefficient_negative {p : ℝ} (hp : 1 < p)
    (hp' : p < (Real.sqrt 51 - 5) / 2) : edgeOneCoefficient p < 0 := by
  have hs : (Real.sqrt 51) ^ 2 = (51 : ℝ) := Real.sq_sqrt (by norm_num)
  have hr : 2 * p + 5 < Real.sqrt 51 := by linarith
  have hnum : 2 * p ^ 2 + 10 * p - 13 < 0 := by nlinarith
  exact div_neg_of_neg_of_pos hnum (by linarith)

lemma boundaryCoefficient_one : boundaryCoefficient 1 = 16 / 15360 := by
  norm_num [boundaryCoefficient]

lemma energyCoefficient_one : energyCoefficient 1 = 17 / 15360 := by
  norm_num [energyCoefficient]

lemma edgeOneCoefficient_one : edgeOneCoefficient 1 = -1 / 15360 := by
  norm_num [edgeOneCoefficient]

end CylinderCovering.SingularCutoff

end OAI
