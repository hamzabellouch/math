import OAI.Analysis.CircleDomains.Topology.SphereChartInversePairs

namespace OAI

/-! Quadratic area estimates with constants uniform near a finite centre. -/

open Set Filter Function Metric MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem spherical_ball_area_bound_near (z : ℂ) :
    ∃ V : Set Sphere, IsOpen V ∧ (z : Sphere) ∈ V ∧
      ∃ R : ℝ, 0 < R ∧ ∃ K : ℝ≥0∞, K ≠ ∞ ∧
        ∀ w : ℂ, (w : Sphere) ∈ V → ∀ r : ℝ≥0, (r : ℝ) < R →
          sphericalArea (ball (w : Sphere) r) ≤ K * (r : ℝ≥0∞) ^ 2 := by
  obtain ⟨L, W, hW, hL⟩ := finite_sphere_chart_inverse_pairs z
  have hc : Continuous (fun p : Sphere => (roundSphereEquiv p : RoundAmbient)) :=
    continuous_subtype_val.comp roundSphereEquiv.continuous
  obtain ⟨R, hR, hRW⟩ := Metric.mem_nhds_iff.mp (hc.continuousAt.preimage_mem_nhds hW)
  let K : ℝ≥0∞ := 4 * (↑(L + 1) : ℝ≥0∞) ^ 2 * NNReal.pi
  refine ⟨ball (z : Sphere) (R / 2), isOpen_ball, mem_ball_self (by positivity),
    R / 2, by positivity, K, by dsimp [K]; finiteness, ?_⟩
  intro w hw r hr
  have hwW : (roundSphereEquiv (w : Sphere) : RoundAmbient) ∈ W :=
    hRW (ball_subset_ball (by linarith : R / 2 ≤ R) hw)
  let A : Set ℂ := ((↑) : ℂ → Sphere) ⁻¹' ball (w : Sphere) r
  have hAB : A ⊆ closedBall w ((L + 1 : ℝ≥0) * r) := by
    intro u hu
    have huR : (u : Sphere) ∈ ball (z : Sphere) R := by
      exact (dist_triangle (u : Sphere) (w : Sphere) (z : Sphere)).trans_lt
        (by have h1 : dist (u : Sphere) (w : Sphere) < r := hu
            have h2 : dist (w : Sphere) (z : Sphere) < R / 2 := hw
            linarith)
    have hb := hL u w (hRW huR) hwW
    have hd : dist (u : Sphere) (w : Sphere) < r := hu
    change dist u w ≤ (L + 1 : ℝ≥0) * r
    calc
      dist u w ≤ L * dist (u : Sphere) (w : Sphere) := hb
      _ ≤ L * r := mul_le_mul_of_nonneg_left hd.le L.coe_nonneg
      _ ≤ (L + 1 : ℝ≥0) * r :=
        mul_le_mul_of_nonneg_right (by simp) r.coe_nonneg
  rw [sphericalArea, Measure.map_apply OnePoint.continuous_coe.measurable measurableSet_ball,
    withDensity_apply _ (OnePoint.continuous_coe.measurable measurableSet_ball)]
  calc
    _ ≤ ∫⁻ _ in A, (4 : ℝ≥0∞) := by
      apply lintegral_mono
      intro u
      exact (ENNReal.ofReal_le_ofReal (sphericalAreaDensity_le_four u)).trans_eq (by norm_num)
    _ = 4 * volume A := by simp
    _ ≤ 4 * volume (closedBall w ((L + 1 : ℝ≥0) * r)) :=
      mul_le_mul' le_rfl (measure_mono hAB)
    _ = K * (r : ℝ≥0∞) ^ 2 := by
      rw [Complex.volume_closedBall]
      rw [show ENNReal.ofReal ((L + 1 : ℝ≥0) * r) =
        (↑(L + 1) : ℝ≥0∞) * ↑r from by
          rw [← NNReal.coe_mul, ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul], mul_pow]
      dsimp [K]
      ring

theorem spherical_ball_area_bound_on_compact {T : Set ℂ} (hT : IsCompact T) :
    ∃ R : ℝ, 0 < R ∧ ∃ K : ℝ≥0∞, K ≠ ∞ ∧
      ∀ z ∈ T, ∀ r : ℝ≥0, (r : ℝ) < R →
        sphericalArea (ball (z : Sphere) r) ≤ K * (r : ℝ≥0∞) ^ 2 := by
  classical
  choose V hVo hVm R hRp K hK hbound using spherical_ball_area_bound_near
  obtain ⟨s, hs⟩ := hT.elim_finite_subcover
    (fun z : ℂ => ((↑) : ℂ → Sphere) ⁻¹' V z)
    (fun z => (hVo z).preimage OnePoint.continuous_coe)
    (fun z _ => mem_iUnion.mpr ⟨z, hVm z⟩)
  have hmin : ∃ r : ℝ, 0 < r ∧ ∀ z ∈ s, r ≤ R z := by
    clear hs
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert z s hz ih =>
      obtain ⟨r, hr, hrR⟩ := ih
      refine ⟨min r (R z), lt_min hr (hRp z), ?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hrR w hw)
  obtain ⟨r, hr, hrR⟩ := hmin
  refine ⟨r, hr, ∑ z ∈ s, K z, ENNReal.sum_ne_top.mpr (fun z _ => hK z), ?_⟩
  intro z hz a ha
  obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp (hs hz)
  exact (hbound w z hzw a (ha.trans_le (hrR w hw))).trans
    (mul_le_mul' (Finset.single_le_sum (fun _ _ => zero_le) hw) le_rfl)

theorem spherical_ball_area_bound_away_infinity (A : Set Sphere)
    (hinf : OnePoint.infty ∉ closure A) :
    ∃ R : ℝ, 0 < R ∧ ∃ K : ℝ≥0∞, K ≠ ∞ ∧
      ∀ p ∈ A, ∀ r : ℝ≥0, (r : ℝ) < R →
        sphericalArea (ball p r) ≤ K * (r : ℝ≥0∞) ^ 2 := by
  have hT : IsCompact (((↑) : ℂ → Sphere) ⁻¹' closure A) :=
    isCompact_finite_preimage isClosed_closure hinf
  obtain ⟨R, hR, K, hK, hb⟩ := spherical_ball_area_bound_on_compact hT
  refine ⟨R, hR, K, hK, ?_⟩
  intro p hp
  cases p using OnePoint.rec with
  | infty => exact (hinf (subset_closure hp)).elim
  | coe z => exact hb z (subset_closure hp)

theorem spherical_ball_sequence_area_bound (A : Set Sphere)
    (hinf : OnePoint.infty ∉ closure A) (a : ℕ → ℝ≥0)
    (hat : Tendsto (fun n => (a n : ℝ)) atTop (𝓝 0)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ᶠ n in atTop, ∀ p ∈ A,
      sphericalArea (ball p (2 * a n)) ≤ C * (a n : ℝ≥0∞) ^ 2 := by
  obtain ⟨R, hR, K, hK, hb⟩ := spherical_ball_area_bound_away_infinity A hinf
  refine ⟨4 * K, by finiteness, ?_⟩
  filter_upwards [hat.eventually (gt_mem_nhds (half_pos hR))] with n hn
  intro p hp
  have h2 : ((2 * a n : ℝ≥0) : ℝ) < R := by
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    linarith
  calc
    sphericalArea (ball p (2 * a n)) ≤ K * ((2 * a n : ℝ≥0) : ℝ≥0∞) ^ 2 :=
      hb p hp (2 * a n) h2
    _ = (4 * K) * (a n : ℝ≥0∞) ^ 2 := by
      rw [ENNReal.coe_mul, ENNReal.coe_ofNat, mul_pow]
      ring

end CircleDomainRigidity

end

end OAI
