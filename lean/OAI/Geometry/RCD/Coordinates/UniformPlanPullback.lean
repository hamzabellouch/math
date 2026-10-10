import OAI.Analysis.RCDHeat.SobolevTestPlan

namespace OAI

/-! # Uniform continuity of Sobolev pullbacks along short compressed plans

The modulus depends on the function and compression bound, so it applies
to a family of different radial plans as their lengths tend to zero.
-/

open Set Filter Metric MeasureTheory
open scoped ENNReal

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular]
attribute [local instance] pathBorel pathBorelSpace

theorem uniform_short_plan_pullback (G : Lp ℝ 2 μ) {C : ℝ≥0∞} (hC : C ≠ ∞)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (π : Measure C(Time, X)) [IsProbabilityMeasure π]
      (_hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
      (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • μ)
      (_hD : MemLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)) 2 π),
      (∀ᵐ γ ∂π, dist (γ 0) (γ 1) ≤ δ) → ∀ t : Time,
        ‖testPlanPullback μ π hC hcomp t G - testPlanPullback μ π hC hcomp 0 G‖ < ε := by
  let A := C.toReal ^ (1 / (2 : ℝ≥0∞)).toReal
  have hA : 0 ≤ A := Real.rpow_nonneg ENNReal.toReal_nonneg _
  let r := ε / (4 * (A + 1))
  have hr : 0 < r := div_pos hε (by positivity)
  obtain ⟨f, hf, φ, L, hφ, hm, rfl⟩ := (Metric.dense_iff.mp (lp_lipschitz_dense μ)) G r hr
  have hnear : ‖G - hm.toLp φ‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hf
  let δ := ε / (2 * ((L : ℝ) + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro π hπ hg hc hD hshort t
  let := hπ
  let T := testPlanPullback μ π hC hc
  have hop (s : Time) (v : Lp ℝ 2 μ) : ‖T s v‖ ≤ A * ‖v‖ :=
    ((T s).le_opNorm v).trans (mul_le_mul_of_nonneg_right
      (compressionPullback_norm_le μ π _ (measurable_path_eval s) hC (hc s)) (norm_nonneg v))
  have hDn : ‖hD.toLp (fun γ : C(Time, X) => dist (γ 0) (γ 1))‖ ≤ δ := by
    have hh := Lp.norm_le_of_ae_bound hδ.le (show ∀ᵐ γ ∂π,
        ‖hD.toLp (fun γ : C(Time, X) => dist (γ 0) (γ 1)) γ‖ ≤ δ from by
      filter_upwards [hD.coeFn_toLp, hshort] with γ hγ hs
      simpa only [hγ, Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using hs)
    simpa [measureUnivNNReal] using hh
  have ht : dist t 0 ≤ (1 : ℝ) := by
    change |(t : ℝ) - 0| ≤ 1
    simpa only [sub_zero, abs_of_nonneg t.2.1] using t.2.2
  have hmid : ‖T t (hm.toLp φ) - T 0 (hm.toLp φ)‖ ≤ (L : ℝ) * δ := by
    have hh := (testPlanPullback_lipschitz μ π hg hC hc hD hφ hm).dist_le_mul t 0
    rw [dist_eq_norm] at hh
    apply hh.trans
    change (L : ℝ) * ‖hD.toLp (fun γ : C(Time, X) => dist (γ 0) (γ 1))‖ * dist t 0 ≤ _
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDn L.coe_nonneg)
      dist_nonneg).trans (mul_le_of_le_one_right (mul_nonneg L.coe_nonneg hδ.le) ht)
  have hleft : ‖T t G - T t (hm.toLp φ)‖ ≤ A * r := by
    rw [← map_sub]
    exact (hop t _).trans (mul_le_mul_of_nonneg_left hnear.le hA)
  have hright : ‖T 0 (hm.toLp φ) - T 0 G‖ ≤ A * r := by
    rw [norm_sub_rev, ← map_sub]
    exact (hop 0 _).trans (mul_le_mul_of_nonneg_left hnear.le hA)
  have htotal : ‖T t G - T 0 G‖ ≤ A * r + (L : ℝ) * δ + A * r := by
    calc
      _ = ‖(T t G - T t (hm.toLp φ)) + (T t (hm.toLp φ) - T 0 (hm.toLp φ)) +
          (T 0 (hm.toLp φ) - T 0 G)‖ := by congr 1; abel
      _ ≤ _ := norm_add₃_le.trans (add_le_add (add_le_add hleft hmid) hright)
  apply htotal.trans_lt
  have hr_eq : 4 * (A + 1) * r = ε := by
    dsimp only [r]
    field_simp
  have hδ_eq : 2 * ((L : ℝ) + 1) * δ = ε := by
    dsimp only [δ]
    field_simp
  nlinarith

end RegularPointCoordinates

end OAI
