import OAI.Analysis.Brenier.SharpOptimality
import OAI.Analysis.Brenier.SharpRectangle

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Problem358

/-- A positive real power can be made arbitrarily small at a positive argument. -/
theorem exists_pos_lt_rpow_lt {p ε δ : ℝ}
    (hp : 0 < p) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ t : ℝ, 0 < t ∧ t < ε ∧ t ^ p < δ := by
  have hlim : Tendsto (fun t : ℝ => t ^ p) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).rpow_const_nhds_zero hp
  have hpw : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t ^ p < δ :=
    hlim.eventually (gt_mem_nhds hδ)
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < ε :=
    eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds hε)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t :=
    self_mem_nhdsWithin
  exact (hpos.and (hsmall.and hpw)).exists

/-- Scalar mechanism behind the sharp one-third exponent: cubic transport displacement
cannot control linear map displacement with any exponent greater than one third. -/
theorem exists_cubic_scaling_violation {α C A B ε : ℝ}
    (hα : (1 / 3 : ℝ) < α) (hC : 0 < C) (hA : 0 < A)
    (hB : 0 < B) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < ε ∧ C * (A * t ^ 3) ^ α < B * t := by
  have hexp : 0 < 3 * α - 1 := by linarith
  have hcoef : 0 < C * A ^ α := mul_pos hC (Real.rpow_pos_of_pos hA α)
  obtain ⟨t, ht, htε, hpow⟩ := exists_pos_lt_rpow_lt hexp hε (div_pos hB hcoef)
  refine ⟨t, ht, htε, ?_⟩
  have hbound : (C * A ^ α) * t ^ (3 * α - 1) < B :=
    by simpa only [mul_comm] using (lt_div_iff₀ hcoef).mp hpow
  have htpow : (t ^ 3) ^ α = t ^ (3 * α - 1) * t := by
    calc
      (t ^ 3) ^ α = t ^ ((3 : ℝ) * α) := by
        rw [← Real.rpow_natCast t 3, ← Real.rpow_mul ht.le]
        norm_num
      _ = t ^ ((3 * α - 1) + 1) := by congr 1; ring
      _ = t ^ (3 * α - 1) * t := by rw [Real.rpow_add ht, Real.rpow_one]
  have hidentity : C * (A * t ^ 3) ^ α =
      ((C * A ^ α) * t ^ (3 * α - 1)) * t := by
    rw [Real.mul_rpow hA.le (pow_nonneg ht.le 3), htpow]
    ring
  rw [hidentity]
  exact mul_lt_mul_of_pos_right hbound ht

/-- The exact one-dimensional numerical inequality used by the three-plane example,
with the manuscript parameter `a` and `b = a / 2`. -/
theorem exists_sharpness_parameter {α C : ℝ}
    (hα : (1 / 3 : ℝ) < α) (hC : 0 < C) :
    ∃ a : ℝ, 0 < a ∧ a < 1 / 2 ∧
      C * (Real.sqrt (a * (a / 2) ^ 2)) ^ α <
        Real.sqrt (a / 4 + a * (a / 2) ^ 2) := by
  obtain ⟨t, ht, htε, hgap⟩ := exists_cubic_scaling_violation
    (A := (1 / 2 : ℝ)) (B := (1 / 2 : ℝ)) (ε := (1 / 2 : ℝ))
    hα hC (by norm_num) (by norm_num) (by norm_num)
  refine ⟨t ^ 2, sq_pos_of_pos ht, ?_, ?_⟩
  · nlinarith [sq_nonneg (t - 1 / 2)]
  · have hW : Real.sqrt (t ^ 2 * (t ^ 2 / 2) ^ 2) = (1 / 2 : ℝ) * t ^ 3 := by
      apply (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).2
      ring
    have hL : (1 / 2 : ℝ) * t ≤ Real.sqrt (t ^ 2 / 4 + t ^ 2 * (t ^ 2 / 2) ^ 2) := by
      apply (Real.le_sqrt (by positivity) (by positivity)).2
      nlinarith [sq_nonneg (t ^ 2 / 2), mul_nonneg (sq_nonneg t) (sq_nonneg (t ^ 2 / 2))]
    rw [hW]
    exact hgap.trans_le hL

/-- A lower bound proportional to `sqrt a`, rather than the exact map-distance formula,
is already sufficient for sharpness. This permits a simple rectangular disagreement set. -/
theorem exists_sharpness_parameter_of_lower_bound {α C D : ℝ}
    (hα : (1 / 3 : ℝ) < α) (hC : 0 < C) (hD : 0 < D) :
    ∃ a : ℝ, 0 < a ∧ a < 1 / 2 ∧
      C * (Real.sqrt (a * (a / 2) ^ 2)) ^ α < Real.sqrt (D * a) := by
  obtain ⟨t, ht, htε, hgap⟩ := exists_cubic_scaling_violation
    (A := (1 / 2 : ℝ)) (B := Real.sqrt D) (ε := (1 / 2 : ℝ))
    hα hC (by norm_num) (Real.sqrt_pos.mpr hD) (by norm_num)
  refine ⟨t ^ 2, sq_pos_of_pos ht, ?_, ?_⟩
  · nlinarith [sq_nonneg (t - 1 / 2)]
  · have hW : Real.sqrt (t ^ 2 * (t ^ 2 / 2) ^ 2) = (1 / 2 : ℝ) * t ^ 3 := by
      apply (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).2
      ring
    rw [hW, Real.sqrt_mul hD.le, Real.sqrt_sq ht.le]
    exact hgap

end Problem358

end

noncomputable section
open MeasureTheory

namespace Problem358

/-- A conservative rectangular lower bound still gives the sharp one-third obstruction. -/
theorem exists_sharpness_rectangle_parameter {α C : ℝ}
    (hα : (1 / 3 : ℝ) < α) (hC : 0 < C) :
    ∃ a : ℝ, 0 < a ∧ a < 1 / 2 ∧
      C * (Real.sqrt (a * (a / 2) ^ 2)) ^ α < Real.sqrt (a / 32) := by
  obtain ⟨t, ht, htε, hgap⟩ := exists_cubic_scaling_violation
    (A := (1 / 2 : ℝ)) (B := (1 / 8 : ℝ)) (ε := (1 / 2 : ℝ))
    hα hC (by norm_num) (by norm_num) (by norm_num)
  refine ⟨t ^ 2, sq_pos_of_pos ht, ?_, ?_⟩
  · nlinarith [sq_nonneg (t - 1 / 2)]
  · have hW : Real.sqrt (t ^ 2 * (t ^ 2 / 2) ^ 2) = (1 / 2 : ℝ) * t ^ 3 := by
      apply (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).2
      ring
    have hL : (1 / 8 : ℝ) * t ≤ Real.sqrt (t ^ 2 / 32) := by
      apply (Real.le_sqrt (by positivity) (by positivity)).2
      nlinarith [sq_nonneg t]
    rw [hW]
    exact hgap.trans_le hL

/-- Transport data sufficient for sharpness, needing bounds rather than exact distances. -/
structure SharpnessBoundsExample (d : ℕ) (a : ℝ) where
  μ : Measure (E d)
  ν : Measure (E d)
  Tμ : E d → E d
  Tν : E d → E d
  probability_μ : IsProbabilityMeasure μ
  probability_ν : IsProbabilityMeasure ν
  supported_μ : IsSupported μ (cube d)
  supported_ν : IsSupported ν (cube d)
  threeAtoms_μ : HasExactlyThreeAtoms μ (cube d)
  threeAtoms_ν : HasExactlyThreeAtoms ν (cube d)
  different : μ ≠ ν
  optimal_μ : IsUniqueQuadraticOptimalMap (uniformMeasure (cube d)) μ Tμ
  optimal_ν : IsUniqueQuadraticOptimalMap (uniformMeasure (cube d)) ν Tν
  wasserstein_pos : 0 < wasserstein2 μ ν
  wasserstein_le : wasserstein2 μ ν ≤ Real.sqrt (a * (a / 2) ^ 2)
  mapDistance_ge : Real.sqrt (a / 32) ≤ mapL2Dist (uniformMeasure (cube d)) Tμ Tν

/-- Rectangle-mass lower bounds suffice to conclude the exact sharpness assertion. -/
theorem one_third_exponent_is_sharp_of_bounds_examples (d : ℕ)
    (examples : ∀ a : ℝ, 0 < a → a < 1 / 2 → Nonempty (SharpnessBoundsExample d a)) :
    ∀ α : ℝ, (1 / 3 : ℝ) < α → ∀ C : ℝ, 0 < C →
      ∃ (μ ν : Measure (E d)) (Tμ Tν : E d → E d),
        IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
        IsSupported μ (cube d) ∧ IsSupported ν (cube d) ∧
        HasExactlyThreeAtoms μ (cube d) ∧ HasExactlyThreeAtoms ν (cube d) ∧
        μ ≠ ν ∧
        IsUniqueQuadraticOptimalMap (uniformMeasure (cube d)) μ Tμ ∧
        IsUniqueQuadraticOptimalMap (uniformMeasure (cube d)) ν Tν ∧
        0 < wasserstein2 μ ν ∧
        C * Real.rpow (wasserstein2 μ ν) α <
          mapL2Dist (uniformMeasure (cube d)) Tμ Tν := by
  intro α hα C hC
  obtain ⟨a, ha, haSmall, hgap⟩ := exists_sharpness_rectangle_parameter hα hC
  obtain ⟨ex⟩ := examples a ha haSmall
  refine ⟨ex.μ, ex.ν, ex.Tμ, ex.Tν, ex.probability_μ, ex.probability_ν,
    ex.supported_μ, ex.supported_ν, ex.threeAtoms_μ, ex.threeAtoms_ν,
    ex.different, ex.optimal_μ, ex.optimal_ν, ex.wasserstein_pos, ?_⟩
  have hα0 : 0 ≤ α := by linarith
  have hbound : C * Real.rpow (wasserstein2 ex.μ ex.ν) α ≤
      C * Real.rpow (Real.sqrt (a * (a / 2) ^ 2)) α :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow ex.wasserstein_pos.le ex.wasserstein_le hα0) hC.le
  exact (hbound.trans_lt hgap).trans_le ex.mapDistance_ge

end Problem358

namespace Problem358

/-- The explicit cube maps satisfy a conservative sharpness certificate.
This construction uses a small rectangle of disagreement, not the exact L² formula. -/
def sharpnessBoundsExample (d : ℕ) (hd : 2 ≤ d) (a : ℝ)
    (ha : 0 < a) (haSmall : a < 1 / 2) : SharpnessBoundsExample d a := by
  have ha1 : a < 1 := by linarith
  have hb : 0 < a / 2 := by positivity
  have hbabs : |a / 2| ≤ 1 := by rw [abs_of_pos hb]; linarith
  have hpush0 := map_sharpSlab_uniform_cube d hd a 0 le_rfl ha.le (by linarith)
  have hpushb := map_sharpSlab_uniform_cube d hd a (a / 2) hb.le (by linarith) (by linarith)
  refine {
    μ := sharpTarget d hd a 0
    ν := sharpTarget d hd a (a / 2)
    Tμ := Sharpness.slabMap (sharpAxis0 d hd) (sharpAxis1 d hd) a 0
    Tν := Sharpness.slabMap (sharpAxis0 d hd) (sharpAxis1 d hd) a (a / 2)
    probability_μ := sharpTarget_isProbabilityMeasure d hd 0 ha.le ha1.le
    probability_ν := sharpTarget_isProbabilityMeasure d hd (a / 2) ha.le ha1.le
    supported_μ := sharpTarget_isSupported d hd a 0 (by norm_num)
    supported_ν := sharpTarget_isSupported d hd a (a / 2) hbabs
    threeAtoms_μ := sharpTarget_hasExactlyThreeAtoms d hd ha ha1 (by norm_num)
    threeAtoms_ν := sharpTarget_hasExactlyThreeAtoms d hd ha ha1 hbabs
    different := sharpTarget_ne d hd ha (ne_of_gt hb)
    optimal_μ := Sharpness.slabMap_isUniqueQuadraticOptimalMap_sharpTarget d hd a 0 hpush0
    optimal_ν := Sharpness.slabMap_isUniqueQuadraticOptimalMap_sharpTarget d hd a (a / 2) hpushb
    wasserstein_pos := wasserstein2_sharpTarget_pos d hd ha ha1.le (ne_of_gt hb)
    wasserstein_le := (wasserstein2_sharpTarget d hd (a / 2) ha.le ha1.le).le
    mapDistance_ge := ?_
  }
  have h := Sharpness.slabMap_mapL2_lower (sharpAxis0 d hd) (sharpAxis1 d hd)
    (sharpAxis_ne d hd) ha.le hb (by linarith : a + (a / 2) / 2 ≤ 1)
  have he : (a / 2) / 16 = a / 32 := by ring
  simpa only [he] using h

/-- An independent full proof of the sharpness conclusion using only coarse map-distance bounds. -/
theorem one_third_exponent_is_sharp_via_rectangle :
    ∀ (d : ℕ), 2 ≤ d → ∀ α : ℝ, (1 / 3 : ℝ) < α → ∀ C : ℝ, 0 < C → ∃ (μ ν : Measure (E d)) (Tμ Tν : E d → E d), IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧ IsSupported μ (cube d) ∧ IsSupported ν (cube d) ∧ HasExactlyThreeAtoms μ (cube d) ∧ HasExactlyThreeAtoms ν (cube d) ∧ μ ≠ ν ∧ IsUniqueQuadraticOptimalMap (uniformMeasure (cube d)) μ Tμ ∧ IsUniqueQuadraticOptimalMap (uniformMeasure (cube d)) ν Tν ∧ 0 < wasserstein2 μ ν ∧ C * Real.rpow (wasserstein2 μ ν) α < mapL2Dist (uniformMeasure (cube d)) Tμ Tν := by
  intro d hd
  exact one_third_exponent_is_sharp_of_bounds_examples d
    (fun a ha haSmall => ⟨sharpnessBoundsExample d hd a ha haSmall⟩)

end Problem358

end

end OAI
