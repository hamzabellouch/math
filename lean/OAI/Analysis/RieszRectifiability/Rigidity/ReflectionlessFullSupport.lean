import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.ReflectionlessAnnularBounds
import OAI.Analysis.RieszRectifiability.Foundations.FullSupportFromAnnuli

namespace OAI

/-!
# Full intrinsic support of reflectionless measures

Monotone approximation of strict annuli extends the centered annular vector estimate
without a boundary-mass assumption. Kernel antisymmetry then puts these bounds in the
form needed by the intrinsic full-support criterion. Thus a nonzero reflectionless
measure with global upper growth and support-centered lower growth fills its ambient
space when the growth exponent equals the ambient dimension.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem reflectionless_strict_annular_vector_bound {d : ℕ} (p : ℕ) (C c : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (hc : 0 < c) (a : Ambient d)
    (hlower : ∀ t : ℝ, 0 < t → ENNReal.ofReal (c * t ^ (p + 1)) ≤ μ (ball a t))
    (hreflect : ScalarReflectionlessAt (p + 1) μ a)
    (ε R : ℝ) (hε : 0 < ε) (hR : 0 < R) :
    ‖∫ y in ball a R ∩ {y | ε < dist y a}, kernel (p + 1) a y ∂μ‖ ≤
      2 * normalizedBumpPairingBound p C c := by
  have hD := normalizedBumpPairingBound_nonneg p C c hg.1 hc
  by_cases hεR : ε < R
  · let r := fun j : ℕ => ε + (R - ε) * (1 / 2 : ℝ) ^ j
    have hrε (j : ℕ) : ε < r j := by
      dsimp only [r]
      have hp : 0 < (R - ε) * (1 / 2 : ℝ) ^ j :=
        mul_pos (sub_pos.mpr hεR) (pow_pos (by norm_num) j)
      linarith
    have hrpos (j : ℕ) : 0 < r j := hε.trans (hrε j)
    have hrR (j : ℕ) : r j ≤ R := by
      have hp : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have h := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hεR.le)
      dsimp only [r]
      linarith
    have hrmono : Antitone r := by
      intro i j hij
      have hp : (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ i :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hij
      change ε + (R - ε) * (1 / 2 : ℝ) ^ j ≤ ε + (R - ε) * (1 / 2 : ℝ) ^ i
      linarith [mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hεR.le)]
    have hrlim : Tendsto r atTop (𝓝 ε) := by
      have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
      simpa only [mul_zero, add_zero] using!
        tendsto_const_nhds.add (hp.const_mul (R - ε))
    let s := fun j : ℕ => ball a R \ ball a (r j)
    have hsm (j : ℕ) : MeasurableSet (s j) := measurableSet_ball.diff measurableSet_ball
    have hsmono : Monotone s := by
      intro i j hij
      exact sdiff_subset_sdiff_right (ball_subset_ball (hrmono hij))
    have hcover : (⋃ j, s j) = ball a R ∩ {y | ε < dist y a} := by
      ext y
      constructor
      · intro hy
        obtain ⟨j, hj⟩ := mem_iUnion.mp hy
        have hd : r j ≤ dist y a := le_of_not_gt hj.2
        exact ⟨hj.1, (hrε j).trans_le hd⟩
      · intro hy
        obtain ⟨j, hj⟩ := (hrlim.eventually (gt_mem_nhds hy.2)).exists
        exact mem_iUnion.mpr ⟨j, hy.1, not_lt.mpr hj.le⟩
    let : IsFiniteMeasure (μ.restrict (ball a R)) :=
      finiteMeasure_restrict_ball_of_globalGrowth (p + 1) C μ hg a R hR
    have hk : IntegrableOn (kernel (p + 1) a)
        (ball a R ∩ {y | ε < dist y a}) μ := by
      have hbase := center_kernel_integrable_finite_exterior (p + 1)
        (μ.restrict (ball a R)) a ε hε
      have hsub : {y : Ambient d | ε < dist y a} ⊆ closedExterior a ε := by
        intro y hy
        simpa only [closedExterior, mem_ofPred_eq, dist_comm a y] using! hy.le
      have h := hbase.mono_set hsub
      have hmeas : MeasurableSet {y : Ambient d | ε < dist y a} :=
        measurableSet_lt measurable_const (continuous_id.dist continuous_const).measurable
      rw [IntegrableOn, Measure.restrict_restrict hmeas,
        inter_comm] at h
      exact h
    have ht := tendsto_setIntegral_of_monotone hsm hsmono
      (show IntegrableOn (kernel (p + 1) a) (⋃ j, s j) μ by rw [hcover]; exact hk)
    rw [hcover] at ht
    exact le_of_tendsto ht.norm (Eventually.of_forall fun j =>
      reflectionless_centered_annular_vector_bound p C c μ hg hc a hlower hreflect
        (r j) R (hrpos j) (hrR j))
  · have hs : ball a R ∩ {y : Ambient d | ε < dist y a} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hεR (hy.2.trans hy.1)
    rw [hs, Measure.restrict_empty, integral_zero_measure, norm_zero]
    positivity

theorem norm_integral_reverse_kernel {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) :
    ‖∫ y, kernel n y a ∂μ‖ = ‖∫ y, kernel n a y ∂μ‖ := by
  have heq : (fun y : Ambient d => kernel n y a) = fun y => -kernel n a y := by
    funext y
    exact kernel_antisymm (d := d) n a y
  rw [heq, integral_neg, norm_neg]

theorem intrinsic_full_support_of_reflectionless (p : ℕ)
    (μ : Measure (Ambient (p + 1))) [SFinite μ] (hμ : μ ≠ 0)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth (p + 1) G μ)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ (p + 1) / C) ≤ μ (ball x R))
    (hreflect : ∀ a ∈ μ.support, ScalarReflectionlessAt (p + 1) μ a) :
    μ.support = univ := by
  apply intrinsic_full_support_of_local_annular_bounds p μ hμ C G hC hg hlower
  intro a ha
  refine ⟨1, zero_lt_one, 2 * normalizedBumpPairingBound p G C⁻¹, ?_⟩
  intro ε hε
  have hl : ∀ t : ℝ, 0 < t → ENNReal.ofReal (C⁻¹ * t ^ (p + 1)) ≤ μ (ball a t) := by
    intro t ht
    convert! hlower a ha t ht using 1
    congr 1
    ring
  have hb := reflectionless_strict_annular_vector_bound (d := p + 1) p G C⁻¹ μ hg (inv_pos.mpr hC)
    a hl (hreflect a ha) ε 1 hε zero_lt_one
  rw [norm_integral_reverse_kernel]
  exact hb

end

end RieszRectifiability

end OAI
