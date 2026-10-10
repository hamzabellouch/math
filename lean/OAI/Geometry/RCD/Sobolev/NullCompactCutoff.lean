import OAI.Geometry.RCD.Heat.CompactHeatMeasure

namespace OAI

/-! # Continuous cutoffs of null compact sets with vanishing L² norm -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology CompactlySupported

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular]

omit [ProperSpace X] in
theorem compactTestToL2_norm_sq_le {F : C_c(X, ℝ)} {V : Set X}
    (hfin : μ V ≠ ∞) (hs : tsupport F ⊆ V)
    (hb : ∀ x, |F x| ≤ 1) : ‖compactTestToL2 μ F‖ ^ 2 ≤ μ.real V := by
  have hi : Integrable (fun x => (F x) ^ 2) μ :=
    (F.continuous.memLp_of_hasCompactSupport F.hasCompactSupport : MemLp F 2 μ).integrable_sq
  rw [← integral_sq_Lp μ (compactTestToL2 μ F)]
  calc
    _ = ∫ x, (F x) ^ 2 ∂μ := integral_congr_ae ((compactTestToL2_coe μ F).fun_comp fun t => t ^ 2)
    _ = ∫ x in V, (F x) ^ 2 ∂μ := by
      symm
      apply setIntegral_eq_integral_of_ae_compl_eq_zero
      filter_upwards with x hx
      have hz : F x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
      simp only [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    _ ≤ ∫ _x in V, (1 : ℝ) ∂μ := by
      apply integral_mono_ae hi.integrableOn (integrableOn_const hfin)
      filter_upwards with x
      have hx := hb x
      nlinarith [sq_abs (F x), abs_nonneg (F x)]
    _ = μ.real V := by simp

/-- Outer regularity supplies continuous unit cutoffs of a null compact
set whose actual L² classes converge to zero. -/
theorem exists_null_compact_cutoffs {S : Set X} (hS : IsCompact S) (hnull : μ S = 0) :
    ∃ F : ℕ → C_c(X, ℝ),
      (∀ i x, 0 ≤ F i x ∧ F i x ≤ 1) ∧
      (∀ i, EqOn (F i) 1 S) ∧
      Tendsto (fun i => compactTestToL2 μ (F i)) atTop (𝓝 0) := by
  have hex (i : ℕ) : ∃ F : C_c(X, ℝ),
      (∀ x, 0 ≤ F x ∧ F x ≤ 1) ∧ EqOn F 1 S ∧
        ‖compactTestToL2 μ F‖ ≤ 1 / ((i : ℝ) + 1) := by
    let δ := (1 / ((i : ℝ) + 1)) ^ 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    obtain ⟨V, hSV, hV, hμV⟩ := S.exists_isOpen_lt_of_lt (μ := μ)
      (ENNReal.ofReal δ) (by rw [hnull]; exact ENNReal.ofReal_pos.mpr hδ)
    obtain ⟨f, hfS, hfc, hfV, hfrange⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hS hV hSV
    let F : C_c(X, ℝ) := ⟨f, hfc⟩
    have hfin : μ V ≠ ∞ := (hμV.trans_le le_top).ne
    have hsq := compactTestToL2_norm_sq_le μ (F := F) hfin hfV (fun x => by
      change |f x| ≤ 1
      rw [abs_of_nonneg (hfrange x).1]
      exact (hfrange x).2)
    have hvol : μ.real V ≤ δ := by
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hμV.le
      simpa only [Measure.real, ENNReal.toReal_ofReal hδ.le] using hh
    refine ⟨F, hfrange, hfS, ?_⟩
    have hi : 0 < 1 / ((i : ℝ) + 1) := by positivity
    nlinarith [hsq.trans hvol, norm_nonneg (compactTestToL2 μ F)]
  choose F hF hS hnorm using hex
  refine ⟨F, hF, hS, tendsto_zero_iff_norm_tendsto_zero.mpr ?_⟩
  exact squeeze_zero (fun i => norm_nonneg _) hnorm tendsto_one_div_add_atTop_nhds_zero_nat

end RegularPointCoordinates

end

end OAI
