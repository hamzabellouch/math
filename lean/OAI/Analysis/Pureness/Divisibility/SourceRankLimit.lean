import OAI.Analysis.Pureness.Cuntz.CuntzRankMonotone

namespace OAI
namespace CuntzPureness
open Filter Topology
open scoped NNReal ENNReal ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma nnrpow_smul_real (a : A) (ha : 0 ≤ a) (s : ℝ) (hs : 0 ≤ s)
    (r : ℝ≥0) (hr : 0 < r) :
    CFC.nnrpow (s • a) r = s ^ (r : ℝ) • CFC.nnrpow a r := by
  have hf0 : (0 : ℝ) ^ (r : ℝ) = 0 := Real.zero_rpow (by exact_mod_cast hr.ne')
  simp only [CFC.nnrpow_eq_pow, CFC.nnrpow_eq_cfcₙ_real (s • a) r (smul_nonneg hs ha),
    CFC.nnrpow_eq_cfcₙ_real a r ha]
  rw [cfcₙ_eq_cfc (hf0 := hf0), cfcₙ_eq_cfc (hf0 := hf0),
    ← cfc_comp_const_mul s (fun t : ℝ => t ^ (r : ℝ)) a
      (hf := (Real.continuous_rpow_const (by positivity)).continuousOn) (ha := ha.isSelfAdjoint),
    ← cfc_const_mul (s ^ (r : ℝ)) (fun t : ℝ => t ^ (r : ℝ)) a]
  apply cfc_congr
  intro t ht
  exact Real.mul_rpow hs (spectrum_nonneg_of_nonneg ha ht)

lemma normalizedRoot_trace_tendsto_realRank (τ : TracialState A) (a : A) (ha : 0 ≤ a) :
    Tendsto (fun n => (τ.functional (normalizedRoot a n)).re) atTop
      (𝓝 (normalizedRootRank τ a).toReal) := by
  have hfinite : normalizedRootRank τ a ≠ ∞ :=
    ne_of_lt ((normalizedRootRank_le_one τ a ha).trans_lt ENNReal.one_lt_top)
  have ht := (ENNReal.tendsto_toReal hfinite).comp (normalizedRootRank_tendsto τ a ha)
  exact ht.congr' (Eventually.of_forall fun n => ENNReal.toReal_ofReal
    (Complex.nonneg_iff.mp (τ.functional.map_nonneg (normalizedRoot_nonneg a n))).1)

theorem source_root_trace_tendsto_rank (τ : TracialState A) (a : A) (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => ENNReal.ofReal
      (τ.functional (CFC.nnrpow a (((n : ℝ≥0) + 1)⁻¹))).re)
      atTop (𝓝 (normalizedRootRank τ a)) := by
  by_cases ha0 : a = 0
  · simp only [ha0, CFC.nnrpow_eq_pow, CFC.zero_nnrpow, map_zero,
      Complex.zero_re, ENNReal.ofReal_zero, normalizedRootRank_zero]
    exact tendsto_const_nhds
  have hexp : Tendsto (fun n : ℕ => ((((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ℝ)) atTop (𝓝 0) := by
    convert (NNReal.continuous_coe.tendsto 0).comp rootExponent_tendsto using 1
    · funext n; rfl
    · simp only [NNReal.coe_zero]
  have hfactor : Tendsto (fun n : ℕ => ‖a‖ ^ ((((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ℝ)) atTop (𝓝 1) := by
    simpa only [Real.rpow_zero] using
      ((tendsto_const_nhds (x := ‖a‖)).rpow hexp (Or.inl (norm_ne_zero_iff.mpr ha0)))
  have hroot (n : ℕ) : CFC.nnrpow a (((n : ℝ≥0) + 1)⁻¹) =
      ‖a‖ ^ ((((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ℝ) • normalizedRoot a n := by
    have hs := nnrpow_smul_real (normalizePositive a) (normalizePositive_nonneg a ha)
      ‖a‖ (norm_nonneg a) (((n : ℝ≥0) + 1)⁻¹) (by positivity)
    rwa [norm_smul_normalizePositive] at hs
  have hreal : Tendsto (fun n : ℕ => (τ.functional (CFC.nnrpow a (((n : ℝ≥0) + 1)⁻¹))).re)
      atTop (𝓝 (normalizedRootRank τ a).toReal) := by
    have ht := hfactor.mul (normalizedRoot_trace_tendsto_realRank τ a ha)
    simpa only [hroot, τ.functional.map_smul_of_tower, Complex.smul_re, smul_eq_mul, one_mul] using ht
  have hfinite : normalizedRootRank τ a ≠ ∞ :=
    ne_of_lt ((normalizedRootRank_le_one τ a ha).trans_lt ENNReal.one_lt_top)
  have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  rw [ENNReal.ofReal_toReal hfinite] at ht
  convert ht using 1
  funext n
  rfl
end CuntzPureness

end OAI
