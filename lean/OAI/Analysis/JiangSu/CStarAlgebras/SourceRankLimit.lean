import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Traces.SmallTraceTransfer
import OAI.Analysis.JiangSu.CuntzSemigroup.CuntzRankMonotone
import OAI.Analysis.JiangSu.CStarAlgebras.SmoothedIntegerCuts

namespace OAI

section

namespace Pureness
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

end Pureness
end

section

namespace Pureness
open scoped ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_integer_cut_rank_approximation (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (hT : Nonempty (TracialState A))
    (p : A) (hp : 0 ≤ p) (η : ℝ) (hη : 0 < η) :
    ∃ c : A, ∃ l : ℕ, 0 ≤ c ∧ ‖c‖ < l ∧
      (∀ j, 0 ≤ positiveIntegerCut c j) ∧
      (∀ τ : TracialState A,
        0 ≤ (τ.functional p).re - ∑ j ∈ Finset.range l, (normalizedRootRank τ (positiveIntegerCut c j)).toReal ∧
        (τ.functional p).re - ∑ j ∈ Finset.range l, (normalizedRootRank τ (positiveIntegerCut c j)).toReal < η) := by
  obtain ⟨c, hc, hτ, hr⟩ := exists_arbitrarily_small_rank_trace_transfer hsimple hinf hT p hp η hη
  obtain ⟨l, hl⟩ := exists_nat_gt ‖c‖
  refine ⟨c, l, hc, hl, positiveIntegerCut_nonneg c, ?_⟩
  intro τ
  have hfinite : normalizedRootRank τ c ≠ ∞ :=
    ne_of_lt ((normalizedRootRank_le_one τ c hc).trans_lt ENNReal.one_lt_top)
  have hηr : (normalizedRootRank τ c).toReal < η := by
    have h := (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mpr (hr τ)
    simpa only [ENNReal.toReal_ofReal hη.le] using h
  have hb := actual_spectral_integer_approximation τ c hc l hl.le
  rw [hτ τ] at hb
  exact ⟨hb.1, hb.2.trans_lt hηr⟩

end Pureness
end

end OAI
