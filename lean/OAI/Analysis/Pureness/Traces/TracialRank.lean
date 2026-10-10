import OAI.Analysis.Pureness.Traces.TracialStates
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence

namespace OAI
namespace CuntzPureness
open scoped ComplexOrder ENNReal NNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

noncomputable def normalizePositive (a : A) : A := ‖a‖⁻¹ • a

lemma normalizePositive_nonneg (a : A) (ha : 0 ≤ a) : 0 ≤ normalizePositive a :=
  smul_nonneg (inv_nonneg.mpr (norm_nonneg a)) ha

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma normalizePositive_zero : normalizePositive (0 : A) = 0 := by
  simp [normalizePositive]

omit [PartialOrder A] [StarOrderedRing A] in
lemma normalizePositive_norm_le (a : A) : ‖normalizePositive a‖ ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha]
  · simp [normalizePositive, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha)]

omit [PartialOrder A] [StarOrderedRing A] in
lemma normalizePositive_smul (a : A) (t : ℝ) (ht : 0 < t) :
    normalizePositive (t • a) = normalizePositive a := by
  simp only [normalizePositive, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
    smul_smul, mul_inv_rev]
  rw [mul_assoc, inv_mul_cancel₀ ht.ne', mul_one]

noncomputable def normalizedRoot (a : A) (j : ℕ) : A :=
  CFC.nnrpow (normalizePositive a) (((j : ℝ≥0) + 1)⁻¹)

noncomputable def normalizedRootRank (τ : TracialState A) (a : A) : ℝ≥0∞ :=
  ⨆ j : ℕ, ENNReal.ofReal (τ.functional (normalizedRoot a j)).re

lemma normalizedRoot_nonneg (a : A) (j : ℕ) : 0 ≤ normalizedRoot a j := CFC.nnrpow_nonneg

lemma normalizedRoot_le_one (a : A) (ha : 0 ≤ a) (j : ℕ) : normalizedRoot a j ≤ 1 := by
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (normalizedRoot_nonneg a j)).mp
  unfold normalizedRoot
  rw [CFC.nnrpow_eq_pow, CFC.norm_nnrpow _ (by positivity) (normalizePositive_nonneg a ha)]
  exact Real.rpow_le_one (norm_nonneg _) (normalizePositive_norm_le a) (by positivity)

lemma normalizedRootRank_le_one (τ : TracialState A) (a : A) (ha : 0 ≤ a) :
    normalizedRootRank τ a ≤ 1 := by
  apply iSup_le
  intro j
  have h : τ.functional (normalizedRoot a j) ≤ τ.functional 1 :=
    τ.functional.monotone (normalizedRoot_le_one a ha j)
  rw [τ.normalized] at h
  apply ENNReal.ofReal_le_one.mpr
  exact (Complex.le_def.mp h).1

lemma normalizedRootRank_smul (τ : TracialState A) (a : A) (t : ℝ) (ht : 0 < t) :
    normalizedRootRank τ (t • a) = normalizedRootRank τ a := by
  simp only [normalizedRootRank, normalizedRoot, normalizePositive_smul a t ht]

lemma normalized_trace_le_rank (τ : TracialState A) (a : A) (ha : 0 ≤ a) :
    ENNReal.ofReal (τ.functional (normalizePositive a)).re ≤ normalizedRootRank τ a := by
  have h := le_iSup (fun j : ℕ => ENNReal.ofReal (τ.functional (normalizedRoot a j)).re) 0
  simpa [normalizedRootRank, normalizedRoot, CFC.nnrpow_one _ (normalizePositive_nonneg a ha)] using h

lemma normalizedRoot_monotone (a : A) (ha : 0 ≤ a) : Monotone (normalizedRoot a) := by
  intro j k hjk
  have hjpos : 0 < ((j : ℝ≥0) + 1)⁻¹ := by positivity
  have hkpos : 0 < ((k : ℝ≥0) + 1)⁻¹ := by positivity
  have hexp : ((k : ℝ≥0) + 1)⁻¹ ≤ ((j : ℝ≥0) + 1)⁻¹ := by
    apply inv_anti₀ (by positivity)
    exact_mod_cast Nat.add_le_add_right hjk 1
  simp only [normalizedRoot, CFC.nnrpow_eq_pow, CFC.nnrpow_def]
  apply cfcₙ_mono
  · intro z hz
    have hz1 : z ≤ 1 :=
      (NonUnitalIsometricContinuousFunctionalCalculus.quasispectrum_le _ hz
        (normalizePositive_nonneg a ha)).trans (by exact_mod_cast normalizePositive_norm_le a)
    by_cases hz0 : z = 0
    · subst z
      change (0 : ℝ≥0) ^ (((j : ℝ≥0) + 1)⁻¹ : ℝ) ≤
        (0 : ℝ≥0) ^ (((k : ℝ≥0) + 1)⁻¹ : ℝ)
      rw [NNReal.zero_rpow (by exact_mod_cast (ne_of_gt hjpos)),
        NNReal.zero_rpow (by exact_mod_cast (ne_of_gt hkpos))]
    · apply NNReal.rpow_le_rpow_of_exponent_ge (pos_iff_ne_zero.mpr hz0) hz1
      exact_mod_cast hexp
  · exact (NNReal.continuous_nnrpow_const _).continuousOn
  · exact (NNReal.continuous_nnrpow_const _).continuousOn
  · exact NNReal.zero_rpow (by exact_mod_cast (ne_of_gt hjpos))
  · exact NNReal.zero_rpow (by exact_mod_cast (ne_of_gt hkpos))

lemma normalizedRootRank_tendsto (τ : TracialState A) (a : A) (ha : 0 ≤ a) :
    Filter.Tendsto (fun j : ℕ => ENNReal.ofReal (τ.functional (normalizedRoot a j)).re)
      Filter.atTop (nhds (normalizedRootRank τ a)) := by
  apply tendsto_atTop_iSup
  intro j k hjk
  apply ENNReal.ofReal_le_ofReal
  exact (Complex.le_def.mp (τ.functional.monotone (normalizedRoot_monotone a ha hjk))).1

lemma normalizedRootRank_pos (τ : TracialState A) (hsimple : TopologicallySimple A)
    (a : A) (ha : 0 ≤ a) (hne : a ≠ 0) : 0 < normalizedRootRank τ a := by
  have hn : normalizePositive a ≠ 0 :=
    smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hne)) hne
  have hτn : τ.functional (normalizePositive a) ≠ 0 := by
    intro hzero
    exact hn (τ.faithful hsimple _ (normalizePositive_nonneg a ha) hzero)
  have hτpos : 0 < τ.functional (normalizePositive a) :=
    lt_of_le_of_ne (τ.functional.map_nonneg (normalizePositive_nonneg a ha)) hτn.symm
  have hreal : 0 < (τ.functional (normalizePositive a)).re := (Complex.pos_iff.mp hτpos).1
  exact (ENNReal.ofReal_pos.mpr hreal).trans_le (normalized_trace_le_rank τ a ha)
end CuntzPureness

end OAI
