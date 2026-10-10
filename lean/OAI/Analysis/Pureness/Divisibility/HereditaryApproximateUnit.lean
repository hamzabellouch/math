import OAI.Analysis.Pureness.Divisibility.Hereditary
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI
namespace CuntzPureness
open Filter Topology
open scoped NNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma rootExponent_tendsto :
    Tendsto (fun j : ℕ => ((j : ℝ≥0) + 1)⁻¹) atTop (𝓝 0) := by
  apply tendsto_inv_atTop_zero.comp
  have hn : Tendsto (fun j : ℕ => (j : ℝ≥0)) atTop atTop := tendsto_natCast_atTop_atTop
  exact tendsto_atTop_mono (fun j => le_add_of_nonneg_right (by positivity)) hn

lemma root_mul_uniform :
    TendstoUniformlyOn
      (fun j : ℕ => fun t : ℝ => t ^ ((((j : ℝ≥0) + 1)⁻¹ + 1 : ℝ≥0) : ℝ))
      (fun t => t) atTop (Set.Icc 0 1) := by
  apply Monotone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
  · intro j
    exact (Real.continuous_rpow_const (by positivity)).continuousOn
  · intro t ht j k hjk
    by_cases ht0 : t = 0
    · subst t
      simp only [Real.zero_rpow (by positivity :
        (((j : ℝ≥0) + 1)⁻¹ + 1 : ℝ≥0) ≠ (0 : ℝ)),
        Real.zero_rpow (by positivity :
        (((k : ℝ≥0) + 1)⁻¹ + 1 : ℝ≥0) ≠ (0 : ℝ))]
      exact le_rfl
    · apply Real.rpow_le_rpow_of_exponent_ge (lt_of_le_of_ne ht.1 (Ne.symm ht0)) ht.2
      have hi : ((k : ℝ≥0) + 1)⁻¹ ≤ ((j : ℝ≥0) + 1)⁻¹ :=
        inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hjk 1)
      exact NNReal.coe_le_coe.mpr (add_le_add hi le_rfl)
  · exact continuousOn_id
  · intro t ht
    have he : Tendsto (fun j : ℕ => ((((j : ℝ≥0) + 1)⁻¹ + 1 : ℝ≥0) : ℝ))
        atTop (𝓝 1) := by
      have hn : Tendsto (fun j : ℕ => ((j : ℝ≥0) + 1)⁻¹ + 1) atTop (𝓝 1) :=
        by simpa using rootExponent_tendsto.add_const 1
      exact (NNReal.continuous_coe.tendsto 1).comp hn
    simpa using (tendsto_const_nhds.rpow he (Or.inr zero_lt_one) :
      Tendsto (fun j : ℕ => t ^ ((((j : ℝ≥0) + 1)⁻¹ + 1 : ℝ≥0) : ℝ))
        atTop (𝓝 (t ^ (1 : ℝ))))

lemma normalizedRoot_mul_normalize_tendsto (h : A) (hh : 0 ≤ h) :
    Tendsto (fun j => normalizedRoot h j * normalizePositive h) atTop
      (𝓝 (normalizePositive h)) := by
  nontriviality A
  have hsub : quasispectrum ℝ (normalizePositive h) ⊆ Set.Icc 0 1 := by
    intro t ht
    refine ⟨quasispectrum_nonneg_of_nonneg _ (normalizePositive_nonneg h hh) _ ht, ?_⟩
    rw [quasispectrum_eq_spectrum_union_zero] at ht
    rcases ht with ht | ht
    · exact (le_abs_self t).trans ((spectrum.norm_le_norm_of_mem ht).trans
        (normalizePositive_norm_le h))
    · simpa only [Set.mem_singleton_iff.mp ht] using (zero_le_one : (0 : ℝ) ≤ 1)
  have ht := tendsto_cfcₙ_fun (a := normalizePositive h) (root_mul_uniform.mono hsub)
    (Eventually.of_forall fun j =>
      (Real.continuous_rpow_const (by positivity :
        (0 : ℝ) ≤ (((j : ℝ≥0) + 1)⁻¹ + 1 : ℝ≥0))).continuousOn)
    (Eventually.of_forall fun j => Real.zero_rpow (by positivity :
        (((j : ℝ≥0) + 1)⁻¹ + 1 : ℝ≥0) ≠ (0 : ℝ)))
  simp only [cfcₙ_id' ℝ (normalizePositive h) (normalizePositive_nonneg h hh).isSelfAdjoint] at ht
  convert ht using 1
  ext j
  rw [← CFC.nnrpow_eq_cfcₙ_real _ _ (normalizePositive_nonneg h hh), CFC.nnrpow_add (by positivity) (by positivity),
    CFC.nnrpow_one _ (normalizePositive_nonneg h hh)]
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_smul_normalizePositive (h : A) : ‖h‖ • normalizePositive h = h := by
  by_cases he : h = 0
  · simp [he]
  · simp [normalizePositive, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr he)]

lemma normalizedRoot_mul_self_tendsto (h : A) (hh : 0 ≤ h) :
    Tendsto (fun j => normalizedRoot h j * h) atTop (𝓝 h) := by
  have ht := (normalizedRoot_mul_normalize_tendsto h hh).const_smul ‖h‖
  simpa only [← mul_smul_comm, norm_smul_normalizePositive] using ht

lemma normalizedRoot_mul_hereditary_tendsto (h : A) (hh : 0 ≤ h)
    (c : A) (hc : c ∈ hereditaryCarrier h) :
    Tendsto (fun j => normalizedRoot h j * c) atTop (𝓝 c) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨d, ⟨w, rfl⟩, hd⟩ := Metric.mem_closure_iff.mp hc (ε / 4) (by positivity)
  have ht : Tendsto (fun j => normalizedRoot h j * (h * w * h)) atTop
      (𝓝 (h * w * h)) := by
    simpa only [mul_assoc] using
      ((normalizedRoot_mul_self_tendsto h hh).mul_const w).mul_const h
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp ht (ε / 2) (by positivity)
  refine ⟨J, fun j hj => ?_⟩
  have hsmall := hJ j hj
  simp only [dist_eq_norm] at hd hsmall ⊢
  have he : ‖normalizedRoot h j‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (normalizedRoot_nonneg h j)).mpr
      (normalizedRoot_le_one h hh j)
  have heq : normalizedRoot h j * c - c =
      normalizedRoot h j * (c - h * w * h) +
        (normalizedRoot h j * (h * w * h) - h * w * h) + (h * w * h - c) := by
    noncomm_ring
  rw [heq]
  calc
    _ ≤ ‖normalizedRoot h j * (c - h * w * h)‖ +
        ‖normalizedRoot h j * (h * w * h) - h * w * h‖ + ‖h * w * h - c‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖normalizedRoot h j‖ * ‖c - h * w * h‖ +
        ‖normalizedRoot h j * (h * w * h) - h * w * h‖ + ‖h * w * h - c‖ := by
      gcongr
      exact norm_mul_le _ _
    _ < ε := by
      rw [norm_sub_rev (h * w * h) c]
      nlinarith [norm_nonneg (c - h * w * h)]
end CuntzPureness

end OAI
