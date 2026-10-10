import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Algebra.Support

namespace OAI

/-! Smooth scalar truncations vanish near the zero trace and converge to
positive inputs with a derivative bound independent of the scale. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def smoothTraceTruncation (δ : ℝ) (t : ℝ) : ℝ :=
  t * Real.smoothTransition (t / δ - 1)

 theorem smoothTraceTruncation_contDiff (δ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothTraceTruncation δ) :=
  contDiff_id.mul (Real.smoothTransition.contDiff.comp
    ((contDiff_id.div_const δ).sub contDiff_const))

 theorem smoothTraceTruncation_zero {δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ δ) :
    smoothTraceTruncation δ t = 0 := by
  unfold smoothTraceTruncation
  rw [Real.smoothTransition.zero_of_nonpos (by
    have h := (div_le_one hδ).mpr ht
    linarith), mul_zero]

 theorem smoothTraceTruncation_eq_self {δ t : ℝ} (hδ : 0 < δ) (ht : 2 * δ ≤ t) :
    smoothTraceTruncation δ t = t := by
  unfold smoothTraceTruncation
  rw [Real.smoothTransition.one_of_one_le (by
    have h : 2 ≤ t / δ := (le_div_iff₀ hδ).mpr ht
    linarith), mul_one]

 theorem smoothTransition_deriv_zero_left {t : ℝ} (ht : t ≤ 0) :
    deriv Real.smoothTransition t = 0 := by
  apply IsLocalMin.deriv_eq_zero
  apply Eventually.of_forall
  intro x
  rw [Real.smoothTransition.zero_of_nonpos ht]
  exact Real.smoothTransition.nonneg x

 theorem smoothTransition_deriv_zero_right {t : ℝ} (ht : 1 ≤ t) :
    deriv Real.smoothTransition t = 0 := by
  apply IsLocalMax.deriv_eq_zero
  apply Eventually.of_forall
  intro x
  rw [Real.smoothTransition.one_of_one_le ht]
  exact Real.smoothTransition.le_one x

 theorem smoothTraceTruncation_deriv (δ t : ℝ) :
    deriv (smoothTraceTruncation δ) t = Real.smoothTransition (t / δ - 1) +
      (t / δ) * deriv Real.smoothTransition (t / δ - 1) := by
  have hs := (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
  have ht := (hasDerivAt_id t).div_const δ
  have he := (hasDerivAt_id t).mul ((hs _).hasDerivAt.comp t (ht.sub_const 1))
  change HasDerivAt (smoothTraceTruncation δ)
    (1 * Real.smoothTransition (t / δ - 1) + t * (deriv Real.smoothTransition (t / δ - 1) * (1 / δ))) t at he
  rw [he.deriv]
  ring

 theorem smoothTraceTruncation_deriv_zero {δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ δ) :
    deriv (smoothTraceTruncation δ) t = 0 := by
  have h : t / δ - 1 ≤ 0 := by have := (div_le_one hδ).mpr ht; linarith
  rw [smoothTraceTruncation_deriv, Real.smoothTransition.zero_of_nonpos h,
    smoothTransition_deriv_zero_left h]
  ring

 theorem smoothTraceTruncation_deriv_one {δ t : ℝ} (hδ : 0 < δ) (ht : 2 * δ ≤ t) :
    deriv (smoothTraceTruncation δ) t = 1 := by
  have h : 1 ≤ t / δ - 1 := by
    have : 2 ≤ t / δ := (le_div_iff₀ hδ).mpr ht
    linarith
  rw [smoothTraceTruncation_deriv, Real.smoothTransition.one_of_one_le h,
    smoothTransition_deriv_zero_right h]
  ring

 theorem smoothTraceTruncation_mem {δ t : ℝ} (ht : 0 ≤ t) :
    smoothTraceTruncation δ t ∈ Icc 0 t := by
  exact ⟨mul_nonneg ht (Real.smoothTransition.nonneg _),
    (mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one _) ht).trans_eq (mul_one t)⟩

 theorem smoothTraceTruncation_uniform_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → ∀ t : ℝ,
      ‖deriv (smoothTraceTruncation δ) t‖ ≤ C := by
  obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    ((Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl).continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp))
  refine ⟨1 + 2 * M, by positivity, ?_⟩
  intro δ hδ t
  by_cases hlo : t ≤ δ
  · rw [smoothTraceTruncation_deriv_zero hδ hlo, norm_zero]
    positivity
  by_cases hhi : 2 * δ ≤ t
  · rw [smoothTraceTruncation_deriv_one hδ hhi, norm_one]
    linarith
  have hr : t / δ - 1 ∈ Icc (0 : ℝ) 1 := by
    constructor
    · have : 1 < t / δ := (one_lt_div hδ).mpr (lt_of_not_ge hlo)
      linarith
    · have : t / δ < 2 := (div_lt_iff₀ hδ).mpr (lt_of_not_ge hhi)
      linarith
  have ht0 : 0 ≤ t / δ := by linarith [hr.1]
  have ht2 : t / δ ≤ 2 := by linarith [hr.2]
  rw [smoothTraceTruncation_deriv]
  calc
    _ ≤ ‖Real.smoothTransition (t / δ - 1)‖ +
      ‖(t / δ) * deriv Real.smoothTransition (t / δ - 1)‖ := norm_add_le _ _
    _ ≤ 1 + 2 * M := by
      rw [norm_mul, Real.norm_eq_abs (t / δ), abs_of_nonneg ht0]
      gcongr
      · rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
        exact Real.smoothTransition.le_one _
      · exact hM _ hr

end CircleDomainRigidity

end

end OAI
