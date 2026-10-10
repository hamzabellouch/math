import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterAbel
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Convex.Topology

namespace OAI

/-! The nonprincipal character Abel integral agrees with the existing
L-function throughout re(s)>0, with explicit modulus dependence. -/

namespace TwoPointCorrelations

open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology

variable {q : ℕ} [NeZero q]

noncomputable def mrtCharacterAbelInput (χ : DirichletCharacter ℂ q) : ℝ → ℂ :=
  (Set.Ioi (1 : ℝ)).indicator (mrtCharacterSummatory χ)

omit [NeZero q] in
lemma mrtCharacterAbelInput_measurable (χ : DirichletCharacter ℂ q) :
    Measurable (mrtCharacterAbelInput χ) :=
  (mrtCharacterSummatory_measurable χ).indicator measurableSet_Ioi

lemma mrtCharacterAbelInput_norm (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) :
    ‖mrtCharacterAbelInput χ t‖ ≤ (q : ℝ) := by
  by_cases ht : 1 < t
  · simpa only [mrtCharacterAbelInput, Set.mem_Ioi, Set.indicator_apply, ite_eq_left ht] using
      mrtCharacterSummatory_norm χ hχ t
  · simp only [mrtCharacterAbelInput, Set.mem_Ioi, Set.indicator_apply, ite_eq_right ht, norm_zero]
    exact Nat.cast_nonneg q

lemma mrtCharacterAbelInput_locallyIntegrable (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    LocallyIntegrableOn (mrtCharacterAbelInput χ) (Set.Ioi (0 : ℝ)) := by
  refine (locallyIntegrableOn_const (s := Set.Ioi (0 : ℝ)) (q : ℝ)).mono
    (mrtCharacterAbelInput_measurable χ).aestronglyMeasurable ?_
  exact Eventually.of_forall fun t => by simpa using mrtCharacterAbelInput_norm χ hχ t

lemma mrtCharacterAbelInput_bigO_atTop (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    mrtCharacterAbelInput χ =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  refine IsBigO.of_bound (q : ℝ) (Eventually.of_forall fun t => ?_)
  simpa only [neg_zero, Real.rpow_zero, norm_one, mul_one] using mrtCharacterAbelInput_norm χ hχ t

omit [NeZero q] in
lemma mrtCharacterAbelInput_bigO_zero (χ : DirichletCharacter ℂ q) (b : ℝ) :
    mrtCharacterAbelInput χ =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-b)) := by
  refine IsBigO.of_bound 0 ?_
  filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
    nhdsWithin_le_nhds] with t ht
  have hnot : t ∉ Set.Ioi (1 : ℝ) := by change ¬1 < t; linarith
  simp only [mrtCharacterAbelInput, Set.indicator_of_notMem hnot, norm_zero, zero_mul, le_refl]

omit [NeZero q] in
lemma mrtCharacterAbelIntegral_eq_mellin (χ : DirichletCharacter ℂ q) (s : ℂ) :
    mrtCharacterAbelIntegral χ s = s * mellin (mrtCharacterAbelInput χ) (-s) := by
  unfold mrtCharacterAbelIntegral mellin
  congr 1
  have heq : (fun t : ℝ => (t : ℂ) ^ (-s - 1) • mrtCharacterAbelInput χ t) =
      (Set.Ioi (1 : ℝ)).indicator (mrtCharacterAbelKernel χ s) := by
    funext t
    by_cases ht : 1 < t
    · simp only [mrtCharacterAbelInput, Set.indicator_apply, Set.mem_Ioi, ite_eq_left ht,
        smul_eq_mul, mrtCharacterAbelKernel]
      rw [show -s - 1 = -(s + 1) by ring, mul_comm]
    · have hn : t ∉ Set.Ioi (1 : ℝ) := ht
      simp only [mrtCharacterAbelInput, Set.indicator_of_notMem hn, smul_zero]
  rw [heq, setIntegral_indicator measurableSet_Ioi]
  rw [Set.inter_eq_right.mpr (show Set.Ioi (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) from
    fun t ht => lt_trans (show (0 : ℝ) < 1 from zero_lt_one) ht)]

theorem mrtCharacterAbelIntegral_differentiableAt (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ (mrtCharacterAbelIntegral χ) s := by
  have hm : DifferentiableAt ℂ (mellin (mrtCharacterAbelInput χ)) (-s) := by
    apply mellin_differentiableAt_of_isBigO_rpow
      (mrtCharacterAbelInput_locallyIntegrable χ hχ) (mrtCharacterAbelInput_bigO_atTop χ hχ)
      (b := -s.re - 1)
    · simpa only [Complex.neg_re] using neg_neg_of_pos hs
    · exact mrtCharacterAbelInput_bigO_zero χ _
    · simp only [Complex.neg_re]
      linarith
  have heq : mrtCharacterAbelIntegral χ = fun z => z * mellin (mrtCharacterAbelInput χ) (-z) :=
    funext (mrtCharacterAbelIntegral_eq_mellin χ)
  rw [heq]
  exact differentiableAt_id.mul (hm.comp s differentiableAt_id.neg)

/-- The bounded-partial-sum integral is the existing L-function on the
entire half-plane of convergence of that integral. -/
theorem mrtCharacterAbelIntegral_eq_LFunction_of_pos (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    mrtCharacterAbelIntegral χ s = DirichletCharacter.LFunction χ s := by
  let U : Set ℂ := {z | 0 < z.re}
  have ho : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hc : Convex ℝ U := (convex_Ioi (0 : ℝ)).linear_preimage Complex.reLm
  have hF : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) U :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd ho
  have hG : AnalyticOnNhd ℂ (mrtCharacterAbelIntegral χ) U := by
    apply DifferentiableOn.analyticOnNhd _ ho
    intro z hz
    exact (mrtCharacterAbelIntegral_differentiableAt χ hχ hz).differentiableWithinAt
  have heq : DirichletCharacter.LFunction χ =ᶠ[𝓝 (2 : ℂ)] mrtCharacterAbelIntegral χ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show 1 < (2 : ℂ).re by norm_num)] with z hz
    exact (mrtCharacterAbelIntegral_eq_LFunction χ hχ hz).symm
  exact (hF.eqOn_of_preconnected_of_eventuallyEq hG hc.isPreconnected
    (show (2 : ℂ) ∈ U by change 0 < (2 : ℂ).re; norm_num) heq hs).symm

theorem mrt_character_LFunction_norm_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ (q : ℝ) * ‖s‖ / s.re := by
  rw [← mrtCharacterAbelIntegral_eq_LFunction_of_pos χ hχ hs]
  exact mrtCharacterAbelIntegral_norm χ hχ hs

theorem mrt_character_LFunction_norm_halfPlane (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ (2 * q : ℝ) * ‖s‖ := by
  have hs0 : 0 < s.re := by linarith
  calc
    _ ≤ (q : ℝ) * ‖s‖ / s.re := mrt_character_LFunction_norm_le χ hχ hs0
    _ ≤ (q : ℝ) * ‖s‖ / (1/2) :=
      div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg q) (norm_nonneg s))
        (by norm_num) hs
    _ = _ := by ring

end TwoPointCorrelations

end OAI
