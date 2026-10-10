import OAI.NumberTheory.TwoPoint.Fourier.ModFiveAbelBounds
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Convex.Topology

namespace OAI

/-! Continue the bounded-partial-sum Abel integral to `re s > 0`.

The Mellin differentiation theorem gives holomorphy without differentiating
an improperly convergent Dirichlet series. The identity principle then
identifies it with the existing entire Dirichlet L-function. In particular
each of the three modulus-five functions has a uniform linear growth bound
on `re s ≥ 1/2`.
-/

namespace TwoPointCorrelations

open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology

noncomputable def modFiveAbelInput (χ : DirichletCharacter ℂ 5) : ℝ → ℂ :=
  (Set.Ioi (1 : ℝ)).indicator (modFiveSummatory χ)

lemma modFiveAbelInput_measurable (χ : DirichletCharacter ℂ 5) :
    Measurable (modFiveAbelInput χ) :=
  (modFiveSummatory_measurable χ).indicator measurableSet_Ioi

lemma modFiveAbelInput_norm (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1) (t : ℝ) :
    ‖modFiveAbelInput χ t‖ ≤ 4 := by
  by_cases ht : 1 < t
  · simpa only [modFiveAbelInput, Set.mem_Ioi, Set.indicator_apply, ite_eq_left ht] using
      modFiveSummatory_norm χ hχ t
  · simp only [modFiveAbelInput, Set.mem_Ioi, Set.indicator_apply, ite_eq_right ht, norm_zero]
    norm_num

lemma modFiveAbelInput_locallyIntegrable (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1) :
    LocallyIntegrableOn (modFiveAbelInput χ) (Set.Ioi (0 : ℝ)) := by
  refine (locallyIntegrableOn_const (s := Set.Ioi (0 : ℝ)) (4 : ℝ)).mono
    (modFiveAbelInput_measurable χ).aestronglyMeasurable ?_
  exact Eventually.of_forall fun t => by simpa using modFiveAbelInput_norm χ hχ t

lemma modFiveAbelInput_bigO_atTop (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1) :
    modFiveAbelInput χ =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  refine IsBigO.of_bound 4 (Eventually.of_forall fun t => ?_)
  simpa only [neg_zero, Real.rpow_zero, norm_one, mul_one] using modFiveAbelInput_norm χ hχ t

lemma modFiveAbelInput_bigO_zero (χ : DirichletCharacter ℂ 5) (b : ℝ) :
    modFiveAbelInput χ =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-b)) := by
  refine IsBigO.of_bound 0 ?_
  filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
    nhdsWithin_le_nhds] with t ht
  have hnot : t ∉ Set.Ioi (1 : ℝ) := by change ¬1 < t; linarith
  simp only [modFiveAbelInput, Set.indicator_of_notMem hnot, norm_zero, zero_mul, le_refl]

lemma modFiveAbelIntegral_eq_mellin (χ : DirichletCharacter ℂ 5) (s : ℂ) :
    modFiveAbelIntegral χ s = s * mellin (modFiveAbelInput χ) (-s) := by
  unfold modFiveAbelIntegral mellin
  congr 1
  have heq : (fun t : ℝ => (t : ℂ) ^ (-s - 1) • modFiveAbelInput χ t) =
      (Set.Ioi (1 : ℝ)).indicator (modFiveAbelKernel χ s) := by
    funext t
    by_cases ht : 1 < t
    · simp only [modFiveAbelInput, Set.indicator_apply, Set.mem_Ioi, ite_eq_left ht,
        smul_eq_mul, modFiveAbelKernel]
      rw [show -s - 1 = -(s + 1) by ring, mul_comm]
    · have hn : t ∉ Set.Ioi (1 : ℝ) := ht
      simp only [modFiveAbelInput, Set.indicator_of_notMem hn, smul_zero]
  rw [heq, setIntegral_indicator measurableSet_Ioi]
  rw [Set.inter_eq_right.mpr (show Set.Ioi (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) from
    fun t ht => lt_trans (show (0 : ℝ) < 1 from zero_lt_one) ht)]

theorem modFiveAbelIntegral_differentiableAt (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ (modFiveAbelIntegral χ) s := by
  have hm : DifferentiableAt ℂ (mellin (modFiveAbelInput χ)) (-s) := by
    apply mellin_differentiableAt_of_isBigO_rpow
      (modFiveAbelInput_locallyIntegrable χ hχ) (modFiveAbelInput_bigO_atTop χ hχ)
      (b := -s.re - 1)
    · simpa only [Complex.neg_re] using neg_neg_of_pos hs
    · exact modFiveAbelInput_bigO_zero χ _
    · simp only [Complex.neg_re]
      linarith
  have heq : modFiveAbelIntegral χ = fun z => z * mellin (modFiveAbelInput χ) (-z) :=
    funext (modFiveAbelIntegral_eq_mellin χ)
  rw [heq]
  exact differentiableAt_id.mul (hm.comp s differentiableAt_id.neg)

/-- The bounded-partial-sum integral is the existing L-function on the
entire half-plane of convergence of that integral. -/
theorem modFiveAbelIntegral_eq_LFunction_of_pos (χ : DirichletCharacter ℂ 5)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    modFiveAbelIntegral χ s = DirichletCharacter.LFunction χ s := by
  let U : Set ℂ := {z | 0 < z.re}
  have ho : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hc : Convex ℝ U := (convex_Ioi (0 : ℝ)).linear_preimage Complex.reLm
  have hF : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) U :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd ho
  have hG : AnalyticOnNhd ℂ (modFiveAbelIntegral χ) U := by
    apply DifferentiableOn.analyticOnNhd _ ho
    intro z hz
    exact (modFiveAbelIntegral_differentiableAt χ hχ hz).differentiableWithinAt
  have heq : DirichletCharacter.LFunction χ =ᶠ[𝓝 (2 : ℂ)] modFiveAbelIntegral χ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show 1 < (2 : ℂ).re by norm_num)] with z hz
    exact (modFiveAbelIntegral_eq_LFunction χ hχ hz).symm
  exact (hF.eqOn_of_preconnected_of_eventuallyEq hG hc.isPreconnected
    (show (2 : ℂ) ∈ U by change 0 < (2 : ℂ).re; norm_num) heq hs).symm

theorem modFive_LFunction_norm_le (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 4 * ‖s‖ / s.re := by
  rw [← modFiveAbelIntegral_eq_LFunction_of_pos χ hχ hs]
  exact modFiveAbelIntegral_norm χ hχ hs

theorem modFive_LFunction_norm_halfPlane (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1)
    {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 8 * ‖s‖ := by
  have hs0 : 0 < s.re := by linarith
  apply (modFive_LFunction_norm_le χ hχ hs0).trans
  apply (div_le_iff₀ hs0).mpr
  nlinarith [norm_nonneg s]

end TwoPointCorrelations

end OAI
