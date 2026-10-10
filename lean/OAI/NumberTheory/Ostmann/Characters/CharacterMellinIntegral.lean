import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Analytic.Uniqueness
import OAI.NumberTheory.Ostmann.Characters.CharacterRightHalfPlane

namespace OAI

/-! # The bounded-prefix Mellin representation on Re(s)>0 -/

namespace Ostmann

open MeasureTheory Filter Set
open scoped Classical BigOperators Topology

noncomputable def characterSummatory (χ : PrimitiveComplexCharacter) (t : ℝ) : ℂ :=
  (Ioi (1 : ℝ)).indicator
    (fun t => ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ.character (n : ZMod χ.modulus)) t

theorem characterSummatory_zero (χ : PrimitiveComplexCharacter) {t : ℝ} (ht : t ≤ 1) :
    characterSummatory χ t = 0 := by simp [characterSummatory, not_lt.mpr ht]

theorem characterSummatory_bound (χ : PrimitiveComplexCharacter) (t : ℝ) :
    ‖characterSummatory χ t‖ ≤ χ.modulus + 1 := by
  by_cases ht : 1 < t
  · simpa [characterSummatory, ht] using χ.prefix_Icc_bound ⌊t⌋₊
  · rw [characterSummatory_zero χ (le_of_not_gt ht), norm_zero]
    positivity

theorem characterSummatory_locallyIntegrable (χ : PrimitiveComplexCharacter) :
    LocallyIntegrableOn (characterSummatory χ) (Ioi 0) := by
  intro t ht
  change 0 < t at ht
  refine ⟨Icc (t / 2) (t + 1), nhdsWithin_le_nhds
    (Icc_mem_nhds (by linarith) (by linarith)), ?_⟩
  have hi := integrableOn_mul_sum_Icc
    (fun n => χ.character (n : ZMod χ.modulus)) (m := 1)
    (show 0 ≤ t / 2 by linarith) (b := t + 1)
    (show IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Icc (t / 2) (t + 1)) from
      continuousOn_const.integrableOn_Icc)
  simp only [one_mul] at hi
  exact hi.indicator measurableSet_Ioi

theorem characterSummatory_bigO (χ : PrimitiveComplexCharacter) :
    characterSummatory χ =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  apply Asymptotics.IsBigO.of_bound (χ.modulus + 1 : ℝ)
  filter_upwards with t
  simpa using characterSummatory_bound χ t

theorem characterSummatory_zero_bigO (χ : PrimitiveComplexCharacter) (b : ℝ) :
    characterSummatory χ =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
  apply Asymptotics.IsBigO.of_bound 0
  filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
    nhdsWithin_le_nhds] with t ht
  simp [characterSummatory_zero χ ht.le]

theorem characterSummatory_mellin (χ : PrimitiveComplexCharacter) (s : ℂ) :
    mellin (characterSummatory χ) (-s) = ∫ t in Ioi (1 : ℝ),
      (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ.character (n : ZMod χ.modulus)) *
        (t : ℂ) ^ (-(s + 1)) := by
  let F : ℝ → ℂ := fun t => (t : ℂ) ^ (-s - 1) * characterSummatory χ t
  have hF (t : ℝ) (ht : t ≤ 1) : F t = 0 := by
    simp [F, characterSummatory_zero χ ht]
  change (∫ t in Ioi (0 : ℝ), F t) = _
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => hF t (by
    simp only [mem_Ioi, not_lt] at ht; linarith))]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Ioi (1 : ℝ)) (fun t ht => hF t (le_of_not_gt ht))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [F, characterSummatory, indicator_of_mem ht]
  rw [show -s - 1 = -(s + 1) by ring]
  exact mul_comm _ _

noncomputable def characterMellinL (χ : PrimitiveComplexCharacter) (s : ℂ) : ℂ :=
  s * mellin (characterSummatory χ) (-s)

theorem characterMellinL_differentiableAt (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : 0 < s.re) : DifferentiableAt ℂ (characterMellinL χ) s := by
  have hm := mellin_differentiableAt_of_isBigO_rpow
    (characterSummatory_locallyIntegrable χ) (characterSummatory_bigO χ)
    (s := -s) (by simpa using neg_neg_of_pos hs)
    (characterSummatory_zero_bigO χ (-s.re - 1)) (by simp)
  exact differentiableAt_id.mul (hm.comp s differentiableAt_id.neg)

theorem characterMellinL_eq_L (χ : PrimitiveComplexCharacter) (s : ℂ) (hs : 0 < s.re) :
    characterMellinL χ s = χ.L s := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ (characterMellinL χ) {s : ℂ | 0 < s.re} :=
    (show DifferentiableOn ℂ (characterMellinL χ) {s : ℂ | 0 < s.re} from
      fun s hs => (characterMellinL_differentiableAt χ s hs).differentiableWithinAt).analyticOnNhd hopen
  have hg : AnalyticOnNhd ℂ χ.L {s : ℂ | 0 < s.re} :=
    (DirichletCharacter.differentiable_LFunction χ.nontrivial).differentiableOn.analyticOnNhd hopen
  have he : characterMellinL χ =ᶠ[𝓝 (2 : ℂ)] χ.L := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by norm_num)] with z hz
    rw [characterMellinL, characterSummatory_mellin, χ.L_integral_right z hz]
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg
    (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected (by norm_num : (2 : ℂ) ∈ {s : ℂ | 0 < s.re})
    he hs

end Ostmann

end OAI
