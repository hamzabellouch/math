import OAI.Analysis.KadisonKastler.KaplanskyResolvent
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

/-! # A bounded rational transform of self-adjoint operators

The scalar map `2t/(1+t²)` takes the real line into the closed unit interval.
Its inverse on that interval is `t/(1+sqrt(1-t²))`. Resolvent continuity
therefore gives bounded strong approximants to any self-adjoint contraction.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

def kaplanskyTransform (t : ℝ) : ℝ := 2 * t / (1 + t ^ 2)

def kaplanskyInverse (t : ℝ) : ℝ := t / (1 + Real.sqrt (1 - t ^ 2))

theorem continuous_kaplanskyTransform : Continuous kaplanskyTransform := by
  unfold kaplanskyTransform
  fun_prop (disch := intro t; positivity)

theorem continuous_kaplanskyInverse : Continuous kaplanskyInverse := by
  unfold kaplanskyInverse
  fun_prop (disch := intro t; positivity)

theorem abs_kaplanskyTransform_le_one (t : ℝ) : |kaplanskyTransform t| ≤ 1 := by
  have hd : 0 < 1 + t ^ 2 := by positivity
  unfold kaplanskyTransform
  rw [abs_le]
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith [sq_nonneg (t + 1)]
  · apply (div_le_iff₀ hd).mpr
    nlinarith [sq_nonneg (t - 1)]

theorem kaplanskyTransform_inverse {t : ℝ} (ht : |t| ≤ 1) :
    kaplanskyTransform (kaplanskyInverse t) = t := by
  have ht₂ : t ^ 2 ≤ 1 := by
    rcases abs_le.mp ht with ⟨hl, hu⟩
    nlinarith
  have hs : (Real.sqrt (1 - t ^ 2)) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by linarith)
  have hd : 1 + Real.sqrt (1 - t ^ 2) ≠ 0 := by positivity
  unfold kaplanskyTransform kaplanskyInverse
  apply (div_eq_iff (by positivity : (1 : ℝ) + (t / (1 + Real.sqrt (1 - t ^ 2))) ^ 2 ≠ 0)).mpr
  field_simp
  linear_combination -t * hs

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The rational transform stays in the unit ball. -/
theorem norm_kaplanskyTransform_le_one (a : H →L[ℂ] H) :
    ‖cfc kaplanskyTransform a‖ ≤ 1 := by
  apply norm_cfc_le (by norm_num)
  intro t _
  simpa only [Real.norm_eq_abs] using abs_kaplanskyTransform_le_one t

/-- Every self-adjoint contraction is the rational transform of a
self-adjoint operator. No spectral or density input is assumed. -/
theorem exists_kaplanskyTransform_preimage (T : H →L[ℂ] H)
    (hT : IsSelfAdjoint T) (hn : ‖T‖ ≤ 1) :
    ∃ S : H →L[ℂ] H, S = cfc kaplanskyInverse T ∧
      IsSelfAdjoint S ∧ cfc kaplanskyTransform S = T := by
  let S := cfc kaplanskyInverse T
  refine ⟨S, rfl, cfc_predicate kaplanskyInverse T, ?_⟩
  dsimp [S]
  rw [← cfc_comp kaplanskyTransform kaplanskyInverse T hT
    continuous_kaplanskyTransform.continuousOn continuous_kaplanskyInverse.continuousOn]
  calc
    cfc (kaplanskyTransform ∘ kaplanskyInverse) T = cfc (id : ℝ → ℝ) T := by
      apply cfc_congr
      intro t ht
      have htn : |t| ≤ ‖T‖ := by
        simpa only [Real.norm_eq_abs] using
          IsometricContinuousFunctionalCalculus.norm_spectrum_le T ht hT
      exact kaplanskyTransform_inverse (htn.trans hn)
    _ = T := cfc_id ℝ T hT

end

end KadisonKastler

end OAI
