import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingDuhamelDuality

namespace OAI

/-! # Uniform domination for the actual dual Duhamel integrand -/

open Set MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem expandingDualDuhamelIntegrand_eq (a b k L t : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (ht : 0 ≤ t)
    (φ : 𝓢(E, ℂ)) (r : ℝ → FourierL2) (s : ℝ) :
    expandingDualDuhamelIntegrand a b k L t ha ha1 hk hL φ r s =
      expandingFourierTest a k (expandingRadius L t) ha ha1 hk
        (hL.trans (expandingRadius_ge L t hL ht)) φ
        (expandingDuhamelIntegrand a b k L ha hk hL t r s) := by
  by_cases hs : s ∈ Icc 0 t
  · simp only [expandingDualDuhamelIntegrand, dite_eq_left hs,
      expandingDuhamelIntegrand_of_mem _ _ _ _ _ _ _ _ _ _ hs]
    have h := expandingFreeStep_fourier_duality a b k (expandingRadius L s) (t - s)
      ha ha1 hk (hL.trans (expandingRadius_ge L s hL hs.1)) (sub_nonneg.mpr hs.2) φ (r s)
    simpa only [expandingDuhamel_destination] using h.symm
  · simp only [expandingDualDuhamelIntegrand, expandingDuhamelIntegrand,
      dite_eq_right hs, map_zero]

theorem integrableOn_expandingDualDuhamelIntegrand (a b k L t : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (ht : 0 ≤ t)
    (φ : 𝓢(E, ℂ)) (r : ℝ → FourierL2) (hr : ContinuousOn r (Icc 0 t)) :
    IntegrableOn (expandingDualDuhamelIntegrand a b k L t ha ha1 hk hL φ r) (Icc 0 t) := by
  have he : expandingDualDuhamelIntegrand a b k L t ha ha1 hk hL φ r =
      fun s => expandingFourierTest a k (expandingRadius L t) ha ha1 hk
        (hL.trans (expandingRadius_ge L t hL ht)) φ
        (expandingDuhamelIntegrand a b k L ha hk hL t r s) :=
    funext (expandingDualDuhamelIntegrand_eq a b k L t ha ha1 hk hL ht φ r)
  rw [he]
  exact (expandingFourierTest a k (expandingRadius L t) ha ha1 hk
    (hL.trans (expandingRadius_ge L t hL ht)) φ).integrable_comp
      (integrableOn_expandingDuhamelIntegrand a b k L ha hk hL t r hr)

theorem expandingDualDuhamelIntegrand_bound (a b k L t M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (ht : 0 ≤ t)
    (φ : 𝓢(E, ℂ)) (r : ℝ → FourierL2) (s : ℝ) (hs : s ∈ Icc 0 t)
    (hr : ‖r s‖ ≤ M) :
    ‖expandingDualDuhamelIntegrand a b k L t ha ha1 hk hL φ r s‖ ≤
      (expandingEmbeddingBound a k * SchwartzMap.seminorm ℂ 0 0 φ) * M := by
  rw [expandingDualDuhamelIntegrand_eq a b k L t ha ha1 hk hL ht,
    expandingDuhamelIntegrand_of_mem _ _ _ _ _ _ _ _ _ _ hs]
  let F := expandingFourierTest a k (expandingRadius L t) ha ha1 hk
    (hL.trans (expandingRadius_ge L t hL ht)) φ
  have hf := expandingFreeStep_norm_bound a b k (expandingRadius L s) (t - s) ha hk
    (hL.trans (expandingRadius_ge L s hL hs.1)) (sub_nonneg.mpr hs.2) (r s)
  have he : Real.exp (-a * (t - s) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hs.2])
  have hstep : ‖expandingFreeStep a b k (expandingRadius L s) (t - s) ha hk
      (hL.trans (expandingRadius_ge L s hL hs.1)) (sub_nonneg.mpr hs.2) (r s)‖ ≤ M :=
    hf.trans ((mul_le_of_le_one_left (norm_nonneg _) he).trans hr)
  exact (F.le_opNorm _).trans
    (mul_le_mul (expandingFourierTest_norm_le a k _ ha ha1 hk _ φ) hstep
      (norm_nonneg _) (by unfold expandingEmbeddingBound; positivity))

end DefocusingNLS

end OAI
