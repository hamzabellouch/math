import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFreeDuality
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingDuhamel

namespace OAI

/-! # The exact Schwartz-tested variation-of-constants formula -/

open Set MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def expandingDualDuhamelIntegrand (a b k L t : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (φ : 𝓢(E, ℂ)) (r : ℝ → FourierL2) (τ : ℝ) : ℂ :=
  if h : τ ∈ Icc 0 t then
    expandingFourierTest a k (expandingRadius L τ) ha ha1 hk
      (hL.trans (expandingRadius_ge L τ hL h.1))
      (homogeneousFreeDualTest a b (t - τ) φ) (r τ)
  else 0

theorem expandingDuhamel_fourier_duality (a b k L t : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (ht : 0 ≤ t)
    (φ : 𝓢(E, ℂ)) (r : ℝ → FourierL2) (hr : ContinuousOn r (Icc 0 t)) :
    expandingFourierTest a k (expandingRadius L t) ha ha1 hk
        (hL.trans (expandingRadius_ge L t hL ht)) φ
        (expandingDuhamel a b k L ha hk hL t r) =
      ∫ τ in Icc 0 t, expandingDualDuhamelIntegrand a b k L t ha ha1 hk hL φ r τ := by
  let F := expandingFourierTest a k (expandingRadius L t) ha ha1 hk
    (hL.trans (expandingRadius_ge L t hL ht)) φ
  have hI := integrableOn_expandingDuhamelIntegrand a b k L ha hk hL t r hr
  calc
    _ = ∫ τ in Icc 0 t, F (expandingDuhamelIntegrand a b k L ha hk hL t r τ) :=
      (F.integral_comp_comm hI).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      simp only [expandingDuhamelIntegrand_of_mem _ _ _ _ _ _ _ _ _ _ hτ,
        expandingDualDuhamelIntegrand, dite_eq_left hτ]
      have h := expandingFreeStep_fourier_duality a b k (expandingRadius L τ) (t - τ)
        ha ha1 hk (hL.trans (expandingRadius_ge L τ hL hτ.1))
        (sub_nonneg.mpr hτ.2) φ (r τ)
      simpa only [expandingDuhamel_destination, F] using h

theorem expandingMild_fourier_duality (a b k L t : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (ht : 0 ≤ t)
    (φ : 𝓢(E, ℂ)) (f u : FourierL2) (r : ℝ → FourierL2)
    (hr : ContinuousOn r (Icc 0 t))
    (hu : u = expandingFreeStep a b k L t ha hk hL ht f +
      expandingDuhamel a b k L ha hk hL t r) :
    expandingFourierTest a k (expandingRadius L t) ha ha1 hk
        (hL.trans (expandingRadius_ge L t hL ht)) φ u =
      expandingFourierTest a k L ha ha1 hk hL (homogeneousFreeDualTest a b t φ) f +
        ∫ τ in Icc 0 t, expandingDualDuhamelIntegrand a b k L t ha ha1 hk hL φ r τ := by
  rw [hu, map_add, expandingFreeStep_fourier_duality,
    expandingDuhamel_fourier_duality a b k L t ha ha1 hk hL ht φ r hr]

end DefocusingNLS

end OAI
