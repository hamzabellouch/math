import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearization
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalInjective
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! # Strong differentiation from a faithful physical integral identity -/

open MeasureTheory Set

namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem hasDerivAt_homogeneous_of_physical (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (u v : ℝ → HomogeneousY a k) (hv : Continuous v)
    (hd : ∀ t : ℝ, ∀ x : E, HasDerivAt
      (fun s => homogeneousPhysicalCLM a k ha ha1 hk (u s) x)
      (homogeneousPhysicalCLM a k ha ha1 hk (v t) x) t) (t : ℝ) :
    HasDerivAt u (v t) t := by
  have he (s : ℝ) : u s = u 0 + ∫ r in (0 : ℝ)..s, v r := by
    apply homogeneousPhysicalCLM_injective a k ha ha1 hk
    ext x
    let L := (homogeneousPointEvaluation a k ha ha1 hk x).restrictScalars ℝ
    have hL (w : HomogeneousY a k) : L w = homogeneousPhysicalCLM a k ha ha1 hk w x := rfl
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r (_ : r ∈ uIcc (0 : ℝ) s) => hd r x)
      ((L.continuous.comp hv).intervalIntegrable 0 s)
    rw [map_add]
    change L (u s) = L (u 0) + L (∫ r in (0 : ℝ)..s, v r)
    rw [← L.intervalIntegral_comp_comm (hv.intervalIntegrable 0 s)]
    simp only [hL] at hi ⊢
    linear_combination -hi
  have hi := (intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable 0 t)
    hv.aestronglyMeasurable.stronglyMeasurableAtFilter (hv.continuousAt (x := t))).const_add (u 0)
  convert hi using 1
  exact funext he

theorem hasDerivWithinAt_homogeneous_of_physical_Ici (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (u v : ℝ → HomogeneousY a k) (hu : ContinuousOn u (Ici 0)) (hv : Continuous v)
    (hd : ∀ t : ℝ, 0 < t → ∀ x : E, HasDerivAt
      (fun s => homogeneousPhysicalCLM a k ha ha1 hk (u s) x)
      (homogeneousPhysicalCLM a k ha ha1 hk (v t) x) t)
    (t : ℝ) (ht : 0 ≤ t) : HasDerivWithinAt u (v t) (Ici 0) t := by
  have he (s : ℝ) (hs : 0 ≤ s) : u s = u 0 + ∫ r in (0 : ℝ)..s, v r := by
    apply homogeneousPhysicalCLM_injective a k ha ha1 hk
    ext x
    let L := (homogeneousPointEvaluation a k ha ha1 hk x).restrictScalars ℝ
    have hL (w : HomogeneousY a k) : L w = homogeneousPhysicalCLM a k ha ha1 hk w x := rfl
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs
      (L.continuous.comp_continuousOn (hu.mono (fun r hr => hr.1)))
      (fun r hr => hd r hr.1 x) ((L.continuous.comp hv).intervalIntegrable 0 s)
    rw [map_add]
    change L (u s) = L (u 0) + L (∫ r in (0 : ℝ)..s, v r)
    rw [← L.intervalIntegral_comp_comm (hv.intervalIntegrable 0 s)]
    simp only [Function.comp_def, hL] at hi ⊢
    linear_combination -hi
  have hi := (intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable 0 t)
    hv.aestronglyMeasurable.stronglyMeasurableAtFilter (hv.continuousAt (x := t))).const_add (u 0)
  exact hi.hasDerivWithinAt.congr_of_mem he ht

end DefocusingNLS

end OAI
