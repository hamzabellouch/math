import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingLimitRealization
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalIntegrable

namespace OAI

/-! # The local space-time limit as a weakly continuous Bochner-measurable Y path -/

open Set Filter Topology MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem expandingLimit_exists_weaklyContinuous_path (a k M T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop)
    (χ : 𝓢(E, ℂ)) (ρ : ℝ) (hρ : 0 < ρ) (hχ : ∀ y : E, ‖y‖ ≤ ρ → χ y = 1)
    (u : ℕ → C(Icc (0 : ℝ) T, FourierL2)) (hu : ∀ n t, ‖u n t‖ ≤ M)
    (v : C(Icc (0 : ℝ) T × E, ℂ))
    (hv : Tendsto (fun n => expandingSpacetimePath a k (L n) T ha ha1 hk (hL n) (u n))
      atTop (𝓝 v)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ w : Icc (0 : ℝ) T → HomogeneousY a k,
      (∀ t, ‖w t‖ ≤ C * M) ∧
      (∀ t y, homogeneousPhysicalCLM a k ha ha1 hk (w t) y = v (t, y)) ∧
      (∀ ℓ : HomogeneousY a k →L[ℝ] ℂ, Continuous (fun t => ℓ (w t))) ∧
      StronglyMeasurable (fun s : ℝ => w (projIcc 0 T hT s)) ∧
      (∀ (t : Icc (0 : ℝ) T) (ℓ : HomogeneousY a k →L[ℝ] ℂ),
        Tendsto (fun n => ℓ (homogeneousLocalizationCLM a k (expandingRadius (L n) t)
          ha ha1 hk ((hL n).trans (expandingRadius_ge (L n) t (hL n) t.2.1)) χ (u n t)))
          atTop (𝓝 (ℓ (w t)))) := by
  obtain ⟨C, hC, h⟩ := expandingLimit_exists_homogeneous_slices a k M T ha ha1 hk
    L hL hLinf χ ρ hρ hχ u hu v hv
  choose w hw hp hweak using h
  have hc (y : E) : Continuous (fun t => homogeneousPhysicalCLM a k ha ha1 hk (w t) y) :=
    (v.continuous.comp (continuous_id.prodMk continuous_const)).congr
      (fun t => (hp t y).symm)
  refine ⟨C, hC, w, hw, hp, ?_, ?_, hweak⟩
  · exact fun ℓ => continuous_functional_of_physical a k (C * M) ha ha1 hk w hw hc ℓ
  · exact stronglyMeasurable_homogeneous_clamped a k T ha ha1 hk hT w hc

end DefocusingNLS

end OAI
