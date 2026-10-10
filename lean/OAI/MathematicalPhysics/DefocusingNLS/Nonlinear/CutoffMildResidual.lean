import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffMildEquation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingDuhamelLinear

namespace OAI

/-! # The exact mild defect has the proved small cutoff-residual bound -/

open Set MeasureTheory
open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem expandingDuhamel_complex_smul (a b k L : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L)
    (t : ℝ) (c : ℂ) (r : ℝ → FourierL2) :
    expandingDuhamel a b k L ha hk hL t (fun s => c • r s) =
      c • expandingDuhamel a b k L ha hk hL t r := by
  unfold expandingDuhamel
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  simp only [expandingDuhamelIntegrand_of_mem _ _ _ _ _ _ _ _ _ _ hs, map_smul]

noncomputable def sampledCutoffNonlinearHistory (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (m : ℕ) : ℝ → FourierL2 :=
  fun t => (-Complex.I) • sampledCutoffNonlinearPath a k L T ha ha1 hk hL
    (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ)
    Q hQ m (projIcc 0 T hT t)

theorem continuous_sampledCutoffNonlinearHistory (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (m : ℕ) :
    Continuous (sampledCutoffNonlinearHistory a k L T ha ha1 hk hL hT χ hχ Q hQ m) := by
  have hp : Continuous (fun t : ℝ => projIcc 0 T hT t) := continuous_projIcc
  exact ((sampledCutoffNonlinearPath a k L T ha ha1 hk hL
    (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ)
    Q hQ m).continuous.comp hp).const_smul (-Complex.I)

theorem sampledCutoffProfile_mild_residual (a b k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (m : ℕ) (ham : 2 * a * (m : ℝ) = 1)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hstationary : ∀ y, stationarySimilarityDefect a b m Q y = 0)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    let u := sampledCutoffProfileHistory a k L T ha ha1 hk hL hT
      (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ
    u t - expandingFreeStep a b k L t ha hk hL ht.1 (u 0) -
      expandingDuhamel a b k L ha hk hL t
        (sampledCutoffNonlinearHistory a k L T ha ha1 hk hL hT χ hχ Q hQ m) =
      (-Complex.I) • expandingDuhamel a b k L ha hk hL t
        (sampledCutoffResidualHistory a k L T ha ha1 hk hL hT χ hχ hχone hχzero m Q hQ) := by
  intro u
  change 0 ≤ t ∧ t ≤ T at ht
  have hu := sampledCutoffProfile_mild a b k L T ha ha1 hk hL hT m ham
    χ hχ hχone hχzero Q hQ hstationary t ht
  change u t = expandingFreeStep a b k L t ha hk hL ht.1 (u 0) +
    expandingDuhamel a b k L ha hk hL t
      (sampledCutoffForcingHistory a k L T ha ha1 hk hL hT χ hχ hχone hχzero m Q hQ) at hu
  have hf : sampledCutoffForcingHistory a k L T ha ha1 hk hL hT χ hχ hχone hχzero m Q hQ =
      fun s => sampledCutoffNonlinearHistory a k L T ha ha1 hk hL hT χ hχ Q hQ m s +
        (-Complex.I) • sampledCutoffResidualHistory a k L T ha ha1 hk hL hT
          χ hχ hχone hχzero m Q hQ s := rfl
  rw [hf] at hu
  have hd := expandingDuhamel_add a b k L ha hk hL t
    (sampledCutoffNonlinearHistory a k L T ha ha1 hk hL hT χ hχ Q hQ m)
    (fun s => (-Complex.I) • sampledCutoffResidualHistory a k L T ha ha1 hk hL hT
      χ hχ hχone hχzero m Q hQ s)
    (continuous_sampledCutoffNonlinearHistory a k L T ha ha1 hk hL hT χ hχ Q hQ m).continuousOn
    ((continuous_sampledCutoffResidualHistory a k L T ha ha1 hk hL hT
      χ hχ hχone hχzero m Q hQ).const_smul (-Complex.I)).continuousOn
  rw [hd, expandingDuhamel_complex_smul] at hu
  change u t = _ at hu
  rw [hu]
  abel

/-- The true mild defect is uniformly small in the initial torus scale. -/
theorem exists_cutoffProfile_mild_residual_bound (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (m : ℕ) (ham : 2 * a * (m : ℝ) = 1) :
    ∃ N : ℕ, ∀ (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (D : ℝ), 0 ≤ D →
      (∀ n ≤ N, ∀ y : E, y ≠ 0 →
        ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) →
      (∀ y, stationarySimilarityDefect a b m Q y = 0) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (L T : ℝ) (hL : 1 ≤ L) (hT : 0 ≤ T) (t : ℝ)
        (ht : t ∈ Icc 0 T),
        let u := sampledCutoffProfileHistory a k L T ha ha1 hk hL hT
          (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ
        ‖u t - expandingFreeStep a b k L t ha hk hL ht.1 (u 0) -
          expandingDuhamel a b k L ha hk hL t
            (sampledCutoffNonlinearHistory a k L T ha ha1 hk hL hT χ hχ Q hQ m)‖ ≤
          C * L ^ (-2 - a) * Real.exp (-a * t / 2) := by
  obtain ⟨N, hN⟩ := exists_cutoffResidual_Duhamel_bound a b k ha ha1 hk χ hχ hχone hχzero m
  refine ⟨N, ?_⟩
  intro Q hQ D hD hsymbol hstationary
  obtain ⟨C, hC, hbound⟩ := hN Q hQ D hD hsymbol
  refine ⟨C, hC, ?_⟩
  intro L T hL hT t ht u
  have he := sampledCutoffProfile_mild_residual a b k L T ha ha1 hk hL hT m ham
    χ hχ hχone hχzero Q hQ hstationary t ht
  change u t - expandingFreeStep a b k L t ha hk hL ht.1 (u 0) -
    expandingDuhamel a b k L ha hk hL t
      (sampledCutoffNonlinearHistory a k L T ha ha1 hk hL hT χ hχ Q hQ m) = _ at he
  rw [he, norm_smul]
  simpa only [norm_neg, Complex.norm_I, one_mul] using hbound L T hL hT t ht

end DefocusingNLS

end OAI
