import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSpacetimeObservation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingLocalConvergence
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalWeakLimit

namespace OAI

/-! # Every time slice of a local space-time limit is a bounded Y vector -/

open Set Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

attribute [local irreducible] expandingTorusFunction

theorem expandingLimit_exists_homogeneous_slices (a k M T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop)
    (χ : 𝓢(E, ℂ)) (ρ : ℝ) (hρ : 0 < ρ) (hχ : ∀ y : E, ‖y‖ ≤ ρ → χ y = 1)
    (u : ℕ → C(Icc (0 : ℝ) T, FourierL2)) (hu : ∀ n t, ‖u n t‖ ≤ M)
    (v : C(Icc (0 : ℝ) T × E, ℂ))
    (hv : Tendsto (fun n => expandingSpacetimePath a k (L n) T ha ha1 hk (hL n) (u n))
      atTop (𝓝 v)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : Icc (0 : ℝ) T,
      ∃ w : HomogeneousY a k, ‖w‖ ≤ C * M ∧
        (∀ y, homogeneousPhysicalCLM a k ha ha1 hk w y = v (t, y)) ∧
        ∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
          Tendsto (fun n => ℓ (homogeneousLocalizationCLM a k (expandingRadius (L n) t)
            ha ha1 hk (hL n |>.trans (expandingRadius_ge (L n) t (hL n) t.2.1)) χ (u n t)))
            atTop (𝓝 (ℓ w)) := by
  obtain ⟨C, hC, hCb⟩ := exists_homogeneousLocalization_bound a k ha ha1 hk χ
  refine ⟨C, hC, fun t => ?_⟩
  let R := fun n => expandingRadius (L n) t
  have hR (n : ℕ) : 1 ≤ R n := (hL n).trans (expandingRadius_ge (L n) t (hL n) t.2.1)
  have hRinf : Tendsto R atTop atTop := hLinf.atTop_mul_const (Real.exp_pos _)
  apply homogeneousY_exists_of_physical_limit a k (C * M) ha ha1 hk
    (fun n => homogeneousLocalizationCLM a k (R n) ha ha1 hk (hR n) χ (u n t))
    (fun y => v (t, y))
  · intro n
    exact (hCb (R n) (hR n) (u n t)).trans (mul_le_mul_of_nonneg_left (hu n t) hC)
  · intro y
    have hp := ((continuous_eval_const (t, y)).tendsto v).comp hv
    have he : (fun n => homogeneousPhysicalCLM a k ha ha1 hk
        (homogeneousLocalizationCLM a k (R n) ha ha1 hk (hR n) χ (u n t)) y) =ᶠ[atTop]
        (fun n => expandingSpacetimePath a k (L n) T ha ha1 hk (hL n) (u n) (t, y)) := by
      filter_upwards [eventually_expandingCutoff_one R hR hRinf χ ρ ‖y‖ hρ hχ] with n hn
      rw [homogeneousLocalization_physical]
      change χ ((R n)⁻¹ • y) * _ = _
      rw [hn y le_rfl, one_mul]
      rfl
    exact hp.congr' he.symm

end DefocusingNLS

end OAI
