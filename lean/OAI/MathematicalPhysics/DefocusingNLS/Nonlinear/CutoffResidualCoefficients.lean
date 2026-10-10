import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffFiniteJets
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffResidualScaling
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

namespace OAI

/-! # Compact annular coefficients of the cutoff residual -/

open scoped SchwartzMap Laplacian ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def cutoffGradientCoefficient (χ : 𝓢(E, ℝ)) (j : Fin 12) : 𝓢(E, ℂ) :=
  (SchwartzMap.evalCLM ℝ E ℝ ((EuclideanSpace.basisFun (Fin 12) ℝ) j)
    (SchwartzMap.fderivCLM ℝ E ℝ χ)).postcompCLM Complex.ofRealCLM

@[simp] theorem cutoffGradientCoefficient_apply (χ : 𝓢(E, ℝ)) (j : Fin 12) (x : E) :
    cutoffGradientCoefficient χ j x =
      (fderiv ℝ χ x ((EuclideanSpace.basisFun (Fin 12) ℝ) j) : ℂ) := rfl

noncomputable def cutoffLaplacianCoefficient (χ : 𝓢(E, ℝ)) : 𝓢(E, ℂ) :=
  (Δ χ).postcompCLM Complex.ofRealCLM

@[simp] theorem cutoffLaplacianCoefficient_apply (χ : 𝓢(E, ℝ)) (x : E) :
    cutoffLaplacianCoefficient χ x = (Δ (χ : E → ℝ) x : ℂ) := by
  simp only [cutoffLaplacianCoefficient, SchwartzMap.postcompCLM_apply,
    SchwartzMap.laplacian_apply, Complex.ofRealCLM_apply]

noncomputable def cutoffPowerCoefficient (χ : 𝓢(E, ℝ))
    (hχ : HasCompactSupport (χ : E → ℝ)) (m : ℕ) : 𝓢(E, ℂ) :=
  ((hχ.comp_left (g := fun t : ℝ => t - t ^ (2 * m + 1)) (by simp)).toSchwartzMap
    (χ.smooth'.sub (χ.smooth'.pow (2 * m + 1)))).postcompCLM Complex.ofRealCLM

@[simp] theorem cutoffPowerCoefficient_apply (χ : 𝓢(E, ℝ))
    (hχ : HasCompactSupport (χ : E → ℝ)) (m : ℕ) (x : E) :
    cutoffPowerCoefficient χ hχ m x = ((χ x - χ x ^ (2 * m + 1) : ℝ) : ℂ) := rfl

private theorem tsupport_annulus_of_zero (f : E → ℂ)
    (hz : ∀ x, ‖x‖ < 1 / 2 ∨ 2 < ‖x‖ → f x = 0) :
    ∀ x ∈ tsupport f, (1 / 2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 2 := by
  have hs : tsupport f ⊆ {x : E | (1 / 2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 2} := by
    apply closure_minimal
    · intro x hx
      constructor
      · by_contra hn
        exact hx (hz x (Or.inl (lt_of_not_ge hn)))
      · by_contra hn
        exact hx (hz x (Or.inr (lt_of_not_ge hn)))
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
  exact fun x hx => hs hx

private theorem cutoff_eventually_constant (χ : 𝓢(E, ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0) (x : E)
    (hx : ‖x‖ < 1 / 2 ∨ 2 < ‖x‖) :
    ∃ c : ℝ, (c = 0 ∨ c = 1) ∧ (χ : E → ℝ) =ᶠ[nhds x] fun _ => c := by
  rcases hx with hx | hx
  · refine ⟨1, Or.inr rfl, ?_⟩
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    exact hχone y hy
  · refine ⟨0, Or.inl rfl, ?_⟩
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    exact hχzero y hy

theorem cutoffGradientCoefficient_annulus (χ : 𝓢(E, ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0) (j : Fin 12) :
    ∀ x ∈ tsupport (cutoffGradientCoefficient χ j : E → ℂ),
      (1 / 2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 2 := by
  apply tsupport_annulus_of_zero
  intro x hx
  obtain ⟨c, _, hc⟩ := cutoff_eventually_constant χ hχone hχzero x hx
  rw [cutoffGradientCoefficient_apply, hc.fderiv_eq]
  simp

theorem cutoffLaplacianCoefficient_annulus (χ : 𝓢(E, ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0) :
    ∀ x ∈ tsupport (cutoffLaplacianCoefficient χ : E → ℂ),
      (1 / 2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 2 := by
  apply tsupport_annulus_of_zero
  intro x hx
  obtain ⟨c, _, hc⟩ := cutoff_eventually_constant χ hχone hχzero x hx
  rw [cutoffLaplacianCoefficient_apply, (InnerProductSpace.laplacian_congr_nhds hc).eq_of_nhds]
  simp

theorem cutoffPowerCoefficient_annulus (χ : 𝓢(E, ℝ))
    (hχ : HasCompactSupport (χ : E → ℝ)) (m : ℕ)
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0) :
    ∀ x ∈ tsupport (cutoffPowerCoefficient χ hχ m : E → ℂ),
      (1 / 2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 2 := by
  apply tsupport_annulus_of_zero
  intro x hx
  obtain ⟨c, hc, heq⟩ := cutoff_eventually_constant χ hχone hχzero x hx
  rw [cutoffPowerCoefficient_apply, heq.eq_of_nhds]
  rcases hc with rfl | rfl <;> simp

theorem hasCompactSupport_of_cutoff_annulus (f : E → ℂ)
    (hf : ∀ x ∈ tsupport f, (1 / 2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 2) :
    HasCompactSupport f := by
  apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : E) 2) (isClosed_tsupport f)
  intro x hx
  simpa only [Metric.mem_closedBall, dist_zero_right] using (hf x hx).2

end DefocusingNLS

end OAI
