import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingCoordinateSequence
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffStableTransfer

namespace OAI

/-! # Uniform finite-coordinate transfer for the sampled cutoff profile -/

open Set Filter Topology
open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem sampledCutoffProfile_uniform_coordinate_defect (a b k T Q C₀ : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 10 < k) (hT : 0 ≤ T)
    (hQ : 0 ≤ Q) (hC₀ : 0 ≤ C₀) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (hχone : ∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1)
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp) (Q₀ : HomogeneousY a k)
    (hQ₀ : ∀ y, homogeneousPhysicalCLM a k ha ha1 (by linarith) Q₀ y = Qp y)
    (hqb : ∀ L : Radius, ‖cutoffProfileCoefficient a k ha1 (by linarith) χ hχ Qp hQp L‖ ≤ Q)
    (hCb : ∀ (L : ℝ) (hL : 1 ≤ L) (f : FourierL2),
      ‖homogeneousLocalizationCLM a k L ha ha1 (by linarith) hL χ f‖ ≤ C₀ * ‖f‖)
    (π : HomogeneousY a k →L[ℝ] F) (A : F →L[ℝ] F)
    (hA : ∀ u, π (homogeneousLinearizedTrajectory a b k T ha ha1 (by linarith) hT m Q₀ u
      ⟨T, hT, le_rfl⟩) = A (π u)) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℝ, ∀ L : Radius, L₀ ≤ L.1 → ∀ f : FourierL2, ‖f‖ ≤ 1 →
      ‖expandingCoordinates a k ha ha1 (by linarith) χ π
          (expandingRadiusCurve L.1 T L.2 ⟨T, hT, le_rfl⟩)
          (expandingProfileTrajectory a b k L.1 T ha ha1 (by linarith) L.2 hT m Q hQ
            (sampledCutoffProfilePath a k L.1 T ha ha1 (by linarith) L.2 χ hχ Qp hQp)
            (fun t => hqb (expandingRadiusCurve L.1 T L.2 t)) f ⟨T, hT, le_rfl⟩) -
        A (expandingCoordinates a k ha ha1 (by linarith) χ π L f)‖ < ε := by
  classical
  have hk8 : 8 < k := by linarith
  intro ε hε
  by_contra h
  push Not at h
  choose L hL f hf hbad using fun n : ℕ => h (n : ℝ)
  have hLinf : Tendsto (fun n => (L n).1) atTop atTop :=
    tendsto_atTop_mono hL tendsto_natCast_atTop_atTop
  let q := fun n => sampledCutoffProfilePath a k (L n).1 T ha ha1 hk8 (L n).2 χ hχ Qp hQp
  have hq (n : ℕ) (t : Icc (0 : ℝ) T) : ‖q n t‖ ≤ Q :=
    hqb (expandingRadiusCurve (L n).1 T (L n).2 t)
  have hqp (t : Icc (0 : ℝ) T) (y : E) :
      Tendsto (fun n => expandingPhysicalContinuous a k (expandingRadius (L n).1 t)
        ha ha1 hk8 ((L n).2.trans (expandingRadius_ge (L n).1 t (L n).2 t.2.1)) (q n t) y)
        atTop (𝓝 (homogeneousPhysicalCLM a k ha ha1 hk8 Q₀ y)) := by
    rw [hQ₀]
    exact tendsto_sampledCutoffProfilePath_physical a k T ha ha1 hk8 χ hχ hχzero hχone
      Qp hQp (fun n => (L n).1) (fun n => (L n).2) hLinf t y
  have hs := expandingProfile_coordinate_sequence a b k T Q 1 C₀ ha ha1 hk hT hQ
    zero_le_one hC₀ m χ (1 / 2) (by norm_num) hχone hCb
    (fun n => (L n).1) (fun n => (L n).2) hLinf q hq f hf Q₀ π A hA hqp ε hε
  obtain ⟨n, hn⟩ := hs.exists
  exact (not_lt_of_ge (hbad n)) hn

end DefocusingNLS

end OAI
