import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingIdentifiedCompactness
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingCoordinateMap
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRealCoordinateEvolution
import OAI.MathematicalPhysics.DefocusingNLS.Linear.WeakLinearCoordinates

namespace OAI

/-! # Finite-coordinate defects vanish along every bounded expanding sequence -/

open Set Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

attribute [local irreducible] expandingProfileTrajectory

theorem expandingProfile_coordinate_sequence (a b k T Q M C₀ : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 10 < k) (hT : 0 ≤ T)
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hC₀ : 0 ≤ C₀) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (ρ : ℝ) (hρ : 0 < ρ) (hχ : ∀ y : E, ‖y‖ ≤ ρ → χ y = 1)
    (hCb : ∀ (L : ℝ) (hL : 1 ≤ L) (f : FourierL2),
      ‖homogeneousLocalizationCLM a k L ha ha1 (by linarith) hL χ f‖ ≤ C₀ * ‖f‖)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop)
    (q : ℕ → C(Icc (0 : ℝ) T, FourierL2)) (hq : ∀ n t, ‖q n t‖ ≤ Q)
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M) (Q₀ : HomogeneousY a k)
    (π : HomogeneousY a k →L[ℝ] F) (A : F →L[ℝ] F)
    (hA : ∀ u, π (homogeneousLinearizedTrajectory a b k T ha ha1 (by linarith) hT m Q₀ u
      ⟨T, hT, le_rfl⟩) = A (π u))
    (hqp : ∀ (s : Icc (0 : ℝ) T) (y : E),
      Tendsto (fun n => expandingPhysicalContinuous a k (expandingRadius (L n) s)
        ha ha1 (by linarith) ((hL n).trans (expandingRadius_ge (L n) s (hL n) s.2.1)) (q n s) y)
        atTop (𝓝 (homogeneousPhysicalCLM a k ha ha1 (by linarith) Q₀ y))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ‖expandingCoordinates a k ha ha1 (by linarith) χ π
          (expandingRadiusCurve (L n) T (hL n) ⟨T, hT, le_rfl⟩)
          (expandingProfileTrajectory a b k (L n) T ha ha1 (by linarith) (hL n) hT
            m Q hQ (q n) (hq n) (f n) ⟨T, hT, le_rfl⟩) -
        A (expandingCoordinates a k ha ha1 (by linarith) χ π ⟨L n, hL n⟩ (f n))‖ < ε := by
  have hk8 : 8 < k := by linarith
  intro ε hε
  by_contra h
  obtain ⟨ψ, hψ, hbad⟩ := extraction_of_frequently_atTop (show ∃ᶠ n in atTop,
      ε ≤ ‖expandingCoordinates a k ha ha1 hk8 χ π
          (expandingRadiusCurve (L n) T (hL n) ⟨T, hT, le_rfl⟩)
          (expandingProfileTrajectory a b k (L n) T ha ha1 hk8 (hL n) hT
            m Q hQ (q n) (hq n) (f n) ⟨T, hT, le_rfl⟩) -
        A (expandingCoordinates a k ha ha1 hk8 χ π ⟨L n, hL n⟩ (f n))‖ by
    simpa only [not_eventually, not_lt] using h)
  obtain ⟨φ, _hφ, _v, u₀, _hu₀, _hv, _hphysical, hweak⟩ :=
    expandingProfile_exists_identified_limit a b k T Q M C₀ ha ha1 hk hT hQ hM hC₀ m χ ρ hρ hχ hCb
      (fun n => L (ψ n)) (fun n => hL (ψ n)) (hLinf.comp hψ.tendsto_atTop)
      (fun n => q (ψ n)) (fun n => hq (ψ n)) (fun n => f (ψ n)) (fun n => hf (ψ n)) Q₀
      (fun t y => (hqp t y).comp hψ.tendsto_atTop)
  let σ := fun n => ψ (φ n)
  have hfina := tendsto_finite_coordinates_of_weak π _ _ (hweak ⟨T, hT, le_rfl⟩)
  have hinit := tendsto_finite_coordinates_of_weak π _ _ (hweak ⟨0, le_rfl, hT⟩)
  simp only [expandingProfileTrajectory_initial, expandingRadius, zero_div, Real.exp_zero,
    mul_one, homogeneousLinearizedTrajectory_initial] at hinit
  have htarget := A.continuous.continuousAt.tendsto.comp hinit
  have hdefect := hfina.sub htarget
  rw [hA, sub_self] at hdefect
  have hnorm := hdefect.norm
  have hsmall := hnorm.eventually (gt_mem_nhds (show ‖(0 : F)‖ < ε by simpa using hε))
  obtain ⟨j, hj⟩ := hsmall.exists
  exact (not_lt_of_ge (hbad (φ j))) hj

end DefocusingNLS

end OAI
