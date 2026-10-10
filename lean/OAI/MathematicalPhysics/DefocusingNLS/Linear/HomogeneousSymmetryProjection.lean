import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSymmetryEvolution
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalFrame
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableProjectionEigenvector
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRealStableCoordinates

namespace OAI

/-! # The contour projection fixes all physical symmetry directions -/

open scoped NNReal

namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

attribute [local irreducible] homogeneousComplexLinearizedStep homogeneousLinearizedStep

theorem homogeneousProjection_fixes_real_eigenvector (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (q : HomogeneousY a k)
    (P : (HomogeneousY a k × HomogeneousY a k) →L[ℂ] (HomogeneousY a k × HomogeneousY a k))
    (hP : IsIdempotentElem P)
    (hcomm : ∀ s, Commute (homogeneousComplexLinearizedStep a b k ha ha1 hk m q s) P)
    (D δ : ℝ) (hδ : 0 < δ)
    (hdecay : ∀ s : ℝ≥0, ∀ w, P w = 0 →
      ‖homogeneousComplexLinearizedStep a b k ha ha1 hk m q s w‖ ≤
        D * Real.exp (-δ * (s : ℝ)) * ‖w‖)
    (u : HomogeneousY a k) (lam : ℝ) (hlam : 0 ≤ lam)
    (he : ∀ s : ℝ≥0, homogeneousLinearizedStep a b k ha ha1 hk m q s u =
      Real.exp (lam * (s : ℝ)) • u) :
    P (homogeneousComplexEmbed a k ha ha1 hk u) = homogeneousComplexEmbed a k ha ha1 hk u := by
  apply stable_projection_fixes_eigenvector _ P hP hcomm D δ hδ hdecay _ lam hlam
  intro s
  rw [homogeneousComplexLinearizedStep, homogeneousComplexification_embed, he]
  simp only [map_smul, Complex.coe_smul]
  rfl

theorem radialMatched_projection_fixes_physical_frame (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (k : ℝ)
    (ha : 0 < radialShootingA n) (ha1 : radialShootingA n < 1) (hk : 8 < k)
    (q : HomogeneousY (radialShootingA n) k)
    (hq : ∀ y, homogeneousPhysicalCLM (radialShootingA n) k ha ha1 hk q y = radialMatchedCartesian n z y)
    (P : (HomogeneousY (radialShootingA n) k × HomogeneousY (radialShootingA n) k) →L[ℂ]
      (HomogeneousY (radialShootingA n) k × HomogeneousY (radialShootingA n) k))
    (hP : IsIdempotentElem P)
    (hcomm : ∀ s, Commute (homogeneousComplexLinearizedStep (radialShootingA n)
      (radialShootingB (profileMatchingParameter z)) k ha ha1 hk (n + radialInnerShootingThreshold) q s) P)
    (D δ : ℝ) (hδ : 0 < δ)
    (hdecay : ∀ s : ℝ≥0, ∀ w, P w = 0 →
      ‖homogeneousComplexLinearizedStep (radialShootingA n)
        (radialShootingB (profileMatchingParameter z)) k ha ha1 hk (n + radialInnerShootingThreshold) q s w‖ ≤
          D * Real.exp (-δ * (s : ℝ)) * ‖w‖)
    (F : ProfileSymmetryParameters →L[ℝ] HomogeneousY (radialShootingA n) k)
    (hF : ∀ p y, homogeneousPhysicalCLM (radialShootingA n) k ha ha1 hk (F p) y =
      (p.1 : ℂ) * (Complex.I * radialMatchedCartesian n z y) +
      (p.2.2 : ℂ) * (((radialShootingA n : ℂ) -
        Complex.I * (radialShootingB (profileMatchingParameter z) : ℂ)) * radialMatchedCartesian n z y +
          cartesianTransport (radialMatchedCartesian n z) y) +
        cartesianDerivative p.2.1 (radialMatchedCartesian n z) y) (p : ProfileSymmetryParameters) :
    P (homogeneousComplexEmbed (radialShootingA n) k ha ha1 hk (F p)) =
      homogeneousComplexEmbed (radialShootingA n) k ha ha1 hk (F p) := by
  let ι := homogeneousComplexEmbed (radialShootingA n) k ha ha1 hk
  have hphase : P (ι (F (1, 0, 0))) = ι (F (1, 0, 0)) := by
    apply homogeneousProjection_fixes_real_eigenvector _ _ _ ha ha1 hk _ q P hP hcomm D δ hδ hdecay _ 0 le_rfl
    intro s
    simpa only [zero_mul, Real.exp_zero, one_smul] using
      radialMatched_phase_evolution n z hX hz k ha ha1 hk q hq (F (1, 0, 0))
        (fun y => by simpa [cartesianDerivative] using hF (1, 0, 0) y) s
  have htime : P (ι (F (0, 0, 1))) = ι (F (0, 0, 1)) := by
    apply homogeneousProjection_fixes_real_eigenvector _ _ _ ha ha1 hk _ q P hP hcomm D δ hδ hdecay _ 1 zero_le_one
    intro s
    simpa only [one_mul] using
      radialMatched_time_evolution n z hX hz k ha ha1 hk q hq (F (0, 0, 1))
        (fun y => by simpa [cartesianDerivative] using hF (0, 0, 1) y) s
  have htrans : P (ι (F (0, p.2.1, 0))) = ι (F (0, p.2.1, 0)) := by
    apply homogeneousProjection_fixes_real_eigenvector _ _ _ ha ha1 hk _ q P hP hcomm D δ hδ hdecay _ (1 / 2) (by norm_num)
    exact radialMatched_translation_evolution n z hX hz k ha ha1 hk q hq p.2.1
      (F (0, p.2.1, 0)) (fun y => by simpa using hF (0, p.2.1, 0) y)
  have hp : p = p.1 • ((1, 0, 0) : ProfileSymmetryParameters) + (0, p.2.1, 0) +
      p.2.2 • ((0, 0, 1) : ProfileSymmetryParameters) := by
    ext <;> simp
  have he : ι (F p) = p.1 • ι (F (1, 0, 0)) + ι (F (0, p.2.1, 0)) +
      p.2.2 • ι (F (0, 0, 1)) := by
    conv_lhs => rw [hp]
    simp only [map_add, map_smul]
  change P (ι (F p)) = ι (F p)
  rw [he]
  simp only [map_add, ContinuousLinearMap.map_smul_of_tower, hphase, htime, htrans]

end DefocusingNLS

end OAI
