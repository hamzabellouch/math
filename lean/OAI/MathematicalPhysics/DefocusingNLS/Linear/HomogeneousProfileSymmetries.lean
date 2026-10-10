import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousProfileDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearization
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialTimeMode

namespace OAI

/-! # Physical symmetry directions in the faithful homogeneous space -/

open scoped ContDiff Laplacian

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneous_profile_translation_map (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hsymbol : ∀ n : ℕ, ∃ D : ℝ, ∀ y : E, 1 ≤ ‖y‖ →
      ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) :
    ∃ D : E →L[ℝ] HomogeneousY a k, ∀ v y,
      homogeneousPhysicalCLM a k ha ha1 hk (D v) y = cartesianDerivative v Q y := by
  classical
  let b := (EuclideanSpace.basisFun (Fin 12) ℝ).toBasis
  choose q hq using fun j : Fin 12 =>
    homogeneous_profile_directional_derivative a k ha ha1 hk Q hQ hsymbol (b j)
  let D : E →L[ℝ] HomogeneousY a k := (b.constr ℝ q).toContinuousLinearMap
  refine ⟨D, ?_⟩
  intro v y
  let ev := (homogeneousPointEvaluation a k ha ha1 hk y).restrictScalars ℝ
  have he : ev.toLinearMap.comp D.toLinearMap = (fderiv ℝ Q y).toLinearMap := by
    apply b.ext
    intro j
    change homogeneousPhysicalCLM a k ha ha1 hk ((b.constr ℝ q) (b j)) y =
      cartesianDerivative (b j) Q y
    rw [b.constr_basis]
    exact hq j y
  exact DFunLike.congr_fun he v

theorem stationary_time_field_eq (a b : ℝ) (m : ℕ) (Q : E → ℂ)
    (hstat : ∀ y, stationarySimilarityDefect a b m Q y = 0) (y : E) :
    ((a : ℂ) - Complex.I * (b : ℂ)) * Q y + cartesianTransport Q y =
      Complex.I * (Δ Q y - oddPowerNonlinearity m (Q y)) := by
  have hs := congrArg (fun z : ℂ => Complex.I * z) (hstat y)
  dsimp only [stationarySimilarityDefect] at hs
  simp only [mul_add, mul_sub, ← mul_assoc, Complex.I_mul_I, neg_one_mul, mul_zero] at hs
  unfold cartesianTransport
  linear_combination -hs

theorem homogeneous_profile_time_direction (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hsymbol : ∀ n : ℕ, ∃ D : ℝ, ∀ y : E, 1 ≤ ‖y‖ →
      ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ)))
    (q : HomogeneousY a k)
    (hq : ∀ y, homogeneousPhysicalCLM a k ha ha1 hk q y = Q y)
    (hstat : ∀ y, stationarySimilarityDefect a b m Q y = 0) :
    ∃ t : HomogeneousY a k, ∀ y, homogeneousPhysicalCLM a k ha ha1 hk t y =
      ((a : ℂ) - Complex.I * (b : ℂ)) * Q y + cartesianTransport Q y := by
  obtain ⟨qL, hL⟩ := homogeneous_profile_laplacian a k ha ha1 hk Q hQ hsymbol
  refine ⟨Complex.I • (qL - homogeneousOddPower a k ha ha1 hk m q), ?_⟩
  intro y
  rw [map_smul, map_sub]
  change Complex.I * (homogeneousPhysicalCLM a k ha ha1 hk qL y -
    homogeneousPhysicalCLM a k ha ha1 hk (homogeneousOddPower a k ha ha1 hk m q) y) = _
  rw [hL, homogeneousOddPower_physical, hq, stationary_time_field_eq a b m Q hstat]

end DefocusingNLS

end OAI
