import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalModulationTaylor

namespace OAI

/-! # The modulation map approaches the physical invertible frame in the retained coordinates -/

open Filter Topology
open scoped SchwartzMap ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}
local notation "Params" => ProfileSymmetryParameters

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem physical_modulation_coordinate_error (a b k : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hk : 8 < k) (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (hχone : ∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (hS : HasCartesianSymbol (-2 * a) Q)
    (F : Params →L[ℝ] HomogeneousY a k)
    (hphys : ∀ p y, homogeneousPhysicalCLM a k ha ha1 hk (F p) y =
      (p.1 : ℂ) * (Complex.I * Q y) +
      (p.2.2 : ℂ) * (((a : ℂ) - Complex.I * (b : ℂ)) * Q y + cartesianTransport Q y) +
      cartesianDerivative p.2.1 Q y)
    (hF : ∀ p, ContDiff ℝ ∞ (fun y => homogeneousPhysicalCLM a k ha ha1 hk (F p) y))
    (π : HomogeneousY a k →L[ℝ] V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℝ, ∀ (L : Radius),
      L₀ ≤ L.1 → 2 ≤ L.1 → ∀ p : Params, ‖p‖ ≤ 1 / 2 → ‖p‖ ≤ 2 * Real.log 2 →
      ‖expandingCoordinates a k ha ha1 hk χ π L
          (modulatedCutoffProfile a k ha ha1 hk χ hχ Q hQ L p) -
        π (F (physicalModulationParameterEquiv b p))‖ ≤
      C * (‖p‖ ^ 2 + ‖p‖ / L.1) + ε * ‖(physicalModulationParameterEquiv b).toContinuousLinearMap‖ * ‖p‖ := by
  obtain ⟨A, hA, haTaylor⟩ := modulatedCutoffProfile_taylor a b k ha ha1 hk χ hχ hχzero
    Q hQ (hS.global_profile_bound a ha) F hphys hF
  obtain ⟨J, hJ, hj⟩ := exists_homogeneousLocalization_bound a k ha ha1 hk χ
  let C := ‖π‖ * J * A
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ε hε
  have hb := physicalFrame_sample_bounded a b k ha ha1 hk Q F hphys hS χ hχ hχzero hF
  obtain ⟨L₀, hL₀⟩ := sampledPhysicalFrame_coordinate_approximation a k ha ha1 hk χ hχ
    hχzero hχone F hF hb π ε hε
  refine ⟨L₀, ?_⟩
  intro L hL hL2 p hp hplog
  let κ := expandingCoordinates a k ha ha1 hk χ π L
  let S := sampledPhysicalFrame a k ha ha1 hk χ hχ F hF L
  let M := physicalModulationParameterEquiv b
  let u := modulatedCutoffProfile a k ha ha1 hk χ hχ Q hQ L p
  have hκ : ‖κ‖ ≤ ‖π‖ * J := expandingCoordinates_norm_le a k J ha ha1 hk hJ χ π hj L
  have herr : ‖κ (u - S (M p))‖ ≤ C * (‖p‖ ^ 2 + ‖p‖ / L.1) := by
    calc
      _ ≤ ‖κ‖ * ‖u - S (M p)‖ := κ.le_opNorm _
      _ ≤ (‖π‖ * J) * (A * (‖p‖ ^ 2 + ‖p‖ / L.1)) :=
        mul_le_mul hκ (haTaylor L hL2 p hp hplog) (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [C]; ring
  have hlinear : ‖κ (S (M p)) - π (F (M p))‖ ≤ ε * ‖M.toContinuousLinearMap‖ * ‖p‖ := by
    have h := ((κ.comp S) - π.comp F).le_opNorm (M p)
    change ‖κ (S (M p)) - π (F (M p))‖ ≤ _ at h
    calc
      _ ≤ ‖κ.comp S - π.comp F‖ * ‖M p‖ := h
      _ ≤ ε * (‖M.toContinuousLinearMap‖ * ‖p‖) := mul_le_mul (hL₀ L hL).le (M.toContinuousLinearMap.le_opNorm p)
        (norm_nonneg _) hε.le
      _ = _ := by ring
  have he : κ u - π (F (M p)) = κ (u - S (M p)) + (κ (S (M p)) - π (F (M p))) := by
    rw [map_sub]
    abel
  change ‖κ u - π (F (M p))‖ ≤ _
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add herr hlinear)

end DefocusingNLS

end OAI
