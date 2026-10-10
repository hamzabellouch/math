import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalModulationRadius
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalModulationBound
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalModulationCoordinates

namespace OAI

/-! # Uniform chart estimates for nearby physical initial data -/

open scoped SchwartzMap ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}
local notation "Params" => ProfileSymmetryParameters

attribute [local irreducible] physicalStartingPerturbation physicalStartingOperator
  modulatedCutoffProfile sampledPhysicalFrame physicalReferenceData

theorem physicalStartingPerturbation_coordinate_data_bound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (L : Radius) (θ : ℝ) (x : SchrodingerTorus) (f g : FourierL2)
    (κ : FourierL2 →L[ℝ] V) :
    ‖κ (physicalStartingPerturbation a k ha ha1 hk χ hχ Q hQ L θ x f) -
      κ (physicalStartingPerturbation a k ha ha1 hk χ hχ Q hQ L θ x g)‖ ≤
      ‖κ‖ * ‖sobolevToExpanding a k ha hk‖ * ‖f - g‖ := by
  rw [← map_sub]
  exact (κ.le_opNorm _).trans ((mul_le_mul_of_nonneg_left
    (physicalStartingPerturbation_data_bound a k ha ha1 hk χ hχ Q hQ L θ x f g)
    (norm_nonneg _)).trans_eq (by ring))

theorem physicalStartingPerturbation_modulation_bound (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (hS : HasCartesianSymbol (-2 * a) Q) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ M R : Radius, 2 ≤ M.1 → ∀ p : Params,
      ‖p‖ ≤ 1 / 2 → ‖p‖ ≤ 2 * Real.log 2 → R.1 = expandingRadius M.1 p.2.2 →
      ∀ f : FourierL2,
      ‖physicalStartingPerturbation a k ha ha1 hk χ hχ Q hQ M p.1
        (euclideanToTorus ((1 / M.1) • p.2.1)) f‖ ≤ A * ‖p‖ +
        ‖sobolevToExpanding a k ha hk‖ *
          ‖f - physicalReferenceData a k ha ha1 hk χ hχ Q hQ R‖ := by
  obtain ⟨A, hA, hbound⟩ := modulatedCutoffProfile_bound a k ha ha1 hk χ hχ hχzero Q hQ
    (hS.global_profile_bound a ha)
  refine ⟨A, hA, ?_⟩
  intro M R hM p hp hplog hR f
  let f₀ := physicalReferenceData a k ha ha1 hk χ hχ Q hQ R
  let P := fun g => physicalStartingPerturbation a k ha ha1 hk χ hχ Q hQ M p.1
    (euclideanToTorus ((1 / M.1) • p.2.1)) g
  have hzero : P f₀ = modulatedCutoffProfile a k ha ha1 hk χ hχ Q hQ M p :=
    physicalStartingPerturbation_reference_modulation a k ha ha1 hk χ hχ Q hQ M R p hR
  have hnorm : ‖P f₀‖ ≤ A * ‖p‖ := by rw [hzero]; exact hbound M hM p hp hplog
  have hd := physicalStartingPerturbation_data_bound a k ha ha1 hk χ hχ Q hQ M p.1
    (euclideanToTorus ((1 / M.1) • p.2.1)) f f₀
  exact ((norm_le_norm_sub_add (P f) (P f₀)).trans
    (add_le_add hd hnorm)).trans_eq (add_comm _ _)

theorem physicalStartingPerturbation_modulation_coordinates
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (a b k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (hχone : ∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (hS : HasCartesianSymbol (-2 * a) Q)
    (F : Params →L[ℝ] HomogeneousY a k)
    (hphys : ∀ p y, homogeneousPhysicalCLM a k ha ha1 hk (F p) y =
      (p.1 : ℂ) * (Complex.I * Q y) +
      (p.2.2 : ℂ) * (((a : ℂ) - Complex.I * (b : ℂ)) * Q y + cartesianTransport Q y) +
      cartesianDerivative p.2.1 Q y)
    (hF : ∀ p, ContDiff ℝ ∞ (fun y => homogeneousPhysicalCLM a k ha ha1 hk (F p) y))
    (π : HomogeneousY a k →L[ℝ] V) (B : ℝ)
    (hκ : ∀ L : Radius, ‖expandingCoordinates a k ha ha1 hk χ π L‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℝ, ∀ M R : Radius,
      L₀ ≤ M.1 → 2 ≤ M.1 → ∀ p : Params, ‖p‖ ≤ 1 / 2 → ‖p‖ ≤ 2 * Real.log 2 →
      R.1 = expandingRadius M.1 p.2.2 → ∀ f : FourierL2,
      ‖expandingCoordinates a k ha ha1 hk χ π M
          (physicalStartingPerturbation a k ha ha1 hk χ hχ Q hQ M p.1
            (euclideanToTorus ((1 / M.1) • p.2.1)) f) -
        π (F (physicalModulationParameterEquiv b p))‖ ≤
      C * (‖p‖ ^ 2 + ‖p‖ / M.1) +
        ε * ‖(physicalModulationParameterEquiv b).toContinuousLinearMap‖ * ‖p‖ +
        B * ‖sobolevToExpanding a k ha hk‖ *
          ‖f - physicalReferenceData a k ha ha1 hk χ hχ Q hQ R‖ := by
  obtain ⟨C, hC, hc⟩ := physical_modulation_coordinate_error a b k ha ha1 hk χ hχ hχzero hχone
    Q hQ hS F hphys hF π
  refine ⟨C, hC, ?_⟩
  intro ε hε
  obtain ⟨L₀, hL₀⟩ := hc ε hε
  refine ⟨L₀, ?_⟩
  intro M R hM hM2 p hp hplog hR f
  let f₀ := physicalReferenceData a k ha ha1 hk χ hχ Q hQ R
  let P := fun g => physicalStartingPerturbation a k ha ha1 hk χ hχ Q hQ M p.1
    (euclideanToTorus ((1 / M.1) • p.2.1)) g
  let κ := expandingCoordinates a k ha ha1 hk χ π M
  have hzero : P f₀ = modulatedCutoffProfile a k ha ha1 hk χ hχ Q hQ M p :=
    physicalStartingPerturbation_reference_modulation a k ha ha1 hk χ hχ Q hQ M R p hR
  have hd : ‖κ (P f) - κ (P f₀)‖ ≤ B * ‖sobolevToExpanding a k ha hk‖ * ‖f - f₀‖ :=
    (physicalStartingPerturbation_coordinate_data_bound a k ha ha1 hk χ hχ Q hQ M p.1
      (euclideanToTorus ((1 / M.1) • p.2.1)) f f₀ κ).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hκ M) (norm_nonneg _))
        (norm_nonneg _))
  have he := hL₀ M hM hM2 p hp hplog
  rw [← hzero] at he
  exact (norm_sub_le_norm_sub_add_norm_sub (κ (P f)) (κ (P f₀)) _).trans
    ((add_le_add hd he).trans_eq (by ring))

end DefocusingNLS

end OAI
