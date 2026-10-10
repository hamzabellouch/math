import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffCoordinateOperator

namespace OAI

/-! # The actual contour coordinates have vanishing torus transfer defect -/

open Set
open scoped SchwartzMap ContDiff NNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

theorem sampledCutoffProfile_contour_coordinate_operator (a b k T Q C₀ : ℝ)
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
    (P : (HomogeneousY a k × HomogeneousY a k) →L[ℂ] (HomogeneousY a k × HomogeneousY a k))
    (hfin : FiniteDimensional ℂ P.range)
    (hcomm : ∀ t, Commute (homogeneousComplexLinearizedStep a b k ha ha1 (by linarith) m Q₀ t) P) :
    let π := homogeneousStableCoordinates a k ha ha1 (by linarith) P
    let A := (projectionSemigroupRestriction
      (homogeneousComplexLinearizedStep a b k ha ha1 (by linarith) m Q₀)
      P hcomm ⟨T, hT⟩).restrictScalars ℝ
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℝ, ∀ L : Radius, L₀ ≤ L.1 →
      ‖(expandingCoordinates a k ha ha1 (by linarith) χ π
          (expandingRadiusCurve L.1 T L.2 ⟨T, hT, le_rfl⟩)).comp
          (expandingProfileEndpoint a b k L.1 T ha ha1 (by linarith) L.2 hT m Q hQ
            (sampledCutoffProfilePath a k L.1 T ha ha1 (by linarith) L.2 χ hχ Qp hQp)
            (fun t => hqb (expandingRadiusCurve L.1 T L.2 t))) -
        A.comp (expandingCoordinates a k ha ha1 (by linarith) χ π L)‖ ≤ ε := by
  intro π A
  let : FiniteDimensional ℂ P.range := hfin
  let : FiniteDimensional ℝ P.range := FiniteDimensional.trans ℝ ℂ P.range
  apply sampledCutoffProfile_coordinate_operator_norm a b k T Q C₀ ha ha1 hk hT hQ hC₀
    m χ hχ hχzero hχone Qp hQp Q₀ hQ₀ hqb hCb π A
  intro u
  exact homogeneousStableCoordinates_slab a b k T ha ha1 (by linarith) hT m Q₀ P hcomm
    ⟨T, hT, le_rfl⟩ u

end DefocusingNLS

end OAI
