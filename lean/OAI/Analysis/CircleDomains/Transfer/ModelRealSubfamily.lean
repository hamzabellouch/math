import OAI.Analysis.CircleDomains.Rigidity.MaskedModelData
import OAI.Analysis.CircleDomains.Uniformization.RealFiniteModel

namespace OAI

/-! Actual real barrier functions retained on a masked circle model. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

structure ModelRealSubfamily {J I A : Type*} {n N : ℕ}
    {T : J → ℂ ≃ₜ ℂ} {H : I → ℂ ≃ₜ ℂ} {G K : Set (ℝ × ℝ)}
    {M : Fin n → Set (ℝ × ℝ)} {f : Fin n → (ℝ × ℝ) → UnitAddCircle}
    {χ : (ℝ × ℝ) → ℝ} {θ : Fin n → ℝ} {ε : ℝ}
    (Q : MaskedModelData T H G K M f χ N θ ε)
    (ι : A → Fin n) (r : A → (ℝ × ℝ) → ℝ) where
  functions : A → (ℝ × ℝ) → ℝ
  filled : IsFilledCoordinateFamily (fun i => realJordanInterior (H i))
    (G ∪ ⋃ i, realJordanInterior (H i))
    (fun j => cutoffStaircase (r j) χ (shiftedStaircase (reciprocalGridStep N)
      (staircaseWidth (reciprocalGridStep N) Q.widthIndex) (θ (ι j)))) functions
  extension_contains : realChartDomain (completedRegion T) ⊆ G ∪ ⋃ i, realJordanInterior (H i)
  projection : ∀ j x, (functions j x : UnitAddCircle) = Q.functions (ι j) x
  retained : ∀ᶠ x in 𝓝ˢ K, ∀ j, functions j x = r j x
  transported : ∀ j, ContDiffOn ℝ ∞ (functions j ∘ sphereRealMap Q.inverse)
    (realChartDomain Q.domain) ∧
    ∀ x ∈ realChartDomain (openCompletedRegion T),
      ((functions j ∘ sphereRealMap Q.inverse) ∘ sphereRealMap Q.forward) =ᶠ[𝓝 x] functions j
  transported_energy : ∀ j (s : Set (ℝ × ℝ)), MeasurableSet s →
    s ⊆ realChartDomain (openCompletedRegion T) →
    (∫ y in sphereRealMap Q.forward '' s,
      gradientEnergy (functions j ∘ sphereRealMap Q.inverse) (fun _ => 1) y) =
      ∫ x in s, gradientEnergy (functions j) Q.metric x
  metric_conformal : ∀ p ∈ openCompletedRegion T, IsMetricConformalAt Q.metric Q.forward p

end CircleDomainRigidity.FiniteTransfer

end

end OAI
