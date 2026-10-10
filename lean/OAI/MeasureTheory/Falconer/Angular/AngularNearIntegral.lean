import OAI.MeasureTheory.Falconer.Angular.AngularRestrictedKernel

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem angularNearIntegral_bound
    (Q₁ Q₂ : DyadicSquare) (hQ₁ : Q₁.side = 1) (hQ₂ : Q₂.side = 1)
    (p : ℕ) (C : Finset (CellPath × CellPath))
    (hC : C ⊆ (dyadicPaths p) ×ˢ (dyadicPaths p))
    (U V : CellPath → ℝ × UnitCircle → ℂ)
    (hU : ∀ P, Measurable (U P)) (hV : ∀ Q, Measurable (V Q))
    {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hbU : ∀ P z, ‖U P z‖ ≤ B) (hbV : ∀ Q z, ‖V Q z‖ ≤ D)
    (v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    ‖angularKernelIntegral p v Ψ (angularRestrictedKernel C (angularNear Q₁ Q₂ p) U V)‖ ≤
      3748096 * ∑ row ∈ C, (sourceAngularH p v Ψ (U row.1) (V row.2)).toReal := by
  let := sourceAngularShellMeasure_finite v Ψ hW hw (fun t ht => by
    by_contra hn
    have := (hs t hn).2
    linarith)
  have hz : ∀ t ≤ 0, Ψ t = 0 := by
    intro t ht
    by_contra hn
    have := (hs t hn).1
    linarith
  rw [angularKernelIntegral_original p v hΨ hpos hz _
    (angularRestrictedKernel_measurable C _ U V hU hV)
    (angularRestrictedKernel_bound C _ U V hB hD hbU hbV)]
  apply original_product_schur_integral C (fun row => U row.1) (fun row => V row.2)
    (fun row _ => hU row.1) (fun row _ => hV row.2) (fun _ => B) (fun _ => D)
    (fun _ _ => hB) (fun _ _ => hD) (fun row _ => hbU row.1) (fun row _ => hbV row.2)
    _ (by norm_num) _ p v hΨ hpos hs hW hw
  intro r u w
  exact angularNearSum_bound Q₁ Q₂ hQ₁ hQ₂ p C hC _ _

end PlanarFalconer

end OAI
