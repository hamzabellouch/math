import OAI.MeasureTheory.Falconer.Shells.FiniteShellIntegrability
import OAI.MeasureTheory.Falconer.Estimates.ScalarInverseTransfer

namespace OAI

/-! # Finite spatial factorization controls the scalar distance shell -/

namespace Falconer
open Set MeasureTheory

theorem finite_spatial_scalar_shell_le {d : ℕ} {ι : Type*} (S : Finset ι)
    (a v : ℝ) (Ψ : ℝ → ℝ) (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hzero : ∀ x ≤ 0, Ψ x = 0) (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (j : ι → ℕ)
    (U V : ι → Space d × (ℝ × Sphere d) → ℂ)
    (hU : ∀ i ∈ S, Measurable (U i)) (hV : ∀ i ∈ S, Measurable (V i))
    (B C : ι → ℝ) (hB : ∀ i ∈ S, 0 ≤ B i) (hC : ∀ i ∈ S, 0 ≤ C i)
    (hbU : ∀ i ∈ S, ∀ z, ‖U i z‖ ≤ B i)
    (hbV : ∀ i ∈ S, ∀ z, ‖V i z‖ ≤ C i)
    (c : ι → ℝ → ℂ) (A H : ι → ℝ)
    (hc : ∀ i ∈ S, Measurable (c i)) (hA : ∀ i ∈ S, 0 ≤ A i)
    (hbound : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      ∀ i ∈ S, ‖c i r‖ ≤ A i)
    (hH : ∀ i ∈ S, ∀ ξ : Space d, independentAngularEnergy a v Ψ
      (fun p => U i (ξ,p)) (fun p => V i (ξ,p)) ≤ H i)
    (F : ℝ → ℂ) (hF : Measurable F) {ε : ℝ}
    (herr : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      ‖F r-(((2:ℝ)^((v-a)*((d:ℝ)-1)/2):ℝ):ℂ)*
        (∑ i ∈ S, c i r *
          spatialSharedAmplitude (spatialFourierCoeff δ L hδ hL (j i)) (U i) (V i) r)‖ ≤ ε) :
    IntegrableOn (fun r => ‖F r‖^2) (Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1))) ∧
      (2:ℝ)^(-a)*(∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖F r‖^2) ≤
        2*((S.card:ℝ)*∑ i ∈ S, (A i)^2*
          ((spatialFourierCost (d := d) δ L hδ hL (j i))^2*H i)) +
        2*(2:ℝ)^(v-a)*ε^2*(PlanarFalconer.sourceAngularShellMeasure v Ψ).real univ := by
  exact scalar_shell_of_stationary_approximation d a v Ψ hΨ hpos hzero hone F
    (fun r => ∑ i ∈ S, c i r *
      spatialSharedAmplitude (spatialFourierCoeff δ L hδ hL (j i)) (U i) (V i) r) hF
    (finite_spatial_shell_sq_integrable S v Ψ δ L hδ hL j U V hU hV B C hB hC
      hbU hbV c A hc hA hbound)
    herr (finite_spatial_shell_le S a v Ψ δ L hδ hL j U V hU hV B C hB hC
      hbU hbV c A H hc hA hbound hH)

end Falconer

end OAI
