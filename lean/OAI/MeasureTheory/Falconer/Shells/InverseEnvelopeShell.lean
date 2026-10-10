import OAI.MeasureTheory.Falconer.Shells.InverseScalarShell
import OAI.MeasureTheory.Falconer.Angular.AngularEnvelope

namespace OAI

/-! # The actual scalar inverse is bounded by the admissible angular supremum -/

namespace Falconer
open Set MeasureTheory

theorem scalar_shell_le_angularEnvelope (n J k : ℕ)
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) {s D : ℝ} (hs : 0 < s) (hD : 1 ≤ D)
    (μ ν : Measure (Space (n+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ L)
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    (B C : Space (n+3) → Space (n+3) → ℂ)
    (S : ℕ → SmoothSeparation (Space (n+3)) (Space (n+3)) (Space (n+3)))
    (hvalue : ∀ j ∈ Finset.range (J+1), ∀ x y (w : Sphere (n+3)),
      localInverseAmplitude n (fun v => B x v*C y v) j w = (S j).value x y w)
    (hmeas : ∀ j ∈ Finset.range (J+1), ∀ i : (S j).index,
      Measurable (Function.uncurry (fun x w => (S j).left i x w)) ∧
        Measurable (Function.uncurry (fun x w => (S j).right i x w)))
    (p q : (j : ℕ) → (S j).index → ℕ)
    (A E : (j : ℕ) → (S j).index → ℝ)
    (hA : ∀ j ∈ Finset.range (J+1), ∀ i, 0 < A j i)
    (hE : ∀ j ∈ Finset.range (J+1), ∀ i, 0 < E j i)
    (hpq : ∀ j ∈ Finset.range (J+1), ∀ i, p j i+q j i ≤ 2*j)
    (GoodLeft GoodRight : Set (Space (n+3) × Sphere (n+3)))
    (hnorm : ∀ j ∈ Finset.range (J+1), ∀ i,
      AngularAdmissible k D GoodLeft
        (normalizedEndpoint (A j i*D^(p j i)) (fun x w => (S j).left i x w)) ∧
      AngularAdmissible k D GoodRight
        (normalizedEndpoint (E j i*D^(q j i)) (fun x w => (S j).right i x w)))
    (a v : ℝ) (Ψ : ℝ → ℝ)
    (hΨ : Measurable Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hzero : ∀ x ≤ 0, Ψ x = 0)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hregime : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      0 < r*s ∧ D^2 ≤ r*s ∧ r*s ≤ 4*(2:ℝ)^(v-a))
    (F : ℝ → ℂ) (hF : Measurable F) {ε : ℝ}
    (herr : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      ‖F r-(M⁻¹*P⁻¹) • (∫ z : Space (n+3) × Space (n+3),
        scaledWeightedInverseSum n J s r (z.1-z.2) (fun w => B z.1 w*C z.2 w)
          ∂μ.prod ν)‖ ≤ ε) :
    let I := (Finset.range (J+1)).sigma (fun j => (Finset.univ : Finset (S j).index))
    IntegrableOn (fun r => ‖F r‖^2) (Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1))) ∧
      (2:ℝ)^(-a)*(∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖F r‖^2) ≤
        2*((I.card:ℝ)*∑ z ∈ I, (A z.1 z.2*E z.1 z.2*4^(((n+2:ℕ):ℝ)/2))^2*
          ((spatialFourierCost (d := n+3) δ L hδ hL z.1)^2*
            angularEnvelope μ ν M P k D a v Ψ GoodLeft GoodRight)) +
        2*(2:ℝ)^(v-a)*ε^2*(PlanarFalconer.sourceAngularShellMeasure v Ψ).real univ := by
  exact scalar_shell_of_integrated_inverse n J k δ L hδ hL hs hD μ ν hsep hM hP
    B C S hvalue hmeas p q A E hA hE hpq
    (fun j hj i => ⟨(hnorm j hj i).1.1,(hnorm j hj i).2.1⟩)
    a v Ψ hΨ hpos hzero hone hregime
    (fun _ _ => angularEnvelope μ ν M P k D a v Ψ GoodLeft GoodRight)
    (fun j hj i ξ => spatial_endpoint_energy_le_envelope μ ν hM hP k D a v Ψ
      GoodLeft GoodRight _ _ (hnorm j hj i).1 (hnorm j hj i).2 s ξ)
    F hF herr

end Falconer

end OAI
