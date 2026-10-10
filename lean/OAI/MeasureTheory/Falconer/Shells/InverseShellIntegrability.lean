import OAI.MeasureTheory.Falconer.Fourier.StationaryShellIntegrability
import OAI.MeasureTheory.Falconer.Shells.InverseShell

namespace OAI

/-! # Square integrability of the actual integrated inverse on the source shell -/

namespace Falconer
open Set MeasureTheory

theorem integrated_inverse_shell_sq_integrable (n J k : ℕ)
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
    (hnorm : ∀ j ∈ Finset.range (J+1), ∀ i,
      ChartSymbolControl k (normalizedEndpoint (A j i*D^(p j i)) (fun x w => (S j).left i x w)) 1 D ∧
      ChartSymbolControl k (normalizedEndpoint (E j i*D^(q j i)) (fun x w => (S j).right i x w)) 1 D)
    (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (hregime : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      0 < r*s ∧ D^2 ≤ r*s ∧ r*s ≤ 4*(2:ℝ)^(v-a))
 :
    Integrable (fun r => ‖((M⁻¹*P⁻¹) • (∫ z : Space (n+3) × Space (n+3),
          scaledWeightedInverseSum n J s r (z.1-z.2) (fun w => B z.1 w*C z.2 w) ∂μ.prod ν)) /
        (((2:ℝ)^((v-a)*(((n+2:ℕ):ℝ)/2)) : ℝ) : ℂ)‖^2)
      (PlanarFalconer.sourceAngularShellMeasure v Ψ) := by
  classical
  let I := (Finset.range (J+1)).sigma (fun j => (Finset.univ : Finset (S j).index))
  have hi (z : Σ j : ℕ, (S j).index) (hz : z ∈ I) : z.1 ∈ Finset.range (J+1) :=
    (Finset.mem_sigma.mp hz).1
  have hid (r : ℝ) :
      ((M⁻¹*P⁻¹) • (∫ z : Space (n+3) × Space (n+3),
        scaledWeightedInverseSum n J s r (z.1-z.2) (fun w => B z.1 w*C z.2 w) ∂μ.prod ν)) /
        (((2:ℝ)^((v-a)*(((n+2:ℕ):ℝ)/2)) : ℝ) : ℂ) =
      ∑ z ∈ I,
        ((((r*s)^(((n+2:ℕ):ℝ)/2)*((r*s)^z.1)⁻¹*
          ((A z.1 z.2*D^(p z.1 z.2))*(E z.1 z.2*D^(q z.1 z.2)))/
          (2:ℝ)^((v-a)*(((n+2:ℕ):ℝ)/2))) : ℝ) : ℂ)*
        spatialSharedAmplitude (spatialFourierCoeff δ L hδ hL z.1)
          (spatialEndpointFamily μ M s
            (normalizedEndpoint (A z.1 z.2*D^(p z.1 z.2)) (fun x w => (S z.1).left z.2 x w)))
          (spatialEndpointFamily ν P s (fun x w =>
            star (normalizedEndpoint (E z.1 z.2*D^(q z.1 z.2)) (fun x w => (S z.1).right z.2 x w) x w))) r := by
    rw [scaled_inverse_normalized_integration n J δ L hδ hL hs hD μ ν hsep M P B C S
      hvalue hmeas p q A E hA hE
      (fun j hj i => (hnorm j hj i).1.bound)
      (fun j hj i => (hnorm j hj i).2.bound)]
    rw [Finset.sum_div]
    simp_rw [Finset.sum_div]
    rw [Finset.sum_sigma']
    apply Finset.sum_congr rfl
    intro z _
    simp only [Complex.ofReal_div,Complex.ofReal_mul,pow_add]
    ring
  simp_rw [hid]
  exact stationary_factor_shell_sq_integrable I μ ν hM hP a v s Ψ δ L hδ hL
    (fun z => z.1) (fun z => p z.1 z.2) (fun z => q z.1 z.2)
    (fun z => A z.1 z.2) (fun z => E z.1 z.2) hD (by positivity)
    (fun z hz => hpq z.1 (hi z hz) z.2)
    (fun z hz => (hA z.1 (hi z hz) z.2).le)
    (fun z hz => (hE z.1 (hi z hz) z.2).le)
    (fun z => normalizedEndpoint (A z.1 z.2*D^(p z.1 z.2)) (fun x w => (S z.1).left z.2 x w))
    (fun z => normalizedEndpoint (E z.1 z.2*D^(q z.1 z.2)) (fun x w => (S z.1).right z.2 x w))
    (fun z hz => (hnorm z.1 (hi z hz) z.2).1.measurable)
    (fun z hz => (hnorm z.1 (hi z hz) z.2).2.measurable)
    (fun z hz => (hnorm z.1 (hi z hz) z.2).1.bound)
    (fun z hz => (hnorm z.1 (hi z hz) z.2).2.bound)
    hregime

end Falconer

end OAI
