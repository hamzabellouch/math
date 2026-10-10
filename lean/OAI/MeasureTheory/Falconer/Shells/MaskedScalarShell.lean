import OAI.MeasureTheory.Falconer.Shells.InverseEnvelopeShell
import OAI.MeasureTheory.Falconer.Estimates.MaskedInverseRemainder
import OAI.MeasureTheory.Falconer.Shells.MaskedDistanceBounds

namespace OAI

/-! # The weighted scalar shell for the original masked distance law

The only analytic inputs are the precisely published gnomonic formula and
quadratic stationary phase. The error and all finite-factor costs remain
explicit until the uniform scale absorption step.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem exists_masked_scalar_shell_order
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (n : ℕ) {κ T : ℝ} (hκ : 0 < κ) :
    ∃ K : ℕ, ∃ A₀ : ℝ, 0 ≤ A₀ ∧
      ∀ (R D δ L C₀ : ℝ) (_hR : 1 ≤ R) (_hD : 1 ≤ D) (_hDR : D ≤ R^2)
        (hδ : 0 < δ) (hL : 0 < L) (_hC₀ : 1 ≤ C₀),
      ∀ (w₀ : Sphere (n+3)) (Q : DyadicCube (n+3)) (ρ : Measure (Space (n+3)))
        [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
        (B : Finset PlanarFalconer.PolicyDescriptor)
        (V : PlanarFalconer.PolicyDescriptor → Finset (Sphere (n+3)))
        (X Y : DyadicCube (n+3)),
      (∀ b ∈ B, ∀ w : Sphere (n+3), ∃ c ∈ V b, dist w c ≤ descriptorMaskRadius N σ b/2) →
      (∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
        δ ≤ dist z.1 z.2*(2:ℝ)^a ∧ dist z.1 z.2*(2:ℝ)^a ≤ L) →
      (∀ᵐ z : Space (n+3) × Space (n+3) ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
        ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (n+2)) : Space (n+3))‖ ≤ 1/8) →
      (∀ x y l, l ≤ 2*(K+1)+(n+2)+1 → ∀ w : Sphere (n+3),
        ‖iteratedFDeriv ℝ l (descriptorPairAmplitude Q ρ (fun u => m (u/N)) N σ J i B V x y) w‖ ≤ C₀*D^l) →
      ∀ (S : ℕ → SmoothSeparation (Space (n+3)) (Space (n+3)) (Space (n+3))),
      (∀ j ∈ Finset.range (K+1), ∀ x y (w : Sphere (n+3)),
        localInverseAmplitude n
          (descriptorPairAmplitude Q ρ (fun u => m (u/N)) N σ J i B V x y) j w = (S j).value x y w) →
      (∀ j ∈ Finset.range (K+1), ∀ u : (S j).index,
        Measurable (Function.uncurry (fun x w => (S j).left u x w)) ∧
          Measurable (Function.uncurry (fun x w => (S j).right u x w))) →
      ∀ (p q : (j : ℕ) → (S j).index → ℕ) (A E : (j : ℕ) → (S j).index → ℝ),
      (∀ j ∈ Finset.range (K+1), ∀ u, 0 < A j u) →
      (∀ j ∈ Finset.range (K+1), ∀ u, 0 < E j u) →
      (∀ j ∈ Finset.range (K+1), ∀ u, p j u+q j u ≤ 2*j) →
      ∀ (k : ℕ) (GoodLeft GoodRight : Set (Space (n+3) × Sphere (n+3))),
      (∀ j ∈ Finset.range (K+1), ∀ u,
        AngularAdmissible k D GoodLeft
          (normalizedEndpoint (A j u*D^(p j u)) (fun x w => (S j).left u x w)) ∧
        AngularAdmissible k D GoodRight
          (normalizedEndpoint (E j u*D^(q j u)) (fun x w => (S j).right u x w))) →
      ∀ (v : ℝ) (Ψ : ℝ → ℝ), Measurable Ψ → (∀ x, 0 ≤ Ψ x) →
      (∀ x ≤ 0, Ψ x = 0) → (∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) →
      ∀ [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)],
      (∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
        0 < r*((2:ℝ)^a)⁻¹ ∧ D^2 ≤ r*((2:ℝ)^a)⁻¹ ∧
          r*((2:ℝ)^a)⁻¹ ≤ 4*(2:ℝ)^(v-a)) →
      (∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
        ∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
          1 ≤ r*dist z.1 z.2 ∧ D^2/(r*dist z.1 z.2) ≤ R^(-κ)) →
      let I := (Finset.range (K+1)).sigma (fun j => (Finset.univ : Finset (S j).index))
      (2:ℝ)^(-(a:ℝ)) *
          (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)),
            ‖charFun (maskedCellDistance w₀ Q ρ m N σ J i a B V X Y) r‖^2) ≤
        2*((I.card:ℝ)*∑ z ∈ I, (A z.1 z.2*E z.1 z.2*4^(((n+2:ℕ):ℝ)/2))^2*
          ((spatialFourierCost (d := n+3) δ L hδ hL z.1)^2*
            angularEnvelope (ρ.restrict X.carrier) (ρ.restrict Y.carrier)
              (profileModelMass m N a) (profileModelMass m N a) k D a v Ψ GoodLeft GoodRight)) +
        2*(2:ℝ)^(v-a)*
          (|(profileModelMass m N a)⁻¹*(profileModelMass m N a)⁻¹| *
            ((δ^(-(((n+2:ℕ):ℝ)/2))*A₀*C₀*R^(-T))*
              ((ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)).real univ))^2*
          (PlanarFalconer.sourceAngularShellMeasure v Ψ).real univ := by
  obtain ⟨K,A₀,hA₀,hrem⟩ := exists_masked_fourier_inverse_order hgnomonic hquadratic n (T := T) hκ
  refine ⟨K,A₀,hA₀,?_⟩
  intro R D δ L C₀ hR hD hDR hδ hL hC₀ w₀ Q ρ _ m N σ J i a B V X Y
    hcover hsep hnear hderiv S hvalue hmeas p q A E hA hE hpq k GoodLeft GoodRight
    hnorm v Ψ hΨ hpos hzero hone _ hregime hfreq
  have hM : 0 < profileModelMass m N a := by unfold profileModelMass; positivity
  have hsep' : ∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
      δ ≤ dist z.1 z.2/((2:ℝ)^a)⁻¹ ∧ dist z.1 z.2/((2:ℝ)^a)⁻¹ ≤ L := by
    simpa only [div_inv_eq_mul] using hsep
  let F : Space (n+3) → Space (n+3) → ℂ := fun x w =>
    (descriptorAmbientProduct Q ρ (fun u => m (u/N)) N σ J i B V x w : ℂ)
  have hInt (r : ℝ) : Integrable (fun z : Space (n+3) × Space (n+3) =>
      scaledWeightedInverseSum n K ((2:ℝ)^a)⁻¹ r (z.1-z.2)
        (descriptorPairAmplitude Q ρ (fun u => m (u/N)) N σ J i B V z.1 z.2))
      ((ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)) := by
    apply scaledWeightedInverseSum_integrable n K ((2:ℝ)^a)⁻¹ r δ hδ
      (ρ.restrict X.carrier) (ρ.restrict Y.carrier)
      (hsep'.mono fun _ hz => hz.1) _ S hvalue hmeas
      (fun j u => A j u*D^(p j u)) (fun j u => E j u*D^(q j u))
    · intro j hj u
      exact mul_nonneg (hA j hj u).le (pow_nonneg (zero_le_one.trans hD) _)
    · intro j hj u
      exact normalizedEndpoint_bound_restored
        (mul_pos (hA j hj u) (pow_pos (zero_lt_one.trans_le hD) _)) _
        (hnorm j hj u).1.1.bound
    · intro j hj u
      exact normalizedEndpoint_bound_restored
        (mul_pos (hE j hj u) (pow_pos (zero_lt_one.trans_le hD) _)) _
        (hnorm j hj u).2.1.bound
  let := maskedCellDistance_finite w₀ Q ρ m N σ J i a B V hcover (by omega)
    hδ X Y (hsep.mono fun _ hz => hz.1)
  apply (scalar_shell_le_angularEnvelope n K k δ L hδ hL (by positivity) hD
    (ρ.restrict X.carrier) (ρ.restrict Y.carrier) hsep' hM hM F F S
    hvalue hmeas p q A E hA hE hpq GoodLeft GoodRight hnorm
    a v Ψ hΨ hpos hzero hone hregime
    (charFun (maskedCellDistance w₀ Q ρ m N σ J i a B V X Y)) measurable_charFun _).2
  filter_upwards [hfreq] with r hr
  rw [norm_sub_rev]
  exact hrem R D r δ hR hD hDR hδ w₀ Q ρ m N σ J i a B V X Y hcover
    (hsep.mono fun _ hz => hz.1) hnear hr C₀ hC₀ hderiv (hInt r)

end Falconer

end OAI
