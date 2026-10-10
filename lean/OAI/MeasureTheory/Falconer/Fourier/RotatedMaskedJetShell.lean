import OAI.MeasureTheory.Falconer.Estimates.RotatedInverseScalar
import OAI.MeasureTheory.Falconer.Fourier.BaseJetAmplitude
import OAI.MeasureTheory.Falconer.Estimates.RotatedMaskedRemainder
import OAI.MeasureTheory.Falconer.Shells.MaskedDistanceBounds

namespace OAI

/-! # The actual masked distance shell in the recursive jet class

The inverse family is constructed from the zero-jet root, with constants
chosen before the masks, scale, and endpoint measures. The only analytic
inputs are the published gnomonic formula and quadratic stationary phase.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

theorem exists_rotated_masked_jet_shell_order
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (n : ℕ) {κ Z : ℝ} (hκ : 0 < κ) :
    ∃ k : ℕ, ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ L : ℕ,
      ∃ A : Fin (k+1) → ℝ, (∀ j, 1 ≤ A j) ∧
      ∀ R E δ W C : ℝ, 1 ≤ R → 1 ≤ E → E ≤ R^2 → ∀ (hδ : 0 < δ) (hW : 0 < W), 1 ≤ C →
      ∀ (T : Space (n+3) ≃ₗᵢ[ℝ] Space (n+3)) (w₀ : Sphere (n+3)) (Q : DyadicCube (n+3)) (ρ : Measure (Space (n+3)))
        [IsFiniteMeasure ρ] (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
        (F : Finset PolicyDescriptor) (S : PolicyDescriptor → Finset (Sphere (n+3)))
        (X Y : DyadicCube (n+3)),
      (∀ b ∈ F, ∀ w : Sphere (n+3), ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2) →
      (∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E) →
      (∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
        δ ≤ dist z.1 z.2*(2:ℝ)^a ∧ dist z.1 z.2*(2:ℝ)^a ≤ W) →
      (∀ᵐ z : Space (n+3) × Space (n+3) ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
        ‖T (NormedSpace.normalize (z.1-z.2))-(gnomonicChart (0 : Space (n+2)) : Space (n+3))‖ ≤ 1/8) →
      (∀ x y l, l ≤ 2*(k+1)+(n+2)+1 → ∀ w : Sphere (n+3),
        ‖iteratedFDeriv ℝ l (descriptorPairAmplitude Q ρ (fun u => profile (u/N)) N σ J i F S x y) w‖ ≤ C*E^l) →
      ∀ U : ℝ, 0 < U → ∀ (v : ℝ) (Ψ : ℝ → ℝ),
      Measurable Ψ → (∀ x, 0 ≤ Ψ x) → (∀ x ≤ 0, Ψ x = 0) →
      (∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) →
      ∀ [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)],
      (∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
        0 < r*((2:ℝ)^a)⁻¹ ∧ E^2 ≤ r*((2:ℝ)^a)⁻¹ ∧
          r*((2:ℝ)^a)⁻¹ ≤ 4*(2:ℝ)^(v-a)) →
      (∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
        ∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
          1 ≤ r*dist z.1 z.2 ∧ E^2/(r*dist z.1 z.2) ≤ R^(-κ)) →
      (2:ℝ)^(-(a:ℝ)) *
          (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)),
            ‖charFun (maskedCellDistance w₀ Q ρ profile N σ J i a F S X Y) r‖^2) ≤
        2*(rotatedInverseShellCost n k F A U δ W hδ hW *
          jetStateEnvelope (n+1) (2*k) L 1 F F Q ρ (fun u => profile (u/N)) N σ J i S U
            (ρ.restrict X.carrier) (ρ.restrict Y.carrier)
            (profileModelMass profile N a) (profileModelMass profile N a) a v Ψ) +
        2*(2:ℝ)^(v-a)*
          (|(profileModelMass profile N a)⁻¹*(profileModelMass profile N a)⁻¹| *
            ((δ^(-(((n+2:ℕ):ℝ)/2))*A₀*C*R^(-Z))*
              ((ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)).real univ))^2*
          (PlanarFalconer.sourceAngularShellMeasure v Ψ).real univ := by
  obtain ⟨k,A₀,hA₀,hrem⟩ := exists_rotated_masked_fourier_inverse_order hgnomonic hquadratic n (Z := Z) hκ
  refine ⟨k,A₀,hA₀,?_⟩
  intro L
  choose A hA hfamily using fun j : Fin (k+1) => exists_rotatedRootSymbols n j.val L
  refine ⟨A,hA,?_⟩
  intro R E δ W C hR hE hER hδ hW hC T w₀ Q ρ _ profile N σ J i a F S X Y
    hcover hseparated hradius hsep hnear hderiv U hU v Ψ hΨ hpos hzero hone _ hregime hfreq
  let family (j : Fin (k+1)) : RotatedRootSymbols n j.val L F T (A j) :=
    Classical.choice (hfamily j F T)
  have hM : 0 < profileModelMass profile N a := by unfold profileModelMass; positivity
  have hsep' : ∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
      δ ≤ dist z.1 z.2/((2:ℝ)^a)⁻¹ ∧ dist z.1 z.2/((2:ℝ)^a)⁻¹ ≤ W := by
    simpa only [div_inv_eq_mul] using hsep
  have hInt (r : ℝ) : Integrable (fun z : Space (n+3) × Space (n+3) =>
      rotatedScaledWeightedInverseSum n k T ((2:ℝ)^a)⁻¹ r (z.1-z.2)
        (descriptorPairAmplitude Q ρ (fun u => profile (u/N)) N σ J i F S z.1 z.2))
      ((ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)) := by
    exact rotated_inverse_jet_integrable k A family (fun j => zero_lt_one.trans_le (hA j))
      Q ρ (fun u => profile (u/N)) N σ J i S hseparated hU δ hδ
      ((2:ℝ)^a)⁻¹ (ρ.restrict X.carrier) (ρ.restrict Y.carrier) (hsep'.mono fun _ hz => hz.1) r
  let := maskedCellDistance_finite w₀ Q ρ profile N σ J i a F S hcover (by omega)
    hδ X Y (hsep.mono fun _ hz => hz.1)
  have hscalar := scalar_shell_of_rotated_inverse k A family
    (fun j => zero_lt_one.trans_le (hA j))
    Q ρ (fun u => profile (u/N)) N σ J i S hseparated hU hE
    hradius δ W hδ hW (by positivity) (ρ.restrict X.carrier) (ρ.restrict Y.carrier)
    hsep' hM hM a v Ψ hΨ hpos hzero hone hregime
    (charFun (maskedCellDistance w₀ Q ρ profile N σ J i a F S X Y)) measurable_charFun
    (ε := |(profileModelMass profile N a)⁻¹*(profileModelMass profile N a)⁻¹| *
      (δ^(-(((n+2:ℕ):ℝ)/2))*A₀*C*R^(-Z)*
        ((ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)).real univ))
  have hb := hscalar (by
    filter_upwards [hfreq] with r hr
    rw [norm_sub_rev]
    exact hrem T R E r δ hR hE hER hδ w₀ Q ρ profile N σ J i a F S X Y hcover
      (hsep.mono fun _ hz => hz.1) hnear hr C hC hderiv (hInt r))
  exact hb.2

end Falconer

end OAI
