import OAI.Geometry.RCD.Sobolev.LocalPoissonHessianPairing

namespace OAI

/-! # Cancellation of both constant-source terms in the integrated Hessian -/

open Set MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Constant Laplacians cancel each other in the integrated Koszul formula,
so the mixed-gradient energy pairing equals twice the Hessian action. -/
theorem LocalHessianPairing.constant_source_identity {Ω : Set X} (hΩ : MeasurableSet Ω)
    {f a : SobolevSpace μ hQ} (G : LocalHessianPairing μ hQ Ω f a)
    {c d : ℝ} (hf : IsConstantLaplacianOn μ hQ Ω f c)
    (ha : IsConstantLaplacianOn μ hQ Ω a d)
    (φ : SobolevSpace.dirichlet μ hQ Ω) :
    energyForm μ hQ G.mixed φ.val = 2*G.hessian φ := by
  let F := (sobolevEnergyForm μ hQ G.mixed).comp (SobolevSpace.dirichlet μ hQ Ω).subtypeL
  have heq : (F : SobolevSpace.dirichlet μ hQ Ω → ℝ) = (2 : ℝ) • G.hessian := by
    apply Continuous.ext_on G.core_dense F.continuous ((2 : ℝ) • G.hessian).continuous
    intro ψ hψ
    let z : G.core := ⟨ψ,hψ⟩
    have hif : (∫ x in Ω, SobolevSpace.toLp μ hQ (G.gammaF z).val x ∂μ) =
        energyForm μ hQ f ψ.val := by
      rw [integral_congr_ae (ae_restrict_of_ae (G.gammaF_rep z))]
      exact integral_localGamma_dirichlet μ hQ Ω hΩ f ψ
    have hia : (∫ x in Ω, SobolevSpace.toLp μ hQ (G.gammaA z).val x ∂μ) =
        energyForm μ hQ a ψ.val := by
      rw [integral_congr_ae (ae_restrict_of_ae (G.gammaA_rep z))]
      exact integral_localGamma_dirichlet μ hQ Ω hΩ a ψ
    have hs : energyForm μ hQ a (G.gammaF z).val = energyForm μ hQ f (G.gammaA z).val := by
      rw [ha _ (G.gammaF z).property,hf _ (G.gammaA z).property,hif,hia,
        hf _ ψ.property,ha _ ψ.property]
      ring
    have hk := G.koszul z
    rw [hs,energyForm_comm μ hQ ψ.val G.mixed] at hk
    change energyForm μ hQ G.mixed ψ.val = 2*G.hessian ψ
    linarith only [hk]
  exact congrFun heq φ

/-- The action is independent of all choices of compact extensions and
regular cores. This allows estimates proved for any local construction
to use the same Hessian action. -/
theorem LocalHessianPairing.hessian_unique_of_constant_sources {Ω : Set X}
    (hΩ : MeasurableSet Ω) {f a : SobolevSpace μ hQ}
    (G H : LocalHessianPairing μ hQ Ω f a) {c d : ℝ}
    (hf : IsConstantLaplacianOn μ hQ Ω f c)
    (ha : IsConstantLaplacianOn μ hQ Ω a d) : G.hessian = H.hessian := by
  apply ContinuousLinearMap.ext
  intro φ
  have he := energyForm_eq_of_ae_eq_on μ hQ hΩ
    (G.mixed_rep.trans (Filter.EventuallyEq.symm H.mixed_rep)) φ
  rw [G.constant_source_identity μ hQ hΩ hf ha,
    H.constant_source_identity μ hQ hΩ hf ha] at he
  linarith

/-- The exact factor two in the shifted divergence identity applies to
both Poisson functions, including a nonzero constant source. -/
theorem LocalHessianPairing.shifted_source_identity {Ω : Set X}
    (hΩ : MeasurableSet Ω) {f a : SobolevSpace μ hQ}
    (G : LocalHessianPairing μ hQ Ω f a) {c d : ℝ}
    (hf : IsConstantLaplacianOn μ hQ Ω f c)
    (ha : IsConstantLaplacianOn μ hQ Ω a d)
    (b : ℝ) (φ : SobolevSpace.dirichlet μ hQ Ω) :
    energyForm μ hQ G.mixed φ.val - 2*b*energyForm μ hQ a φ.val =
      2*(G.hessian φ-b*energyForm μ hQ a φ.val) := by
  rw [G.constant_source_identity μ hQ hΩ hf ha]
  ring

end RegularPointCoordinates

end

end OAI
