import OAI.Geometry.RCD.Sobolev.CompactPoissonHessian
import OAI.Geometry.RCD.Sobolev.PoissonHessianIdentity

namespace OAI

/-! # Replacing the local Hessian core without changing its functional -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- For compact Poisson functions, the actual dense regular core can be
installed while preserving the given Hessian functional and mixed Gram
representative. This makes bounds independent of a prior core choice. -/
theorem NoncollapsedRCD.hessian_pairing_regular_core {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (p : X)
    {Ω : Set X} (hΩ : IsOpen Ω)
    (f a : compactLaplacianCore (hausdorff n X) hX.quadratic univ)
    (c d : ℝ)
    (hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic Ω f.val c)
    (ha : IsConstantLaplacianOn (hausdorff n X) hX.quadratic Ω a.val d)
    (G : LocalHessianPairing (hausdorff n X) hX.quadratic Ω f.val a.val) :
    ∃ H : LocalHessianPairing (hausdorff n X) hX.quadratic Ω f.val a.val,
      H.core=regularDirichletCore (hausdorff n X) hX.quadratic Ω ∧
      H.mixed=G.mixed ∧ H.hessian=G.hessian := by
  let μ := hausdorff n X
  let hQ := hX.quadratic
  obtain ⟨v,L,hv,hvc,-,hfr⟩ := f.property.1
  obtain ⟨w,M,hw,hwc,-,har⟩ := a.property.1
  obtain ⟨df,hdf⟩ := f.property.2
  obtain ⟨da,hda⟩ := a.property.2
  choose γf hγf using hX.compact_test_gradient hn p hΩ f.val hv hvc hfr df hdf
  choose γa hγa using hX.compact_test_gradient hn p hΩ a.val hw hwc har da hda
  refine ⟨{ G with
    core := regularDirichletCore μ hQ Ω
    core_dense := hX.regularDirichletCore_dense hn hΩ
    gammaF := γf
    gammaA := γa
    gammaF_rep := hγf
    gammaA_rep := hγa
    koszul := ?_ },rfl,rfl,rfl⟩
  intro φ
  have hif : (∫ x in Ω, SobolevSpace.toLp μ hQ (γf φ).val x ∂μ)=
      energyForm μ hQ f.val φ.val.val := by
    rw [integral_congr_ae (ae_restrict_of_ae (hγf φ))]
    exact integral_localGamma_dirichlet μ hQ Ω hΩ.measurableSet f.val φ.val
  have hia : (∫ x in Ω, SobolevSpace.toLp μ hQ (γa φ).val x ∂μ)=
      energyForm μ hQ a.val φ.val.val := by
    rw [integral_congr_ae (ae_restrict_of_ae (hγa φ))]
    exact integral_localGamma_dirichlet μ hQ Ω hΩ.measurableSet a.val φ.val
  have he : energyForm μ hQ a.val (γf φ).val=energyForm μ hQ f.val (γa φ).val := by
    rw [ha _ (γf φ).property,hf _ (γa φ).property,hif,hia,
      hf _ φ.val.property,ha _ φ.val.property]
    ring
  have hG := G.constant_source_identity μ hQ hΩ.measurableSet hf ha φ.val
  rw [he,energyForm_comm μ hQ φ.val.val G.mixed]
  linarith only [hG]

end RegularPointCoordinates

end

end OAI
