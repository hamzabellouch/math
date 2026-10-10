import OAI.Geometry.RCD.Sobolev.CompactMixedEnergy
import OAI.Geometry.RCD.Sobolev.SobolevCompactSupport
import OAI.Geometry.RCD.Coordinates.RegularDirichletCore
import OAI.Geometry.RCD.Sobolev.WeakRadialCancellation

namespace OAI

/-! # The integrated Hessian formula for regular Poisson functions -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.compact_test_gradient {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n) (p : X)
    {Ω : Set X} (hΩ : IsOpen Ω)
    (f : SobolevSpace (hausdorff n X) hX.quadratic)
    {v : X → ℝ} {L : ℝ≥0} (hv : LipschitzWith L v) (hc : HasCompactSupport v)
    (hf : SobolevSpace.toLp (hausdorff n X) hX.quadratic f =ᵐ[hausdorff n X] v)
    (df : Lp ℝ 2 (hausdorff n X)) (hdf : IsWeakLaplacian (hausdorff n X) hX.quadratic f df)
    (φ : regularDirichletCore (hausdorff n X) hX.quadratic Ω) :
    ∃ G : SobolevSpace.dirichlet (hausdorff n X) hX.quadratic Ω,
      SobolevSpace.toLp (hausdorff n X) hX.quadratic G.val =ᵐ[hausdorff n X]
        localGamma (hausdorff n X) hX.quadratic f φ.val.val := by
  obtain ⟨w,M,hw,hwc,hws,hwr⟩ := φ.property.1
  obtain ⟨dφ,hdφ⟩ := φ.property.2
  obtain ⟨G,hG⟩ := hX.compact_mixed_energy hn p f φ.val.val hv hc hf hw hwc hwr df dφ hdf hdφ
  exact ⟨⟨G,hX.gamma_representative_mem_dirichlet hn hΩ f φ.val.val G hwc hws hwr hG⟩,hG⟩

/-- All Sobolev representatives in the Koszul identity are constructed
from the RCD energy-density theorem and a proved dense compact core. -/
theorem NoncollapsedRCD.compact_poisson_hessian_pairing {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n) (p : X)
    {Ω : Set X} (hΩ : IsOpen Ω)
    (f a : SobolevSpace (hausdorff n X) hX.quadratic)
    {v w : X → ℝ} {L M : ℝ≥0}
    (hv : LipschitzWith L v) (hvc : HasCompactSupport v)
    (hfr : SobolevSpace.toLp (hausdorff n X) hX.quadratic f =ᵐ[hausdorff n X] v)
    (hw : LipschitzWith M w) (hwc : HasCompactSupport w)
    (har : SobolevSpace.toLp (hausdorff n X) hX.quadratic a =ᵐ[hausdorff n X] w)
    (df da : Lp ℝ 2 (hausdorff n X))
    (hdf : IsWeakLaplacian (hausdorff n X) hX.quadratic f df)
    (hda : IsWeakLaplacian (hausdorff n X) hX.quadratic a da)
    (c d : ℝ)
    (hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic Ω f c)
    (ha : IsConstantLaplacianOn (hausdorff n X) hX.quadratic Ω a d) :
    Nonempty (LocalHessianPairing (hausdorff n X) hX.quadratic Ω f a) := by
  let μ := hausdorff n X
  obtain ⟨G,hG⟩ := hX.compact_mixed_energy hn p f a hv hvc hfr hw hwc har df da hdf hda
  choose γf hγf using hX.compact_test_gradient hn p hΩ f hv hvc hfr df hdf
  choose γa hγa using hX.compact_test_gradient hn p hΩ a hw hwc har da hda
  let H : SobolevSpace.dirichlet μ hX.quadratic Ω →L[ℝ] ℝ :=
    (1/2 : ℝ) • ((sobolevEnergyForm μ hX.quadratic G).comp
      (SobolevSpace.dirichlet μ hX.quadratic Ω).subtypeL)
  refine ⟨{
    mixed := G
    mixed_rep := ae_restrict_of_ae hG
    core := regularDirichletCore μ hX.quadratic Ω
    core_dense := hX.regularDirichletCore_dense hn hΩ
    gammaF := γf
    gammaA := γa
    gammaF_rep := hγf
    gammaA_rep := hγa
    hessian := H
    koszul := ?_ }⟩
  intro φ
  have hif : (∫ x in Ω, SobolevSpace.toLp μ hX.quadratic (γf φ).val x ∂μ) =
      energyForm μ hX.quadratic f φ.val.val := by
    rw [integral_congr_ae (ae_restrict_of_ae (hγf φ))]
    exact integral_localGamma_dirichlet μ hX.quadratic Ω hΩ.measurableSet f φ.val
  have hia : (∫ x in Ω, SobolevSpace.toLp μ hX.quadratic (γa φ).val x ∂μ) =
      energyForm μ hX.quadratic a φ.val.val := by
    rw [integral_congr_ae (ae_restrict_of_ae (hγa φ))]
    exact integral_localGamma_dirichlet μ hX.quadratic Ω hΩ.measurableSet a φ.val
  have heq : energyForm μ hX.quadratic a (γf φ).val =
      energyForm μ hX.quadratic f (γa φ).val := by
    rw [ha _ (γf φ).property,hf _ (γa φ).property,hif,hia,
      hf _ φ.val.property,ha _ φ.val.property]
    ring
  change 2*((1/2 : ℝ)*energyForm μ hX.quadratic G φ.val.val) = _
  rw [heq,energyForm_comm μ hX.quadratic G φ.val.val]
  ring

end RegularPointCoordinates

end

end OAI
