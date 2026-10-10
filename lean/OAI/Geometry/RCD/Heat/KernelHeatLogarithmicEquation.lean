import OAI.Geometry.RCD.Heat.LocalLogarithmicLaplacian
import OAI.Geometry.RCD.Coordinates.KernelHeatBoundedRegularity
import OAI.Geometry.RCD.Heat.KernelHeatSpatialSource
import OAI.Geometry.RCD.Heat.KernelHeatProductDerivative

namespace OAI

/-! # The local logarithmic heat equation from the actual semigroup

On any compact region where the heat value is positive, the logarithm
has a Sobolev extension with L² Laplacian. Its pointwise time derivative
agrees almost everywhere with that Laplacian plus its squared gradient.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p in
theorem kernelHeat_logarithmic_equation {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (f : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0)
    (hC : ∀ᵐ x ∂hausdorff n X, |f x| ≤ C) {t : ℝ} (ht : 0 < t)
    {Ω : Set X} (hΩ : IsCompact Ω)
    (hpos : ∀ x ∈ Ω, 0 < kernelHeat (hausdorff n X) hX.quadratic hk t f x) :
    ∃ (u v : SobolevSpace (hausdorff n X) hX.quadratic) (q : Lp ℝ 2 (hausdorff n X)),
      (kernelHeat (hausdorff n X) hX.quadratic hk t f =ᵐ[hausdorff n X]
        SobolevSpace.toLp (hausdorff n X) hX.quadratic u) ∧
      IsWeakLaplacian (hausdorff n X) hX.quadratic v q ∧
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic v =ᵐ[(hausdorff n X).restrict Ω]
        fun x => Real.log (kernelHeat (hausdorff n X) hX.quadratic hk t f x)) ∧
      (∀ᵐ x ∂(hausdorff n X).restrict Ω,
        HasDerivAt (fun s => Real.log (kernelHeat (hausdorff n X) hX.quadratic hk s f x))
          (q x + localGamma (hausdorff n X) hX.quadratic v v x) t) ∧
      ∀ w : SobolevSpace (hausdorff n X) hX.quadratic,
        localGamma (hausdorff n X) hX.quadratic v w =ᵐ[(hausdorff n X).restrict Ω]
          fun x => localGamma (hausdorff n X) hX.quadratic u w x /
            kernelHeat (hausdorff n X) hX.quadratic hk t f x := by
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let H := kernelHeat μ hQ hk t f
  obtain ⟨hLip,hBound⟩ := hX.kernelHeat_bounded_regularity hn p hk f C hC t ht
  obtain ⟨u,d,hu,hd,hD⟩ := kernelHeat_spatial_source μ hQ hk f ht
  let U := SobolevSpace.toLp μ hQ u
  obtain ⟨a,ha,haH⟩ := hΩ.exists_forall_le' hLip.continuous.continuousOn hpos
  have hval : ∀ᵐ x ∂μ.restrict Ω, U x ∈ Icc a (max a C) := by
    filter_upwards [ae_restrict_of_ae hu,(ae_restrict_mem hΩ.measurableSet)] with x hx hmem
    rw [← hx]
    exact ⟨haH x hmem,(le_abs_self _).trans ((hBound x).trans (le_max_right _ _))⟩
  obtain ⟨v,q,hvq,hv,hq,hmix⟩ := exists_local_logarithmic_laplacian μ hQ u d hd _
    (SobolevSpace.minimalSlope_le_lipschitz μ hQ u hLip hu.symm) ha (le_max_left _ _) hval
  have henergy : localGamma μ hQ v v =ᵐ[μ.restrict Ω]
      fun x => localGamma μ hQ u u x / (U x)^2 := by
    filter_upwards [hmix v,hmix u,ae_restrict_of_ae (localGamma_comm μ hQ u v)] with x hvv hvu hcomm
    rw [hvv,hcomm,hvu,div_div,pow_two]
  refine ⟨u,v,q,hu,hvq,?_,?_,?_⟩
  · filter_upwards [hv,ae_restrict_of_ae hu] with x hvx hux
    exact hvx.trans (congrArg Real.log hux.symm)
  · filter_upwards [hq,henergy,ae_restrict_of_ae hu,ae_restrict_of_ae hD,
      ae_restrict_mem hΩ.measurableSet] with x hqx he hux hDx hmem
    have hder := kernelHeat_log_hasDerivAt μ hQ hk f ht x (hpos x hmem).ne'
    have heq : q x+localGamma μ hQ v v x = kernelHeatGeneratorSource μ hQ hk t f x/H x := by
      rw [hqx,he,hDx]
      change d x/U x-localGamma μ hQ u u x/U x^2+localGamma μ hQ u u x/U x^2 = d x/H x
      rw [← hux]
      ring
    exact heq ▸ hder
  · intro w
    filter_upwards [hmix w,ae_restrict_of_ae hu] with x hx hux
    exact hx.trans (by rw [hux])

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
