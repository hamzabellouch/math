import OAI.Geometry.RCD.Heat.BoundedLocalLogarithm
import OAI.Geometry.RCD.Heat.BoundedHeatMixedGramBounds
import OAI.Geometry.RCD.Sobolev.WeakLaplacianDomain

namespace OAI

/-! # Regular bounded extensions of a positive heat logarithm -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  [(hausdorff n X).Regular] [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2≤n) (p : X)

include hn p in
theorem bounded_heat_log_regular (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A) {t : ℝ} (ht : 0<t)
    {Ω : Set X} (hΩ : IsCompact Ω)
    (hp : ∀ x∈Ω, 0<kernelHeat (hausdorff n X) hX.quadratic
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) t f x) :
    ∃ (u : SobolevSpace (hausdorff n X) hX.quadratic) (q : Lp ℝ 2 (hausdorff n X))
      (U : X → ℝ) (L B : ℝ≥0),
      IsWeakLaplacian (hausdorff n X) hX.quadratic u q ∧ LipschitzWith L U ∧
      (∀ x, |U x|≤B) ∧ (SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] U) ∧
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic u
        =ᵐ[(hausdorff n X).restrict Ω] fun x => Real.log
          (kernelHeat (hausdorff n X) hX.quadratic
            (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) t f x)) := by
  let m := hausdorff n X
  let Q := hX.quadratic
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  let u := heatSobolev m Q t ht f
  have hrep : SobolevSpace.toLp m Q u =ᵐ[m] kernelHeat m Q hk t f := by
    simpa only [u,heatSobolev_toLp] using (kernelHeat_represents_L2 m Q hk ht f).symm
  obtain ⟨hLip,hBound⟩ := hX.kernelHeat_bounded_regularity hn p hk f A hf t ht
  obtain ⟨a,b,ha,hab,hval⟩ := hX.bounded_heat_positive_range hn p f A hf ht hΩ hp
  have hval' : ∀ᵐ x ∂m.restrict Ω, kernelHeat m Q hk t f x∈Icc a b := by
    filter_upwards [hval,ae_restrict_of_ae hrep] with x hx he
    rwa [← he]
  have hd : IsWeakLaplacian m Q u (-heatGeneratorAt m Q t f) := by
    simpa only [u,heatGeneratorAt_of_pos m Q t ht] using heatSobolev_weak_laplacian m Q t ht f
  exact bounded_local_logarithm m Q u (-heatGeneratorAt m Q t f) hd
    (kernelHeat m Q hk t f) hLip hBound hrep ha hab hval'

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
