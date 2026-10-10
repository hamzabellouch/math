import OAI.Analysis.CircleDomains.Rigidity.ZeroTraceExtension

namespace OAI

/-! The zero-trace extension preserves the original weak gradient and
Dirichlet energy, and introduces no energy on the excluded set. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem zeroTraceWitness_gradient_on
    {U : Set EuclideanPlane} (hU : IsOpen U) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (hz : ∀ x ∉ U, u x = 0) (hw : DeGiorgi.MemW1pWitness 2 u U) (i : Fin 2) :
    (fun x => (zeroTraceWitness hU hu hs hz hw).weakGrad x i) =ᵐ[volume.restrict U]
      (fun x => hw.weakGrad x i) := by
  let H := zeroTraceWitness hU hu hs hz hw
  let H' := H.restrict hU (subset_univ U)
  exact (H'.isWeakGrad i).ae_eq hU (hw.isWeakGrad i)
    ((H'.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
    ((hw.weakGrad_component_memLp i).locallyIntegrable (by norm_num))

 theorem zeroTraceWitness_component_energy
    {U : Set EuclideanPlane} (hU : IsOpen U) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (hz : ∀ x ∉ U, u x = 0) (hw : DeGiorgi.MemW1pWitness 2 u U) (i : Fin 2) :
    (∫ x, (zeroTraceWitness hU hu hs hz hw).weakGrad x i ^ 2) =
      ∫ x in U, hw.weakGrad x i ^ 2 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U) (fun x hx => by
    rw [zeroTraceWitness_zero hU hu hs hz hw i hx, zero_pow (by norm_num : 2 ≠ 0)])]
  apply integral_congr_ae
  filter_upwards [zeroTraceWitness_gradient_on hU hu hs hz hw i] with x hx
  rw [hx]

 theorem zeroTraceWitness_energy
    {U : Set EuclideanPlane} (hU : IsOpen U) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (hz : ∀ x ∉ U, u x = 0) (hw : DeGiorgi.MemW1pWitness 2 u U) :
    (∫ x, (zeroTraceWitness hU hu hs hz hw).weakGrad x 0 ^ 2 +
      (zeroTraceWitness hU hu hs hz hw).weakGrad x 1 ^ 2) =
      ∫ x in U, hw.weakGrad x 0 ^ 2 + hw.weakGrad x 1 ^ 2 := by
  let H := zeroTraceWitness hU hu hs hz hw
  have hH (i : Fin 2) : Integrable (fun x => H.weakGrad x i ^ 2) := by
    have ht := (H.weakGrad_component_memLp i).integrable_sq
    simpa only [Measure.restrict_univ] using ht
  rw [integral_add (hH 0) (hH 1),
    integral_add (hw.weakGrad_component_memLp 0).integrable_sq
      (hw.weakGrad_component_memLp 1).integrable_sq]
  rw [zeroTraceWitness_component_energy hU hu hs hz hw 0,
    zeroTraceWitness_component_energy hU hu hs hz hw 1]

end CircleDomainRigidity

end

end OAI
