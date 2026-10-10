import OAI.Analysis.CircleDomains.Sobolev.CompactSobolevJacobian
import OAI.Analysis.CircleDomains.Sobolev.LocalSobolevSmoothing

namespace OAI

/-! Compact Sobolev replacements agreeing outside a closed region have
the same Jacobian integral over that region. This is the interior
replacement step in the conductivity area computation. -/
open Set Filter Function MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem weakGradient_eq_on_open {u v : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u univ) (hv : DeGiorgi.MemW1pWitness 2 v univ)
    {U : Set EuclideanPlane} (hU : IsOpen U) (heq : EqOn u v U) (i : Fin 2) :
    (fun x => hu.weakGrad x i) =ᵐ[volume.restrict U] fun x => hv.weakGrad x i := by
  let huU := hu.restrict hU (subset_univ U)
  let hvU := hv.restrict hU (subset_univ U)
  have hh := weakPartial_congrOn hU (huU.isWeakGrad i) heq
  exact hh.ae_eq hU (hvU.isWeakGrad i)
    ((huU.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
    ((hvU.weakGrad_component_memLp i).locallyIntegrable (by norm_num))

 theorem sobolev_jacobian_integral_locality {u v a b : EuclideanPlane → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u univ) (hv : DeGiorgi.MemW1pWitness 2 v univ)
    (ha : DeGiorgi.MemW1pWitness 2 a univ) (hb : DeGiorgi.MemW1pWitness 2 b univ)
    (hsv : HasCompactSupport v) (hsb : HasCompactSupport b)
    {K : Set EuclideanPlane} (hK : IsClosed K) (hua : EqOn u a Kᶜ) (hvb : EqOn v b Kᶜ) :
    (∫ x in K, hu.weakGrad x 0 * hv.weakGrad x 1 - hu.weakGrad x 1 * hv.weakGrad x 0) =
    ∫ x in K, ha.weakGrad x 0 * hb.weakGrad x 1 - ha.weakGrad x 1 * hb.weakGrad x 0 := by
  have h0 := integral_compact_sobolev_jacobian_zero hu hv hsv
  have h1 := integral_compact_sobolev_jacobian_zero ha hb hsb
  have huG (i : Fin 2) : MemLp (fun x => hu.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using hu.weakGrad_component_memLp i
  have hvG (i : Fin 2) : MemLp (fun x => hv.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using hv.weakGrad_component_memLp i
  have haG (i : Fin 2) : MemLp (fun x => ha.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using ha.weakGrad_component_memLp i
  have hbG (i : Fin 2) : MemLp (fun x => hb.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using hb.weakGrad_component_memLp i
  have hI : Integrable (fun x => hu.weakGrad x 0 * hv.weakGrad x 1 - hu.weakGrad x 1 * hv.weakGrad x 0) :=
    ((huG 0).integrable_mul (hvG 1)).sub ((huG 1).integrable_mul (hvG 0))
  have hJ : Integrable (fun x => ha.weakGrad x 0 * hb.weakGrad x 1 - ha.weakGrad x 1 * hb.weakGrad x 0) :=
    ((haG 0).integrable_mul (hbG 1)).sub ((haG 1).integrable_mul (hbG 0))
  have hcomp : (∫ x in Kᶜ, hu.weakGrad x 0 * hv.weakGrad x 1 - hu.weakGrad x 1 * hv.weakGrad x 0) =
      ∫ x in Kᶜ, ha.weakGrad x 0 * hb.weakGrad x 1 - ha.weakGrad x 1 * hb.weakGrad x 0 := by
    apply integral_congr_ae
    filter_upwards [weakGradient_eq_on_open hu ha hK.isOpen_compl hua 0,
      weakGradient_eq_on_open hu ha hK.isOpen_compl hua 1,
      weakGradient_eq_on_open hv hb hK.isOpen_compl hvb 0,
      weakGradient_eq_on_open hv hb hK.isOpen_compl hvb 1] with x hu0 hu1 hv0 hv1
    rw [hu0, hu1, hv0, hv1]
  have hsum0 := integral_add_compl hK.measurableSet hI
  have hsum1 := integral_add_compl hK.measurableSet hJ
  rw [h0] at hsum0
  rw [h1] at hsum1
  linarith

end CircleDomainRigidity

end

end OAI
