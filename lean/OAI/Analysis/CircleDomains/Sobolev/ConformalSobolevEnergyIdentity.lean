import OAI.Analysis.CircleDomains.Sobolev.SmoothTransportDifferenceEnergy
import OAI.Analysis.CircleDomains.Sobolev.PairedEnergyCauchy
import OAI.Analysis.CircleDomains.Sobolev.SobolevConformalTransport

namespace OAI

/-! Exact Dirichlet energy transport for a continuous compactly supported
Sobolev function. Strong Cauchy control of transported mollifications
retains equality, strengthening the earlier one-sided bound. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem sobolev_conformal_energy_identity
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V) (hU : IsOpen U) (hV : IsOpen V)
    (hinf : OnePoint.infty ∈ U) (hfix : f OnePoint.infty = OnePoint.infty)
    (hf : IsConformalOn f U) {u v : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (H : DeGiorgi.MemW1pWitness 2 u univ)
    (hv : EqOn v (planeInverseTransport fi u) (physicalPlaneDomain V))
    (hL : MemLp v 2 (volume.restrict (physicalPlaneDomain V))) :
    ∃ K : DeGiorgi.MemW1pWitness 2 v (physicalPlaneDomain V),
      (∫ x in physicalPlaneDomain V, K.weakGrad x 0^2+K.weakGrad x 1^2) =
        ∫ x in physicalPlaneDomain U, H.weakGrad x 0^2+H.weakGrad x 1^2 := by
  have huL : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using H.memLp
  let a := planarMollification u
  let b := fun n => planeInverseTransport fi (a n)
  have ha (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (a n) :=
    planarMollification_smooth (huL.locallyIntegrable (by norm_num)) n
  let d := fun (i : Fin 2) n x => fderiv ℝ (a n) x (EuclideanSpace.single i 1)
  let e := fun (i : Fin 2) n x => fderiv ℝ (b n) x (EuclideanSpace.single i 1)
  have hd (i : Fin 2) (n : ℕ) : MemLp (d i n) 2
      (volume.restrict (physicalPlaneDomain U)) :=
    (planarMollification_partial_memLp H hs n i).restrict _
  have ht (n : ℕ) := smooth_plane_energy_transport heq hU hV hinf hfix hf
    (ha n).contDiffOn (fun i => hd i n)
  have he (i : Fin 2) (n : ℕ) : MemLp (e i n) 2
      (volume.restrict (physicalPlaneDomain V)) := (ht n).2.1 i
  have hdc (i : Fin 2) : CauchySeq (fun n => (hd i n).toLp (d i n)) := by
    have hg : MemLp (fun x => H.weakGrad x i) 2 (volume.restrict (physicalPlaneDomain U)) := by
      simpa only [Measure.restrict_univ] using (H.weakGrad_component_memLp i).restrict (physicalPlaneDomain U)
    have hl : Tendsto (fun n => eLpNorm (fun x => d i n x-H.weakGrad x i) 2
        (volume.restrict (physicalPlaneDomain U))) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (planarMollification_tendsto_gradient_L2 H i)
        (fun _ => bot_le) (fun _ => eLpNorm_mono_measure _ Measure.restrict_le_self)
    exact ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (d i) (hd i)
      (fun x => H.weakGrad x i) hg).mpr hl).cauchySeq
  have hec := cauchy_partials_of_paired_energy_isometry d e hd he hdc (fun m n =>
    smooth_transport_difference_energy heq hU hV hinf hfix hf (ha m).contDiffOn
      (ha n).contDiffOn (fun i => hd i m) (fun i => hd i n))
  obtain ⟨C,hC⟩ := hu.bounded_above_of_compact_support hs
  have hunit (x : EuclideanPlane) : u x ∈ Icc (-C) C :=
    abs_le.mp (by simpa only [Real.norm_eq_abs] using hC x)
  have hb (n : ℕ) (x : EuclideanPlane) (_hx : x ∈ physicalPlaneDomain V) : ‖b n x‖ ≤ C := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr (planarMollification_mem_Icc hu.aestronglyMeasurable hunit n _)
  have hp (x : EuclideanPlane) (hx : x ∈ physicalPlaneDomain V) :
      Tendsto (fun n => b n x) atTop (𝓝 (v x)) := by
    rw [hv hx]
    exact planarMollification_tendsto_of_continuous hu _
  apply energy_limit_of_strong_cauchy_partials (isOpen_physicalPlaneDomain hV) hL
    (fun n => (ht n).1.continuousOn) hb hp e he
    (fun i n => weakPartial_of_smooth_on (isOpen_physicalPlaneDomain hV) (ht n).1 i) hec
  convert planarMollification_energy_tendsto H hs (physicalPlaneDomain U) using 1
  funext n
  exact (ht n).2.2

end CircleDomainRigidity

end

end OAI
