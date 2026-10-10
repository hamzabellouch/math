import OAI.Analysis.CircleDomains.Sobolev.LocalSobolevClassicalPartials
import OAI.Analysis.CircleDomains.Sobolev.LocalComplexWitness

namespace OAI

/-! Classical coordinate partials for the precise continuous representative
of a genuinely local W1,2 function. No global integrability is assumed. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def scalarBallWeakWitness {u : EuclideanPlane → ℝ} (hu : Continuous u)
    {V : EuclideanPlane → EuclideanPlane} (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R))) (R : ℝ) :
    DeGiorgi.MemW1pWitness 2 u (ball 0 R) where
  memLp := continuous_memLp_ball hu R
  weakGrad := V
  weakGrad_component_memLp := hLp R
  isWeakGrad := fun i => weakPartial_restrict_from_univ (hw i) _

lemma locally_sobolev_coordinate_ae_hasDerivAt {u : EuclideanPlane → ℝ}
    (hu : Continuous u) {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V u univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R))) (i : Fin 2) :
    ∀ᵐ y ∂volume, ∀ᵐ t ∂volume,
      HasDerivAt (fun s => u (physicalCoordinateLine i y s))
        (V (physicalCoordinateLine i y t) i) t := by
  have hsub (n : ℕ) : closedBall (0 : EuclideanPlane) n ⊆ ball 0 (n+1) := by
    intro p hp
    exact (mem_closedBall.mp hp).trans_lt (by linarith)
  choose O hO hKO hOsub hder using fun n : ℕ =>
    compact_core_sobolev_coordinate_derivative isOpen_ball (isCompact_closedBall (0 : EuclideanPlane) n)
      (hsub n) hu (scalarBallWeakWitness hu hw hLp (n+1)) i
  have hall : ∀ᵐ y ∂volume, ∀ n : ℕ, ∀ᵐ t ∂volume,
      physicalCoordinateLine i y t ∈ O n →
        HasDerivAt (fun s => u (physicalCoordinateLine i y s))
          (V (physicalCoordinateLine i y t) i) t := by
    apply ae_all_iff.mpr
    intro n
    exact hder n
  filter_upwards [hall] with y hy
  filter_upwards [ae_all_iff.mpr hy] with t ht
  obtain ⟨n, hn⟩ := exists_nat_gt ‖physicalCoordinateLine i y t‖
  apply ht n (hKO n ?_)
  simpa only [mem_closedBall, dist_zero_right] using hn.le

end CircleDomainRigidity

end

end OAI
