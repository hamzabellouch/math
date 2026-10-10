import OAI.Analysis.CircleDomains.Sobolev.PrincipalSmoothLimit
import OAI.Analysis.CircleDomains.Sobolev.SmoothScalarWeakLimit
import OAI.Analysis.CircleDomains.Sobolev.SmoothPhysicalPullbackBounds
import OAI.Analysis.CircleDomains.Sobolev.MollificationMovingPoint
import OAI.Analysis.CircleDomains.Sobolev.MollificationEnergy
import OAI.Analysis.CircleDomains.Topology.CompactMapContainment

namespace OAI

/-! The retained actual smooth principal maps transport the positive
mollifications of a continuous compact Sobolev scalar to an actual weak
Sobolev limit on the image plane. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami CannonPlane

variable {g : PlaneL2} {k R : ℝ} {S : PrincipalSmoothApproximation g k R}

def principalScalarApproximation (L : PrincipalMapLimit S)
    (u : EuclideanPlane → ℝ) (n : ℕ) : EuclideanPlane → ℝ :=
  planarMollification u n ∘ physicalHomeomorph (S.map (L.index n)).symm

lemma PrincipalMapLimit.inverse_physical_tendsto (L : PrincipalMapLimit S)
    (x : EuclideanPlane) :
    Tendsto (fun n => physicalHomeomorph (S.map (L.index n)).symm x) atTop
      (𝓝 (physicalHomeomorph L.map.symm x)) := by
  have h := (continuous_eval_const (complexPlaneCoordinates x)).tendsto
    (homeomorphMap L.map.symm) |>.comp L.inverse
  exact complexPlaneCoordinates.symm.continuous.continuousAt.tendsto.comp h

lemma PrincipalMapLimit.scalar_approximation_smooth (L : PrincipalMapLimit S)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (principalScalarApproximation L u n) :=
  (planarMollification_smooth hu.locallyIntegrable n).comp
    (physicalHomeomorph_contDiff _ (S.inverse_smooth _))

lemma PrincipalMapLimit.scalar_approximation_compact (L : PrincipalMapLimit S)
    {u : EuclideanPlane → ℝ} (hs : HasCompactSupport u) (n : ℕ) :
    HasCompactSupport (principalScalarApproximation L u n) :=
  (planarMollification_hasCompactSupport hs n).comp_homeomorph _

lemma PrincipalMapLimit.scalar_approximation_tendsto (L : PrincipalMapLimit S)
    {u : EuclideanPlane → ℝ} (hu : Continuous u) (x : EuclideanPlane) :
    Tendsto (fun n => principalScalarApproximation L u n x) atTop
      (𝓝 ((u ∘ physicalHomeomorph L.map.symm) x)) :=
  planarMollification_tendsto_moving hu (L.inverse_physical_tendsto x)

lemma PrincipalMapLimit.scalar_weak_limit (L : PrincipalMapLimit S)
    (hk : 0 ≤ k) (hk1 : k < 1) {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) :
    Nonempty (ScalarSmoothWeakLimit (principalScalarApproximation L u)
      (u ∘ physicalHomeomorph L.map.symm)) := by
  let K := (1+k)/(1-k)
  have hK : 0 ≤ K := div_nonneg (by linarith) (by linarith)
  have hdist (n : ℕ) := (smooth_beltrami_two_sided_distortion (S.map (L.index n))
    (S.smooth _) (S.inverse_smooth _) (S.coefficient _) hk hk1
    (S.coefficient_bound _) (S.equation _)).2
  have he := planarMollification_energy_tendsto W hs univ
  simp only [Measure.restrict_univ] at he
  obtain ⟨B, hB⟩ := he.bddAbove_range
  obtain ⟨C, hC⟩ := hu.bounded_above_of_compact_support hs
  have hb (n : ℕ) (x : EuclideanPlane) : ‖principalScalarApproximation L u n x‖ ≤ C := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr (planarMollification_mem_Icc hu.aestronglyMeasurable
      (fun y => abs_le.mp (by simpa only [Real.norm_eq_abs] using hC y)) n _)
  apply exists_scalarSmoothWeakLimit
    ((hu.comp (physicalHomeomorph L.map.symm).continuous).memLp_of_hasCompactSupport
      (hs.comp_homeomorph _)) _ (L.scalar_approximation_smooth hu)
    (fun n i => physicalSmoothPartial_memLp (L.scalar_approximation_smooth hu n)
      (L.scalar_approximation_compact hs n) i) hb (L.scalar_approximation_tendsto hu)
  intro n
  apply (physicalSmoothPullback_energy_global (S.map (L.index n)).symm
    (S.inverse_smooth _) (planarMollification_smooth hu.locallyIntegrable n)
    (planarMollification_hasCompactSupport hs n) hK (hdist n)).trans
  exact mul_le_mul_of_nonneg_left (hB (mem_range_self n)) hK

end CircleDomainRigidity

end

end OAI
