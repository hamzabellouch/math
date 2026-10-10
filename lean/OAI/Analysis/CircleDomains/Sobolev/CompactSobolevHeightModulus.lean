import OAI.Analysis.CircleDomains.Sobolev.HeightSmoothApproximation
import OAI.Analysis.CircleDomains.Sobolev.ComplexScalarEnergy
import OAI.Analysis.CircleDomains.Sobolev.UniformLocalMollification

namespace OAI

/-! The logarithmic coordinate estimate for an actual compact Sobolev
representative. All approximations are constructed by positive convolution. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem compact_sobolev_height_log_bound (φ : ℂ ≃ₜ ℂ) (c : ℂ)
    {u : EuclideanPlane → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u univ)
    (hc : Continuous u) (hs : HasCompactSupport u)
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (heq : ∀ z ∈ closedBall c R, u (complexPlaneCoordinates.symm z) = (φ z).im)
    {x y : ℂ} (hx : x ∈ closedBall c r) (hy : y ∈ closedBall c r) :
    |(φ x).im-(φ y).im|^2 * Real.log (R/r) ≤
      16*Real.pi*(∫ p in complexPlaneCoordinates ⁻¹'
        {z : ℂ | r < dist z c ∧ dist z c < R}, hu.weakGrad p 0^2+hu.weakGrad p 1^2) := by
  let f : ℕ → ℂ → ℝ := fun n => planarMollification u n ∘ complexPlaneCoordinates.symm
  have hL : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using hu.memLp
  have hf (n : ℕ) : ContDiff ℝ 1 (f n) :=
    ((planarMollification_smooth (hL.locallyIntegrable (by norm_num)) n).comp
      complexPlaneCoordinates.symm.contDiff).of_le (by simp)
  apply homeomorphic_height_log_bound_of_smooth_approximation φ c f hf hr hrR ?_
    (complex_mollification_energy_tendsto hu hs _) hx hy
  intro ε hε
  have hK := (isCompact_closedBall c R).image complexPlaneCoordinates.symm.continuous
  have ht := planarMollification_uniform_on_compact hL.aestronglyMeasurable hK
    isOpen_univ (subset_univ _) hc.continuousOn hε
  filter_upwards [ht] with n hn z hz
  have hh := hn (complexPlaneCoordinates.symm z) ⟨z, hz, rfl⟩
  dsimp only [f, comp_apply]
  rw [← heq z hz, abs_sub_comm]
  exact hh.le

end CircleDomainRigidity

end

end OAI
