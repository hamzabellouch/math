import OAI.Geometry.RCD.Sobolev.SobolevPointedTestRecovery
import OAI.Analysis.RCDHeat.HopfTransport

namespace OAI

/-! # Compact Hopf--Lax regularizations in the original Dirichlet space -/

open Set Metric Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem compact_hopf_dirichlet (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (hQ : QuadraticCheegerEnergy μ) (hgeo : IsGeodesicSpace X)
    {p : X} {r b S t : ℝ} (hr : 0<r) (ht : 0<t) {M : ℝ≥0}
    (hroom : b+2*t*(M:ℝ)<S) {F : X → ℝ}
    (hF : LipschitzWith ⟨(M:ℝ)/r,div_nonneg M.coe_nonneg hr.le⟩ F)
    (hs : tsupport F⊆closedBall p (b*r)) :
    ∃ w : SobolevSpace.dirichlet μ hQ (ball p (S*r)),
      (SobolevSpace.toLp μ hQ w.val =ᵐ[μ] hopfLax F (t*r^2)) ∧
      ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ w.val x≤
        (localSlope (hopfLax F (t*r^2)) x).toReal := by
  have hT : 0<t*r^2 := mul_pos ht (sq_pos_of_pos hr)
  have hFL := hopfLax_lipschitz hF hgeo hT
  have hzero (x : X) (hx : b*r<dist p x) : F x=0 := by
    by_contra hne
    have hh := hs (subset_tsupport F hne)
    rw [mem_closedBall,dist_comm] at hh
    linarith
  have hqs : tsupport (hopfLax F (t*r^2))⊆closedBall p ((b+2*t*(M:ℝ))*r) := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hnot
    have hd : (b+2*t*(M:ℝ))*r<dist p x := by
      simpa only [mem_closedBall,dist_comm,not_le] using hnot
    apply hx
    apply hopfLax_zero_outside hF p (b*r) hzero hT
    change b*r+2*(t*r^2)*((M:ℝ)/r)<dist p x
    have heq : b*r+2*(t*r^2)*((M:ℝ)/r)=(b+2*t*(M:ℝ))*r := by
      field_simp
    rwa [heq]
  have hqc : HasCompactSupport (hopfLax F (t*r^2)) :=
    (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) hqs
  let w0 := SobolevSpace.ofLipschitzCompact μ hQ hFL hqc
  have hrep : SobolevSpace.toLp μ hQ w0 =ᵐ[μ] hopfLax F (t*r^2) :=
    SobolevSpace.ofLipschitzCompact_coe μ hQ hFL hqc
  have hdir : w0∈SobolevSpace.dirichlet μ hQ (ball p (S*r)) :=
    (SobolevSpace.dirichletCore μ hQ (ball p (S*r))).le_topologicalClosure
      ⟨hopfLax F (t*r^2),_,hFL,hqc,hqs.trans (closedBall_subset_ball
        (mul_lt_mul_of_pos_right hroom hr)),hrep⟩
  exact ⟨⟨w0,hdir⟩,hrep,SobolevSpace.ofLipschitzCompact_minimalSlope_le_slope μ hQ hFL hqc⟩

end RegularPointCoordinates

end

end OAI
