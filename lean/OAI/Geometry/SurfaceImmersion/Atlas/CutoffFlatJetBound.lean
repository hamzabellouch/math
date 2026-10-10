import OAI.Geometry.SurfaceImmersion.Atlas.ShrinkingJetCutoff
import OAI.Geometry.SurfaceImmersion.Correction.WeightedPolynomialBounds

namespace OAI

/-! A shrinking cutoff applied to a flat remainder has a second-order
bound independent of the cutoff radius. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

theorem cutoff_flat_jet_bound : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (R : Base → ProjectionTarget 3), ContDiff ℝ ∞ R → R 0 = 0 →
      fderiv ℝ R 0 = 0 → ∀ r M : ℝ, 0 < r → r ≤ 1 → 0 ≤ M →
      (∀ x ∈ closedBall (0 : Base) r, ‖fderiv ℝ (fderiv ℝ R) x‖ ≤ M) →
      ∀ j ≤ 2, ∀ x : Base,
        ‖iteratedFDeriv ℝ j (fun y => shrinkingJetCutoff r y • R y) x‖ ≤ C*M := by
  obtain ⟨C,hC,hcut⟩ := shrinkingJetCutoff_weighted_bound
  refine ⟨4*C,by positivity,?_⟩
  intro R hR h0 hD0 r M hr hr1 hM hb j hj x
  let Q : Base → ProjectionTarget 3 := fun y => shrinkingJetCutoff r y • R y
  have hQ : ContDiff ℝ ∞ Q := (shrinkingJetCutoff_smooth r).smul hR
  have hsupp : tsupport Q ⊆ closedBall (0 : Base) (r/2) :=
    (tsupport_smul_subset_left _ _).trans (shrinkingJetCutoff_tsupport hr)
  by_cases hx : x ∈ ball (0 : Base) r
  · have hRbound := flat_remainder_weighted_bound hR h0 hD0 hr hM hb
    have hprod := (hcut r hr).smul_real isOpen_ball.uniqueDiffOn hr.le hC
      (mul_nonneg hM (sq_nonneg r)) (shrinkingJetCutoff_smooth r).contDiffOn
      hR.contDiffOn hRbound
    have h := hprod j hj x hx
    rw [iteratedFDerivWithin_of_isOpen j isOpen_ball hx] at h
    have hpow : r^2 ≤ r^j := pow_le_pow_of_le_one hr.le hr1 hj
    apply (mul_le_mul_iff_right₀ (pow_pos hr j)).mp
    calc
      _ ≤ (2:ℝ)^2*C*(M*r^2) := h
      _ = (4*C*M)*r^2 := by ring
      _ ≤ (4*C*M)*r^j := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring
  · have hnot : x ∉ tsupport Q := by
      intro hm
      have hsmall := hsupp hm
      apply hx
      rw [mem_ball,dist_zero_right]
      have hnorm : ‖x‖ ≤ r/2 := by simpa only [mem_closedBall,dist_zero_right] using hsmall
      linarith
    have he := ((notMem_tsupport_iff_eventuallyEq.mp hnot).iteratedFDeriv ℝ j).eq_of_nhds
    change ‖iteratedFDeriv ℝ j Q x‖ ≤ _
    rw [he]
    simpa only [iteratedFDeriv_zero,Pi.zero_apply,norm_zero] using mul_nonneg (by positivity : 0 ≤ 4*C) hM

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
