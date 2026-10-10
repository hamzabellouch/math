import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.RadialCoefficientProfiles
import OAI.Geometry.TamingCompatibility.Functional.RadialParameterJets

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter Function Metric
open scoped ContDiff Topology RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [HasContDiffBump E]

lemma fderiv_scaledCutoff_zero_inner {R : ℝ} (hR : 0 < R) {z : E} (hz : ‖z‖ < R) :
    fderiv ℝ (scaledCutoff R : E → ℝ) z = 0 := by
  have he : (scaledCutoff R : E → ℝ) =ᶠ[𝓝 z] fun _ => 1 := by
    filter_upwards [isOpen_ball.mem_nhds (by simpa using hz : z ∈ ball (0:E) R)] with w hw
    exact scaledCutoff_one hR (by simpa using (le_of_lt (show ‖w‖ < R by simpa using hw)))
  rw [he.fderiv_eq]
  simp

def cutoffLogError (V : E → E) (R : ℝ) (p : ℝ × E) (z : E) : ℝ :=
  logPotential p.1 z * fderiv ℝ (scaledCutoff R) z (V (p.2+z))

def cutoffSqrtError (V : E → E) (R : ℝ) (p : ℝ × E) (z : E) : ℝ :=
  sqrtPotential p.1 z * fderiv ℝ (scaledCutoff R) z (V (p.2+z))

lemma cutoffLogError_smooth (V : E → E) (hV : ContDiff ℝ ∞ V)
    {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ ∞ (fun q : (ℝ × E) × E => cutoffLogError V R q.1 q.2) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hz : q.2 = 0
  · have he : (fun q : (ℝ × E) × E => cutoffLogError V R q.1 q.2) =ᶠ[𝓝 q] fun _ => 0 := by
      have hb : q.2 ∈ ball (0:E) R := by simp [hz,hR]
      filter_upwards [(continuous_snd.tendsto q).eventually (isOpen_ball.mem_nhds hb)] with p hp
      simp [cutoffLogError,fderiv_scaledCutoff_zero_inner hR (by simpa using hp)]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hpos : 0 < q.1.1^2 + ‖q.2‖^2 := by
      have hn := norm_pos_iff.mpr hz; nlinarith [sq_nonneg q.1.1]
    have hl := (log_joint_smooth_at hpos).comp q
      (contDiff_fst.fst.prodMk contDiff_snd).contDiffAt
    have hd : ContDiff ℝ ∞ (fun q : (ℝ × E) × E => fderiv ℝ (scaledCutoff R) q.2) :=
      ((scaledCutoff_smooth R).fderiv_right (m := ∞) (by simp)).comp contDiff_snd
    have hv : ContDiff ℝ ∞ (fun q : (ℝ × E) × E => V (q.1.2+q.2)) :=
      hV.comp (contDiff_fst.snd.add contDiff_snd)
    exact hl.mul (hd.clm_apply hv).contDiffAt

lemma cutoffSqrtError_smooth (V : E → E) (hV : ContDiff ℝ ∞ V)
    {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ ∞ (fun q : (ℝ × E) × E => cutoffSqrtError V R q.1 q.2) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hz : q.2 = 0
  · have he : (fun q : (ℝ × E) × E => cutoffSqrtError V R q.1 q.2) =ᶠ[𝓝 q] fun _ => 0 := by
      have hb : q.2 ∈ ball (0:E) R := by simp [hz,hR]
      filter_upwards [(continuous_snd.tendsto q).eventually (isOpen_ball.mem_nhds hb)] with p hp
      simp [cutoffSqrtError,fderiv_scaledCutoff_zero_inner hR (by simpa using hp)]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hpos : 0 < q.1.1^2 + ‖q.2‖^2 := by
      have hn := norm_pos_iff.mpr hz; nlinarith [sq_nonneg q.1.1]
    have hl := (sqrt_joint_smooth_at hpos).comp q
      (contDiff_fst.fst.prodMk contDiff_snd).contDiffAt
    have hd : ContDiff ℝ ∞ (fun q : (ℝ × E) × E => fderiv ℝ (scaledCutoff R) q.2) :=
      ((scaledCutoff_smooth R).fderiv_right (m := ∞) (by simp)).comp contDiff_snd
    have hv : ContDiff ℝ ∞ (fun q : (ℝ × E) × E => V (q.1.2+q.2)) :=
      hV.comp (contDiff_fst.snd.add contDiff_snd)
    exact hl.mul (hd.clm_apply hv).contDiffAt

lemma cutoffLogError_tsupport (V : E → E) {R : ℝ} (hR : 0 < R) (p : ℝ × E) :
    tsupport (cutoffLogError V R p) ⊆ closedBall (0:E) (2*R) := by
  apply (tsupport_mul_subset_right.trans ?_).trans (scaledCutoff_tsupport hR)
  exact (firstOrderSource_tsupport (fun z => V (p.2+z)) (scaledCutoff R))

lemma cutoffSqrtError_tsupport (V : E → E) {R : ℝ} (hR : 0 < R) (p : ℝ × E) :
    tsupport (cutoffSqrtError V R p) ⊆ closedBall (0:E) (2*R) := by
  apply (tsupport_mul_subset_right.trans ?_).trans (scaledCutoff_tsupport hR)
  exact (firstOrderSource_tsupport (fun z => V (p.2+z)) (scaledCutoff R))

lemma cutoffLogError_derivatives_bounded [ProperSpace E]
    (V : E → E) (hV : ContDiff ℝ ∞ V) {R : ℝ} (hR : 0 < R)
    {K : Set E} (hK : IsCompact K) (S : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0:ℝ) S, ∀ b ∈ K, ∀ z : E,
      ‖iteratedFDeriv ℝ n (cutoffLogError V R (s,b)) z‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := compact_parameter_family_derivatives_bounded (cutoffLogError V R)
    (cutoffLogError_smooth V hV hR) (isCompact_Icc.prod hK) (isCompact_closedBall (0:E) (2*R))
    (fun p _hp => cutoffLogError_tsupport V hR p) n
  exact ⟨C,hC,fun s hs b hb z => h (s,b) ⟨hs,hb⟩ z⟩

lemma cutoffSqrtError_derivatives_bounded [ProperSpace E]
    (V : E → E) (hV : ContDiff ℝ ∞ V) {R : ℝ} (hR : 0 < R)
    {K : Set E} (hK : IsCompact K) (S : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0:ℝ) S, ∀ b ∈ K, ∀ z : E,
      ‖iteratedFDeriv ℝ n (cutoffSqrtError V R (s,b)) z‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := compact_parameter_family_derivatives_bounded (cutoffSqrtError V R)
    (cutoffSqrtError_smooth V hV hR) (isCompact_Icc.prod hK) (isCompact_closedBall (0:E) (2*R))
    (fun p _hp => cutoffSqrtError_tsupport V hR p) n
  exact ⟨C,hC,fun s hs b hb z => h (s,b) ⟨hs,hb⟩ z⟩
end TamingCompatibility.RadialPotential

end

end OAI
