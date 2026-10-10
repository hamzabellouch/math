import OAI.Geometry.Relativity.CKS.ConeSupport

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def stereoFactor (x : Point) : ℝ := 4/(1+x 0^2+x 1^2)^2

def stereoMetric (x : Point) : Mat := stereoFactor x • (1 : Mat)

lemma stereoFactor_positive (x : Point) : 0 < stereoFactor x := by
  unfold stereoFactor
  positivity

lemma stereoFactor_smooth : ContDiff ℝ ∞ stereoFactor := by
  apply ContDiff.div contDiff_const
  · fun_prop
  · intro x
    positivity

lemma stereoMetric_smooth : ContDiff ℝ ∞ stereoMetric := stereoFactor_smooth.smul contDiff_const

lemma stereoMetric_det_positive (x : Point) : 0 < determinant (stereoMetric x) := by
  simpa [determinant,stereoMetric] using mul_pos (stereoFactor_positive x) (stereoFactor_positive x)

lemma actualJet_continuous {q : Point → Mat} (hq : ContDiff ℝ 3 q) : Continuous (actualJet q) := by
  rw [continuous_iff_continuousAt]
  intro x
  apply ContinuousAt.prodMk hq.continuous.continuousAt
  apply ContinuousAt.prodMk
  · apply continuousAt_pi.mpr
    intro a
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro k
    have hc : ContDiffAt ℝ 3 (fun y => q y i k) x :=
      contDiffAt_pi.mp (contDiffAt_pi.mp hq.contDiffAt i) k
    exact (contDiffAt_D hc (m := 2) (by norm_num) (basis a)).continuousAt
  · apply continuousAt_pi.mpr
    intro a
    apply continuousAt_pi.mpr
    intro b
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro k
    have hc : ContDiffAt ℝ 3 (fun y => q y i k) x :=
      contDiffAt_pi.mp (contDiffAt_pi.mp hq.contDiffAt i) k
    exact (contDiffAt_D (contDiffAt_D hc (m := 2) (by norm_num) (basis b))
      (m := 1) (by norm_num) (basis a)).continuousAt

def roundReference (x : Point) : CombinedJet := (actualJet stereoMetric x,(1,0,0))

def roundReferenceFamily (c : ℝ) : Set CombinedJet := roundReference '' Metric.closedBall 0 c

lemma roundReference_continuous : Continuous roundReference := by
  exact (actualJet_continuous (stereoMetric_smooth.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))).prodMk continuous_const

lemma roundReferenceFamily_compact (c : ℝ) : IsCompact (roundReferenceFamily c) :=
  (isCompact_closedBall 0 c).image roundReference_continuous

lemma roundReferenceFamily_regular (c : ℝ) : roundReferenceFamily c ⊆ regular := by
  rintro j ⟨x,hx,rfl⟩
  exact ⟨(stereoMetric_det_positive x).ne',by norm_num [roundReference]⟩

theorem round_uniform_operators (c : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ≥0,
      LipschitzOnWith C operators (Metric.cthickening δ (roundReferenceFamily c)) :=
  operators_uniform_lipschitz (roundReferenceFamily_compact c) (roundReferenceFamily_regular c)

end
end CKSAngularGeometry

end

end OAI
