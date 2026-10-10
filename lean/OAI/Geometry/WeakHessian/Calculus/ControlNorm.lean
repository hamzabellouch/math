import Mathlib
import OAI.Geometry.WeakHessian.Measure.TimeMeasure

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction

namespace WeakHessian
variable {X : Type*} [MetricSpace X]

lemma HasControlBound.dist_le_modulus {γ : Curve X} {B : ℝ} (h : HasControlBound γ B)
    (s t : Time) : dist (γ s) (γ t) ≤ Real.sqrt (dist s t)*|B| := by
  have H := h.dist_sq_le s t
  have hd : dist s t = |(s:ℝ)-(t:ℝ)| := rfl
  rw [← hd] at H
  apply (sq_le_sq₀ dist_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt dist_nonneg, sq_abs] using H

lemma isCompact_hasControlBound [CompactSpace X] (B : ℝ) :
    IsCompact {γ : Curve X | HasControlBound γ B} := by
  let e := ContinuousMap.isometryEquivBoundedOfCompact Time X
  let A : Set (Time →ᵇ X) := e.symm ⁻¹' {γ : Curve X | HasControlBound γ B}
  have hcl : IsClosed A := (isClosed_hasControlBound B).preimage e.symm.continuous
  have heq : Equicontinuous ((↑) : A → Time → X) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => Real.sqrt r*|B|)
    · simpa using (Real.continuous_sqrt.tendsto 0).mul_const |B|
    · intro s t γ
      exact γ.2.dist_le_modulus s t
  have hc := BoundedContinuousFunction.arzela_ascoli₁ A hcl heq
  have hc' : IsCompact (e.symm '' A) := hc.image e.symm.continuous
  have hrange : e.symm '' A = {γ : Curve X | HasControlBound γ B} := e.symm.toEquiv.image_preimage _
  rw [hrange] at hc'
  exact hc'

lemma hasControlBound_of_forall_gt {γ : Curve X} {B : ℝ}
    (h : ∀ C : ℝ, B < C → HasControlBound γ C) : HasControlBound γ B := by
  let K : ℕ → Set ControlSpace := fun n => Metric.closedBall 0 (B+1/(n+1:ℝ)) ∩
    ⋂ (s : Time) (t : Time) (_ : s ≤ t),
      {u | dist (γ s) (γ t) ≤ intervalFunctional s t u}
  have hKcl : ∀ n, IsClosed (K n) := fun n => Metric.isClosed_closedBall.inter
    (isClosed_iInter fun s => isClosed_iInter fun t => isClosed_iInter fun _ =>
      isClosed_le continuous_const (intervalFunctional s t).continuous)
  have hKconv : ∀ n, Convex ℝ (K n) := fun n => (convex_closedBall (0:ControlSpace) _).inter
    (convex_iInter fun s => convex_iInter fun t => convex_iInter fun _ =>
      (convex_Ici _).linear_preimage (intervalFunctional s t).toLinearMap)
  have hKanti : Antitone K := by
    intro n k hnk u hu
    refine ⟨?_, hu.2⟩
    apply Metric.closedBall_subset_closedBall _ hu.1
    have heps : 1/(k+1:ℝ) ≤ 1/(n+1:ℝ) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hnk 1
    linarith
  have hKne : ∀ n, (K n).Nonempty := by
    intro n
    obtain ⟨u,hu,hud⟩ := h (B+1/(n+1:ℝ)) (by
      have he : 0 < 1/(n+1:ℝ) := by positivity
      linarith)
    exact ⟨u, by simpa only [Metric.mem_closedBall, dist_zero_right] using hu,
      mem_iInter.mpr fun s => mem_iInter.mpr fun t => mem_iInter.mpr fun hst => hud s t hst⟩
  obtain ⟨u,hu⟩ := WeakHessianFunctional.nonempty_iInter_closed_convex hKne hKcl hKconv hKanti
    (Metric.isBounded_closedBall.subset inter_subset_left)
  refine ⟨u, ?_, fun s t hst =>
    mem_iInter.mp (mem_iInter.mp (mem_iInter.mp (mem_iInter.mp hu 0).2 s) t) hst⟩
  have Hall : ∀ n : ℕ, ‖u‖ ≤ B+1/(n+1:ℝ) := fun n => by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (mem_iInter.mp hu n).1
  apply ge_of_tendsto (by simpa only [add_zero] using
    (tendsto_const_nhds (x := B)).add tendsto_one_div_add_atTop_nhds_zero_nat)
  exact Eventually.of_forall Hall

def controlNorm (γ : Curve X) : ℝ≥0∞ :=
  ⨅ (B : ℝ) (_ : HasControlBound γ B), ENNReal.ofReal B

lemma controlNorm_le {γ : Curve X} {B : ℝ} (h : HasControlBound γ B) :
    controlNorm γ ≤ ENNReal.ofReal B :=
  iInf_le_of_le B (iInf_le _ h)

lemma controlNorm_le_iff {γ : Curve X} {B : ℝ} (hB : 0 ≤ B) :
    controlNorm γ ≤ ENNReal.ofReal B ↔ HasControlBound γ B := by
  refine ⟨fun h => hasControlBound_of_forall_gt fun C hC => ?_, controlNorm_le⟩
  have hlt : controlNorm γ < ENNReal.ofReal C :=
    h.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (hB.trans_lt hC)).mpr hC)
  obtain ⟨D,hD⟩ := iInf_lt_iff.mp hlt
  obtain ⟨hD,hdlt⟩ := iInf_lt_iff.mp hD
  have hDC : D < C := (ENNReal.ofReal_lt_ofReal_iff (hB.trans_lt hC)).mp hdlt
  obtain ⟨u,hu,hud⟩ := hD
  exact ⟨u,hu.trans hDC.le,hud⟩

lemma lowerSemicontinuous_controlNorm : LowerSemicontinuous (controlNorm (X := X)) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro a
  by_cases ha : a = ∞
  · simp [ha]
  · have heq : a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal ha).symm
    rw [heq]
    change IsClosed {γ : Curve X | controlNorm γ ≤ ENNReal.ofReal a.toReal}
    simp_rw [controlNorm_le_iff ENNReal.toReal_nonneg]
    exact isClosed_hasControlBound _

lemma controlNorm_lt_top_iff {γ : Curve X} :
    controlNorm γ < ∞ ↔ ∃ B : ℝ, HasControlBound γ B := by
  refine ⟨fun h => ⟨(controlNorm γ).toReal, ?_⟩, ?_⟩
  · apply (controlNorm_le_iff ENNReal.toReal_nonneg).mp
    rw [ENNReal.ofReal_toReal h.ne]
  · rintro ⟨B,hB⟩
    exact lt_of_le_of_lt (controlNorm_le hB) ENNReal.ofReal_lt_top

lemma controlNorm_finite_isAC2 {γ : Curve X} (h : controlNorm γ < ∞) : IsAC2 γ := by
  obtain ⟨B,hB⟩ := controlNorm_lt_top_iff.mp h
  obtain ⟨a,ha,_⟩ := hB.squareControl
  exact ha.isAC2

end WeakHessian

end
end InlinedFile0

end OAI
