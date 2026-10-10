import OAI.Geometry.Relativity.CKS.CKSMetricInput
import OAI.Geometry.Relativity.CKS.CollarRoundReferences

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma matrixScalarJets_norm_le_three (q : Point → Mat) (x : Point) :
    ‖matrixScalarJets q x‖ ≤ ‖matrixThreeJets q x‖ := by
  apply (Matrix.norm_le_iff (norm_nonneg _)).mpr
  intro i k
  exact (norm_fst_le (matrixThreeJets q x i k)).trans
    (Matrix.norm_entry_le_entrywise_sup_norm (matrixThreeJets q x))

lemma normalizedShift_diff {r : ℝ} {q : Point → Mat} {mixed : Point → Point} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) (hb : ContDiffAt ℝ 3 mixed x) (h0 : determinant (q x) ≠ 0) :
    ContDiffAt ℝ 3 (normalizedShift r q mixed) x := by
  apply contDiffAt_pi.mpr
  intro a
  change ContDiffAt ℝ 3 (fun y => (1/r)*∑ b, inverse (q y) a b*mixed y b) x
  apply ContDiffAt.const_smul (1/r)
  apply ContDiffAt.sum
  intro b hb'
  apply ContDiffAt.mul _ (contDiffAt_pi.mp hb b)
  unfold inverse
  apply ContDiffAt.div
  · fin_cases a <;> fin_cases b <;> dsimp <;>
      first | exact component_three hq _ _ | exact (component_three hq _ _).neg
  · exact (determinant_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)).contDiffAt.comp x hq
  · exact h0

lemma convex_metric_posDef {q σ : Mat} (hq : q.PosDef) (hσ : σ.PosDef)
    {e : ℝ} (he : 0 ≤ e) (he1 : e ≤ 1) : ((1-e) • q+e • σ).PosDef := by
  rcases eq_or_lt_of_le he1 with h | h
  · subst e
    simpa using hσ
  · exact (hq.smul (sub_pos.mpr h)).add_posSemidef (hσ.posSemidef.smul he)

theorem cks_expansion_input_bound (c : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (r A B T : ℝ) (m E dE : Point → Mat) (mixed : Point → Point) (x : Point),
      1 ≤ r → 0 ≤ A → 0 ≤ B → 0 ≤ T → x ∈ Metric.closedBall 0 c →
      ContDiffAt ℝ 3 m x → ContDiffAt ℝ 3 E x → ContDiffAt ℝ 2 dE x →
      ContDiffAt ℝ 3 mixed x →
      ‖matrixThreeJets m x‖ ≤ B → ‖matrixThreeJets E x‖ ≤ A/r^2 →
      ‖matrixScalarJets dE x‖ ≤ A/r^3 →
      ‖fun a => actualThreeJet (fun y => mixed y a) x‖ ≤ T/r^3 →
      max T (A+B)/r^3 ≤ δ →
      ((1/r^2) • cksLeaf r stereoMetric m E x).PosDef →
      let q := fun y => (1/r^2) • cksLeaf r stereoMetric m E y
      ‖actualExpansionInput q (cksRadialField r m E dE) (normalizedShift r q mixed) x-
          roundExpansionReference x‖ ≤ (3*A+3*B+C*T)/r^3 := by
  obtain ⟨δ,hδ,C,hC,hshift⟩ := normalized_shift_bound
    (roundShiftFamily_compact c) (roundShiftFamily_regular c)
  refine ⟨δ,hδ,C,hC,?_⟩
  intro r A B T m E dE mixed x hr hA hB hT hx hm hE hdE hb hmB hEB hdEB hbB hsmall hpos
  let q : Point → Mat := fun y => (1/r^2) • cksLeaf r stereoMetric m E y
  have hr0 : 0 < r := by linarith
  have hσ : ContDiffAt ℝ 3 stereoMetric x := stereoMetric_smooth.contDiffAt.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hq : ContDiffAt ℝ 3 q x := by
    dsimp [q,cksLeaf]
    exact (((hσ.const_smul (r^2)).add (hm.const_smul (1/r))).add hE).const_smul (1/r^2)
  have hqB : ‖matrixThreeJets q x-matrixThreeJets stereoMetric x‖ ≤ (A+B)/r^3 :=
    cks_normalized_three_bound hr hA hB hσ hm hE hmB hEB
  have h0 : determinant (q x) ≠ 0 := by
    rw [determinant_eq]
    exact hpos.det_pos.ne'
  have hsB : ‖fun a => actualThreeJet (fun y => normalizedShift r q mixed y a) x‖ ≤ C*T/r^4 := by
    rw [normalizedShift_realized r hq hb h0]
    exact hshift (matrixThreeJets q x) (matrixThreeJets stereoMetric x)
      (fun a => actualThreeJet (fun y => mixed y a) x) r T (A+B)
      ⟨x,hx,rfl⟩ hr0 hT (by positivity) hqB hbB hsmall
  have hQB : ‖matrixScalarJets (cksRadialField r m E dE) x‖ ≤ (3*A+3*B)/r^3 :=
    cks_radial_jet_bound hr hA hB (hm.of_le (by norm_num)) (hE.of_le (by norm_num)) hdE
      ((matrixScalarJets_norm_le_three m x).trans hmB)
      ((matrixScalarJets_norm_le_three E x).trans hEB) hdEB
  apply actualExpansionInput_norm (by positivity)
  · exact hqB.trans (div_le_div_of_nonneg_right (by nlinarith) (by positivity))
  · exact hQB.trans (div_le_div_of_nonneg_right (by nlinarith) (by positivity))
  · apply hsB.trans
    calc
      C*T/r^4 = (C*T/r^3)*(1/r) := by field_simp
      _ ≤ C*T/r^3 := mul_le_of_le_one_right (by positivity) ((div_le_one hr0).mpr hr)
      _ ≤ (3*A+3*B+C*T)/r^3 := div_le_div_of_nonneg_right (by nlinarith) (by positivity)

end
end CKSAngularGeometry

end

end OAI
