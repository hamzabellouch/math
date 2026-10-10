import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixCodegreeDriftTerm
import OAI.Combinatorics.TriangleRemoval.Process.ExtendedLinkMulVec
import OAI.Combinatorics.TriangleRemoval.Stability.EdgeStabilityRate

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical Matrix

namespace SharpTerminalLeave

noncomputable def completeEdgePair {n : ℕ} (e : CompleteEdge n) :
    {uv : Fin n × Fin n // uv.1 ≠ uv.2 ∧ e.val = {uv.1,uv.2}} := by
  have h : ∃ uv : Fin n × Fin n, uv.1 ≠ uv.2 ∧ e.val = {uv.1,uv.2} := by
    obtain ⟨u,v,huv,he⟩ := Finset.card_eq_two.mp (mem_completeGraph.mp e.property)
    exact ⟨(u,v),huv,he⟩
  exact ⟨h.choose,h.choose_spec⟩

noncomputable def centeredEdgeVector {n : ℕ} (G : Graph n) (s : ℝ) (e : CompleteEdge n) : ℝ :=
  (currentCodegree G (completeEdgePair e).val.1 (completeEdgePair e).val.2 : ℝ)/s-1

lemma centeredEdgeVector_restrict {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (s : ℝ) :
    graphRestrict G hG (centeredEdgeVector G s) = fun e : G => (triangleDegree G e.val : ℝ)/s-1 := by
  funext e
  let uv := completeEdgePair (graphEdgeEmbed G hG e)
  have he : e.val = {uv.val.1,uv.val.2} := uv.property.2
  change (currentCodegree G uv.val.1 uv.val.2 : ℝ)/s-1 = _
  rw [he,triangleDegree_eq_codegree hG (he ▸ e.property)]

lemma graphMatrixLift_apply {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (M : Matrix G G ℝ) (z : CompleteEdge n → ℝ) (e : CompleteEdge n) (he : e.val ∈ G) :
    graphMatrixLift G hG M z e = (M *ᵥ graphRestrict G hG z) ⟨e.val,he⟩ := by
  change (if he : e.val ∈ G then _ else 0) = _
  rw [dite_eq_left he]
  rfl

lemma graph_centered_normalized_operator {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (s : ℝ) (e : CompleteEdge n) (he : e.val ∈ G) :
    graphMatrixLift G hG (s⁻¹ • globalLinkAdjacency G hG) (centeredEdgeVector G s) e =
      centeredCodegreeNeighborSum G (completeEdgePair e).val.1 (completeEdgePair e).val.2 s/s^2 := by
  by_cases hs : s = 0
  · subst s; simp [graphMatrixLift]
  let uv := completeEdgePair e
  have heq : e.val = {uv.val.1,uv.val.2} := uv.property.2
  rw [graphMatrixLift_apply _ _ _ _ _ he,centeredEdgeVector_restrict,Matrix.smul_mulVec]
  simp only [Pi.smul_apply,smul_eq_mul]
  have hp : {uv.val.1,uv.val.2} ∈ G := heq ▸ he
  have hei : (⟨e.val,he⟩ : G) = ⟨{uv.val.1,uv.val.2},hp⟩ := Subtype.ext heq
  rw [hei,global_link_codegree_action G hG _ _ hp s hs]
  dsimp only [uv]
  ring

lemma graph_star_residual_sum {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (s : ℝ) (z : CompleteEdge n → ℝ) (e : CompleteEdge n) (he : e.val ∈ G) :
    movingStarLift (fun e : CompleteEdge n => e.val)
      (movingStarMean (fun e : CompleteEdge n => e.val) (graphActive G) z) e+
      graphMatrixLift G hG (s⁻¹ • globalLinkAdjacency G hG-globalStarAverage G) z e =
      graphMatrixLift G hG (s⁻¹ • globalLinkAdjacency G hG) z e := by
  rw [graph_movingStarLift G hG z e ((mem_graphActive _ _).mpr he)]
  simp only [graphMatrixLift_apply G hG _ _ _ he,Matrix.sub_mulVec,Pi.sub_apply]
  ring

lemma centered_edge_operator_drift {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (s t : ℝ) (hs : s ≠ 0) (e : CompleteEdge n) (he : e.val ∈ G) :
    pmfMean (step G) (fun H => (currentCodegree H (completeEdgePair e).val.1 (completeEdgePair e).val.2 : ℝ)/t)-
      (centeredEdgeVector G s e+1) =
      -edgeStabilityRate s t (triangles G).card*
        (movingStarLift (fun e : CompleteEdge n => e.val)
          (movingStarMean (fun e : CompleteEdge n => e.val) (graphActive G) (centeredEdgeVector G s)) e+
          graphMatrixLift G hG (s⁻¹ • globalLinkAdjacency G hG-globalStarAverage G) (centeredEdgeVector G s) e)+
      edgeStabilityScalar s t (triangles G).card 1*(centeredEdgeVector G s e+1) := by
  rw [graph_star_residual_sum G hG s _ e he,graph_centered_normalized_operator G hG s e he]
  let uv := completeEdgePair e
  have huv := uv.property.1
  have hep : {uv.val.1,uv.val.2} ∈ G := uv.property.2 ▸ he
  dsimp only [centeredEdgeVector]
  simp only [sub_add_cancel]
  rw [normalized_codegree_centered_drift hG _ _ huv s t,ite_eq_left hep]
  unfold edgeStabilityScalar edgeStabilityRate
  field_simp [hs]
  ring

lemma history_valid_all {n T : ℕ} (ω : History (Graph n) T)
    (hω : ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) T T).support) (i : ℕ) :
    ω (historyIndex T i) ⊆ completeGraph n := by
  have hi : historyIndex T i = historyIndex T (min i T) := by simp [historyIndex]
  rw [hi]
  exact complete_history_valid ω hω _ (Nat.min_le_right _ _)

noncomputable def prefixCenteredEdge {n : ℕ} (ω : History (Graph n) (prefixTime n))
    (i : ℕ) : CompleteEdge n → ℝ :=
  centeredEdgeVector (ω (historyIndex (prefixTime n) i)) (earlyTemplateScale 1 2 n i)

noncomputable def prefixEdgeRate {n : ℕ} (ω : History (Graph n) (prefixTime n)) (i : ℕ) : ℝ :=
  edgeStabilityRate (earlyTemplateScale 1 2 n i) (earlyTemplateScale 1 2 n (i+1))
    (triangles (ω (historyIndex (prefixTime n) i))).card

noncomputable def prefixEdgeScalar {n : ℕ} (ω : History (Graph n) (prefixTime n)) (i : ℕ) : ℝ :=
  edgeStabilityScalar (earlyTemplateScale 1 2 n i) (earlyTemplateScale 1 2 n (i+1))
    (triangles (ω (historyIndex (prefixTime n) i))).card 1

noncomputable def prefixEdgeResidual {n : ℕ} (ω : History (Graph n) (prefixTime n))
    (hω : ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support)
    (i : ℕ) : Module.End ℝ (CompleteEdge n → ℝ) :=
  graphMatrixLift _ (history_valid_all ω hω i)
    ((earlyTemplateScale 1 2 n i)⁻¹ • globalLinkAdjacency _ (history_valid_all ω hω i)-globalStarAverage _)

noncomputable def prefixEdgeForcing {n : ℕ} (ω : History (Graph n) (prefixTime n))
    (i : ℕ) (e : CompleteEdge n) : ℝ :=
  prefixCenteredEdge ω 0 e+
    historyNoise (fun _ => step)
      (fun k H => (currentCodegree H (completeEdgePair e).val.1 (completeEdgePair e).val.2 : ℝ)/earlyTemplateScale 1 2 n k)
      (prefixTime n) i ω+
    ∑ k ∈ Finset.range i, prefixEdgeScalar ω k*(prefixCenteredEdge ω k e+1)

lemma prefixEdgeForcing_zero {n : ℕ} (ω : History (Graph n) (prefixTime n)) :
    prefixEdgeForcing ω 0 = prefixCenteredEdge ω 0 := by
  funext e
  simp [prefixEdgeForcing]

lemma prefix_centered_edge_recurrence {n i : ℕ} (ω : History (Graph n) (prefixTime n))
    (hω : ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support)
    (hi : i < prefixTime n) (hs : earlyTemplateScale 1 2 n i ≠ 0)
    (e : CompleteEdge n) (he : e ∈ graphActive (ω (historyIndex (prefixTime n) (i+1)))) :
    prefixCenteredEdge ω (i+1) e = prefixCenteredEdge ω i e-
      prefixEdgeRate ω i*(movingStarLift (fun e : CompleteEdge n => e.val)
        (movingStarMean (fun e : CompleteEdge n => e.val)
          (graphActive (ω (historyIndex (prefixTime n) i))) (prefixCenteredEdge ω i)) e+
        prefixEdgeResidual ω hω i (prefixCenteredEdge ω i) e)+
      (prefixEdgeForcing ω (i+1) e-prefixEdgeForcing ω i e) := by
  have hpath := (historyLaw_path_support (PMF.pure (completeGraph n)) (fun _ => step)
    (prefixTime n) (prefixTime n) le_rfl ω hω).2 i hi
  have he0 : e.val ∈ ω (historyIndex (prefixTime n) i) := step_support_subset hpath ((mem_graphActive _ _).mp he)
  have hd := centered_edge_operator_drift _ (history_valid_all ω hω i)
    (earlyTemplateScale 1 2 n i) (earlyTemplateScale 1 2 n (i+1)) hs e he0
  unfold prefixEdgeForcing
  rw [historyNoise_succ_same _ _ _ _ hi,Finset.sum_range_succ]
  simp only [historyIncrement] at *
  change _ = _ at hd
  dsimp only [prefixCenteredEdge,prefixEdgeRate,prefixEdgeScalar,prefixEdgeResidual] at *
  dsimp only [centeredEdgeVector] at *
  linarith only [hd]

end SharpTerminalLeave
end
end

end OAI
