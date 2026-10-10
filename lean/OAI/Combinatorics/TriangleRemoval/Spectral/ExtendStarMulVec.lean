import Mathlib
import OAI.Combinatorics.TriangleRemoval.Spectral.LinkStarMatrix
import OAI.Combinatorics.TriangleRemoval.Process.CompleteEdge

namespace OAI

section
noncomputable section
open scoped BigOperators
open Classical Matrix

namespace SharpTerminalLeave

lemma extendStar_mulVec_apply {E : Type*} [Fintype E] [DecidableEq E]
    (S : Finset E) (M : Matrix S S ℝ) (z : E → ℝ) (e : E) :
    (extendStar S M *ᵥ z) e = if he : e ∈ S then
      (M *ᵥ fun f : S => z f.val) ⟨e,he⟩ else 0 := by
  rw [extendStar,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,starInclusion_mulVec]
  simp only [Matrix.mulVec,dotProduct,starInclusion]
  by_cases he : e ∈ S
  · have hh : ∀ f : S, e = f.val ↔ f = ⟨e,he⟩ := fun f => by rw [Subtype.ext_iff]; exact eq_comm
    simp [he,hh]
  · have hh : ∀ f : S, e ≠ f.val := fun f hf => he (hf.symm ▸ f.property)
    simp [he,hh]

lemma extendStar_average_apply {E : Type*} [Fintype E] [DecidableEq E]
    (S : Finset E) (z : E → ℝ) (e : E) :
    (extendStar S averagingProjector *ᵥ z) e =
      if e ∈ S then (∑ f ∈ S, z f)/(S.card : ℝ) else 0 := by
  rw [extendStar_mulVec_apply]
  split_ifs with he
  · simp only [Matrix.mulVec,dotProduct,averagingProjector,Fintype.card_coe]
    rw [← Finset.mul_sum,Finset.sum_coe_sort]
    ring
  · rfl

lemma graphActive_star_sum {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (x : CompleteEdge n → ℝ) (u : Fin n) :
    (∑ e ∈ (graphActive G).filter (fun e => u ∈ e.val), x e) =
      ∑ e ∈ edgeStar G u, graphRestrict G hG x e := by
  rw [Finset.sum_filter]
  rw [graphActive_sum G hG]
  simp only [edgeStar,Finset.sum_filter]
  rfl

lemma graphActive_star_card {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n) (u : Fin n) :
    ((graphActive G).filter (fun e => u ∈ e.val)).card = (edgeStar G u).card := by
  have hh := graphActive_star_sum G hG (fun _ => 1) u
  simpa only [graphRestrict,LinearMap.coe_mk,AddHom.coe_mk,Finset.sum_const,nsmul_eq_mul,mul_one,
    Nat.cast_inj] using hh

lemma graph_movingStarMean {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (x : CompleteEdge n → ℝ) (u : Fin n) :
    movingStarMean (fun e : CompleteEdge n => e.val) (graphActive G) x u =
      (∑ e ∈ edgeStar G u, graphRestrict G hG x e)/(edgeStar G u).card := by
  unfold movingStarMean movingStarDegree
  congr 1
  · convert graphActive_star_sum G hG x u using 1
    congr 1
    ext e
    simp
  · convert congrArg (Nat.cast : ℕ → ℝ) (graphActive_star_card G hG u) using 1
    congr 2
    ext e
    simp

lemma graph_movingStarLift {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (x : CompleteEdge n → ℝ) (e : CompleteEdge n) (he : e ∈ graphActive G) :
    movingStarLift (fun e : CompleteEdge n => e.val)
      (movingStarMean (fun e : CompleteEdge n => e.val) (graphActive G) x) e =
      graphMatrixLift G hG (globalStarAverage G) x e := by
  have heG : e.val ∈ G := (mem_graphActive G e).mp he
  change (∑ u ∈ e.val, _) = (graphExtend G (globalStarAverage G *ᵥ graphRestrict G hG x)) e
  simp only [graphExtend,LinearMap.coe_mk,AddHom.coe_mk,dite_eq_left heG]
  rw [globalStarAverage,Matrix.sum_mulVec]
  simp only [Finset.sum_apply,extendStar_average_apply,mem_edgeStar]
  rw [← Finset.sum_filter]
  have heq : Finset.univ.filter (fun u => u ∈ e.val) = e.val := by ext; simp
  rw [heq]
  exact Finset.sum_congr rfl (fun u _ => graph_movingStarMean G hG x u)

end SharpTerminalLeave
end
end

end OAI
