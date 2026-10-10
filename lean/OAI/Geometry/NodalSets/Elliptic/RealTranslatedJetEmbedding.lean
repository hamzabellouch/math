import Mathlib.MeasureTheory.Group.Integral
import OAI.Geometry.NodalSets.Elliptic.RealCubeL2EmbeddingLemmas

namespace OAI

namespace Yau.Geometry
open Yau.Analysis MeasureTheory Set Function Metric
open scoped ContDiff
noncomputable section

lemma partialJet_translate (W : Yau.Jets.Coord → ℝ) (a : Yau.Jets.Coord)
    (ds : List (Fin 4)) (x : Yau.Jets.Coord) :
    partialJet (fun z ↦ W (a+z)) ds x = partialJet W ds (a+x) := by
  induction ds generalizing x with
  | nil => rfl
  | cons i ds ih =>
    have he : partialJet (fun z ↦ W (a+z)) ds = fun z ↦ partialJet W ds (a+z) := funext ih
    change fderiv ℝ (partialJet (fun z ↦ W (a+z)) ds) x _ = _
    rw [he,fderiv_comp_add_left]
    rfl

lemma realFiniteJetSquare_translate (W : Yau.Jets.Coord → ℝ) (a : Yau.Jets.Coord)
    (n : ℕ) (x : Yau.Jets.Coord) :
    realFiniteJetSquare (fun z ↦ W (a+z)) n x = realFiniteJetSquare W n (a+x) := by
  simp only [realFiniteJetSquare,partialJet_translate]

lemma real_integral_ball_translate (F : Yau.Jets.Coord → ℝ) (a : Yau.Jets.Coord) (r : ℝ) :
    (∫ z in closedBall (0 : Yau.Jets.Coord) r, F (a+z)) = ∫ z in closedBall a r, F z := by
  have hs : (fun z : Yau.Jets.Coord ↦ a+z) ⁻¹' closedBall a r = closedBall 0 r := by
    ext z
    simp only [mem_preimage,mem_closedBall,dist_self_add_left,dist_zero_right]
  rw [← hs]
  exact (measurePreserving_add_left volume a).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft a).measurableEmbedding F _

theorem real_point_jet_l2_embedding (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W)
    (ds : List (Fin 4)) (x : Yau.Jets.Coord) :
    (partialJet W ds x)^2 ≤ 256 * (∫ z in closedBall x 1,
      realFiniteJetSquare W (ds.length+4) z) := by
  have h := real_cube_l2_embedding (fun z ↦ W (x+z))
    (hW.comp (contDiff_const.add contDiff_id)) ds 0 (by intro i; simp)
  simp only [partialJet_translate,add_zero,realFiniteJetSquare_translate,
    real_integral_ball_translate] at h
  exact h

theorem real_uniform_jet_l2_embedding (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W)
    (n : ℕ) (y : Yau.Jets.Coord) (r : ℝ) (ds : List (Fin 4)) (hd : ds.length ≤ n)
    (x : Yau.Jets.Coord) (hx : x ∈ closedBall y r) :
    (partialJet W ds x)^2 ≤ 256 * (∫ z in closedBall y (r+1), realFiniteJetSquare W (n+4) z) := by
  have hsub : closedBall x 1 ⊆ closedBall y (r+1) := by
    intro z hz
    exact (dist_triangle z x y).trans (by linarith [mem_closedBall.mp hz,mem_closedBall.mp hx])
  have hs (z : Yau.Jets.Coord) : realFiniteJetSquare W (ds.length+4) z ≤ realFiniteJetSquare W (n+4) z := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intro a _ _
    exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hi (m : ℕ) (a : Yau.Jets.Coord) (s : ℝ) :
      IntegrableOn (realFiniteJetSquare W m) (closedBall a s) :=
    (realFiniteJetSquare_smooth W hW m).continuous.continuousOn.integrableOn_compact (isCompact_closedBall a s)
  have hmono := (setIntegral_mono_on (hi (ds.length+4) x 1) (hi (n+4) x 1)
    isClosed_closedBall.measurableSet (fun z _ ↦ hs z)).trans
    (setIntegral_mono_set (hi (n+4) y (r+1))
      (Filter.Eventually.of_forall (realFiniteJetSquare_nonneg W (n+4)))
      (Filter.Eventually.of_forall hsub))
  exact (real_point_jet_l2_embedding W hW ds x).trans
    (mul_le_mul_of_nonneg_left hmono (by norm_num))

end
end Yau.Geometry

end OAI
