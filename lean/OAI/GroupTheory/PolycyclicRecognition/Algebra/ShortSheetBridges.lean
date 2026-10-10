import OAI.GroupTheory.PolycyclicRecognition.Analysis.CenteredImagePaths
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarsePathRadius

namespace OAI

/-! # Short bridges between the two sheets at a common pivot -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped NNReal

theorem exists_short_path_of_minimizing_paths
    {G : Type*} [Group G] [MetricSpace G] [IsTopologicalGroup G] [IsIsometricSMul G G]
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|) (a b : G) :
    ∃ γ : Path a b, PathMetricBound γ (dist a b) 0 := by
  obtain ⟨f, hf0, hf1, hf⟩ := hpath (a⁻¹ * b)
  have hd : dist (1 : G) (a⁻¹ * b) = dist a b := by
    simpa only [mul_one, mul_inv_cancel_left] using
      (dist_mul_left a (1 : G) (a⁻¹ * b)).symm
  have hlip : LipschitzWith ⟨dist a b, dist_nonneg⟩ (fun t : unitInterval => f t) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    change dist (f s) (f t) ≤ dist a b * dist s t
    rw [Subtype.dist_eq, Real.dist_eq, ← hd]
    exact hf s s.property t t.property
  let γ : Path a b := {
    toFun := fun t => a * f t
    continuous_toFun := continuous_const.mul hlip.continuous
    source' := by simp only [Icc.coe_zero, hf0, mul_one]
    target' := by simp only [Icc.coe_one, hf1, mul_inv_cancel_left] }
  refine ⟨γ, ?_⟩
  intro s t
  change dist (a * f s) (a * f t) ≤ _
  rw [dist_mul_left, add_zero]
  simpa only [hd] using hf s s.property t t.property

/-- Adding the two pivot bridges preserves the template, with only the
Lipschitz image of their lengths added to the height error. -/
theorem exists_bridged_profile_path
    {X W : Type*} [PseudoMetricSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (hpath : ∀ a b : X, ∃ γ : Path a b, PathMetricBound γ (dist a b) 0)
    {a a' b' b : X} (middle : Path a' b')
    {L κ δ B r : ℝ} (hκ : 0 ≤ κ) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hm : PathMetricBound middle L κ) (ha : dist a a' ≤ δ) (hb : dist b' b ≤ δ)
    (J : X → W) {K : ℝ≥0} (hJ : LipschitzWith K J)
    (E : Set W) (hE0 : (0 : W) ∈ E)
    (himage : ∀ t, ∃ w ∈ E, ‖J (middle t) - J a' - r • w‖ ≤ B) :
    ∃ γ : Path a b, PathMetricBound γ (4 * (max L 0 + δ)) (4 * κ) ∧
      ∀ t, ∃ w ∈ E, ‖J (γ t) - J a - r • w‖ ≤ B + 2 * K * δ := by
  obtain ⟨first, hfirst⟩ := hpath a a'
  obtain ⟨last, hlast⟩ := hpath b' b
  let C := max L 0 + δ
  have hC : 0 ≤ C := add_nonneg (le_max_right _ _) hδ
  have hfirst' : PathMetricBound first C κ := hfirst.mono
    (ha.trans (le_add_of_nonneg_left (le_max_right _ _))) hκ
  have hlast' : PathMetricBound last C κ := hlast.mono
    (hb.trans (le_add_of_nonneg_left (le_max_right _ _))) hκ
  have hm' : PathMetricBound middle C κ := hm.mono
    ((le_max_left _ _).trans (le_add_of_nonneg_right hδ)) le_rfl
  have hfm := hfirst'.trans hκ hm'
  have hlast'' : PathMetricBound last (2 * C) (2 * κ) :=
    hlast'.mono (by linarith) (by linarith)
  have hbound := hfm.trans (by linarith : 0 ≤ 2 * κ) hlast''
  let S := {z : X | ∃ w ∈ E, ‖J z - J a - r • w‖ ≤ B + 2 * K * δ}
  have hshift : ‖J a' - J a‖ ≤ K * δ := by
    rw [← dist_eq_norm]
    exact (hJ.dist_le_mul a' a).trans
      (mul_le_mul_of_nonneg_left (by simpa only [dist_comm] using ha) K.coe_nonneg)
  have hmiddle : ∀ t, middle t ∈ S := by
    intro t
    obtain ⟨w, hw, he⟩ := himage t
    refine ⟨w, hw, ?_⟩
    calc
      ‖J (middle t) - J a - r • w‖ ≤ ‖J (middle t) - J a' - r • w‖ + ‖J a' - J a‖ := by
        convert norm_add_le (J (middle t) - J a' - r • w) (J a' - J a) using 1
        congr 1
        abel
      _ ≤ B + K * δ := add_le_add he hshift
      _ ≤ B + 2 * K * δ := by nlinarith [mul_nonneg K.coe_nonneg hδ]
  have hfirstS : ∀ t, first t ∈ S := by
    intro t
    refine ⟨0, hE0, ?_⟩
    rw [smul_zero, sub_zero, ← dist_eq_norm]
    have hd := hfirst.dist_source_le (dist_nonneg (x := a) (y := a')) t
    have hd' : dist (first t) a ≤ δ := by
      rw [dist_comm]
      exact hd.trans (by simpa only [add_zero] using ha)
    have he := (hJ.dist_le_mul (first t) a).trans
      (mul_le_mul_of_nonneg_left hd' K.coe_nonneg)
    exact he.trans (by nlinarith [mul_nonneg K.coe_nonneg hδ])
  have hlastS : ∀ t, last t ∈ S := by
    intro t
    obtain ⟨w, hw, he⟩ := himage 1
    rw [Path.target] at he
    have hd := (hlast.dist_source_le (dist_nonneg (x := b') (y := b)) t).trans
      (by simpa only [add_zero] using hb)
    have hdiff : ‖J (last t) - J b'‖ ≤ K * δ := by
      rw [← dist_eq_norm]
      exact (hJ.dist_le_mul (last t) b').trans
        (mul_le_mul_of_nonneg_left (by simpa only [dist_comm] using hd) K.coe_nonneg)
    refine ⟨w, hw, ?_⟩
    calc
      ‖J (last t) - J a - r • w‖ ≤
          ‖J (last t) - J b'‖ + ‖J b' - J a' - r • w‖ + ‖J a' - J a‖ := by
        calc
          _ = ‖(J (last t) - J b') + (J b' - J a' - r • w) + (J a' - J a)‖ := by congr 1; abel
          _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ K * δ + B + K * δ := add_le_add (add_le_add hdiff he) hshift
      _ = B + 2 * K * δ := by ring
  refine ⟨(first.trans middle).trans last, ?_,
    path_trans_range_mem (path_trans_range_mem hfirstS hmiddle) hlastS⟩
  have hL : 4 * (max L 0 + δ) = 2 * (2 * C) := by dsimp only [C]; ring
  have hκ' : 4 * κ = 2 * (2 * κ) := by ring
  rw [hL, hκ']
  exact hbound

end PolycyclicRecognition

end

end OAI
