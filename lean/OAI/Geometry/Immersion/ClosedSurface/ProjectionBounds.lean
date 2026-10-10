import OAI.Geometry.Immersion.ClosedSurface.NormalProjection

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open SmallModes Set Metric

abbrev TangentPair := RVec 4 × RVec 4

def normalColumns (p : TangentPair) : Fin 4 → RVec 4 :=
  fun i => realNormalPart p.1 p.2 (Pi.single i 1)

lemma contDiff_gram_pair : ContDiff ℝ ∞ (fun p : TangentPair => NormalFrame.gramDet p.1 p.2) := by
  unfold NormalFrame.gramDet dotProduct
  fun_prop

lemma contDiffAt_normalColumns {p : TangentPair} (hp : NormalFrame.gramDet p.1 p.2 ≠ 0) :
    ContDiffAt ℝ ∞ normalColumns p := by
  apply contDiffAt_pi.mpr
  intro i
  unfold normalColumns realNormalPart
  have hd : ContDiffAt ℝ ∞ (fun p : TangentPair => NormalFrame.gramDet p.1 p.2) p :=
    contDiff_gram_pair.contDiffAt
  have hX : ContDiffAt ℝ ∞ (fun p : TangentPair => p.1) p := contDiff_fst.contDiffAt
  have hY : ContDiffAt ℝ ∞ (fun p : TangentPair => p.2) p := contDiff_snd.contDiffAt
  apply (contDiffAt_const.sub ?_).sub ?_
  · apply ContDiffAt.fun_smul _ hX
    apply ContDiffAt.fun_div _ hd hp
    unfold dotProduct
    fun_prop
  · apply ContDiffAt.fun_smul _ hY
    apply ContDiffAt.fun_div _ hd hp
    unfold dotProduct
    fun_prop

lemma realNormalPart_columns (p : TangentPair) (W : RVec 4) :
    realNormalPart p.1 p.2 W = ∑ i : Fin 4, W i • normalColumns p i := by
  have hlin := realNormalPart_linear p.1 p.2
  have he : W = ∑ i : Fin 4, W i • (Pi.single i 1 : RVec 4) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => arg 3; rw [he]
  change (hlin.mk' _) (∑ i : Fin 4, W i • Pi.single i 1) = _
  simp only [map_sum,map_smul,IsLinearMap.mk'_apply,normalColumns]

lemma norm_realNormalPart_columns (p : TangentPair) (W : RVec 4) :
    ‖realNormalPart p.1 p.2 W‖ ≤ 4 * ‖normalColumns p‖ * ‖W‖ := by
  rw [realNormalPart_columns]
  calc
    _ ≤ ∑ i : Fin 4, ‖W i • normalColumns p i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 4, ‖normalColumns p‖ * ‖W‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact (mul_le_mul (norm_le_pi_norm W i) (norm_le_pi_norm (normalColumns p) i)
        (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = _ := by simp; ring

lemma norm_realNormalPart_change (p q : TangentPair) (W : RVec 4) :
    ‖realNormalPart p.1 p.2 W - realNormalPart q.1 q.2 W‖ ≤
      4 * ‖normalColumns p - normalColumns q‖ * ‖W‖ := by
  rw [realNormalPart_columns,realNormalPart_columns,← Finset.sum_sub_distrib]
  calc
    _ = ‖∑ i : Fin 4, W i • (normalColumns p i-normalColumns q i)‖ := by simp [smul_sub]
    _ ≤ ∑ i : Fin 4, ‖W i • (normalColumns p i-normalColumns q i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 4, ‖normalColumns p-normalColumns q‖ * ‖W‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact (mul_le_mul (norm_le_pi_norm W i)
        (norm_le_pi_norm (normalColumns p-normalColumns q) i)
        (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = _ := by simp; ring



theorem compact_normal_projection_bounds (R c : ℝ) (hc : 0 < c) :
    ∃ L D : ℝ, 0 ≤ L ∧ 0 ≤ D ∧ ∀ (p q : TangentPair),
      ‖p‖ ≤ R → c ≤ NormalFrame.gramDet p.1 p.2 →
      ‖q‖ ≤ R → c ≤ NormalFrame.gramDet q.1 q.2 → ∀ W Z : RVec 4,
      ‖realNormalPart p.1 p.2 W - realNormalPart q.1 q.2 Z‖ ≤
        L * ‖p-q‖ * ‖W‖ + D * ‖W-Z‖ := by
  let K : Set TangentPair := closedBall 0 R ∩ {p | c ≤ NormalFrame.gramDet p.1 p.2}
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const contDiff_gram_pair.continuous)
  have hne (p : TangentPair) (hp : p ∈ K) : NormalFrame.gramDet p.1 p.2 ≠ 0 :=
    (hc.trans_le hp.2).ne'
  have hloc : LocallyLipschitzOn K normalColumns := by
    intro p hp
    obtain ⟨L,U,hU,hL⟩ := ((contDiffAt_normalColumns (hne p hp)).of_le
      (show (1 : ℕ∞ω) ≤ ∞ by simp)).exists_lipschitzOnWith
    exact ⟨L,U,Filter.mem_of_superset (mem_nhdsWithin_of_mem_nhds hU) (fun _ h => h),hL⟩
  obtain ⟨L,hL⟩ := hloc.exists_lipschitzOnWith_of_compact hK
  have hcont : ContinuousOn normalColumns K := fun p hp =>
    (contDiffAt_normalColumns (hne p hp)).continuousAt.continuousWithinAt
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨4*(L:ℝ),4*max D 0,by positivity,by positivity,?_⟩
  intro p q hp hpD hq hqD W Z
  have hpK : p ∈ K := ⟨by simpa only [mem_closedBall,dist_zero_right] using hp,hpD⟩
  have hqK : q ∈ K := ⟨by simpa only [mem_closedBall,dist_zero_right] using hq,hqD⟩
  have hcols : ‖normalColumns p-normalColumns q‖ ≤ (L:ℝ)*‖p-q‖ := by
    simpa only [dist_eq_norm] using hL.dist_le_mul p hpK q hqK
  have hdecomp : realNormalPart p.1 p.2 W-realNormalPart q.1 q.2 Z =
      (realNormalPart p.1 p.2 W-realNormalPart q.1 q.2 W) +
        realNormalPart q.1 q.2 (W-Z) := by
    rw [(realNormalPart_linear q.1 q.2).map_sub]
    abel
  rw [hdecomp]
  calc
    _ ≤ ‖realNormalPart p.1 p.2 W-realNormalPart q.1 q.2 W‖ +
        ‖realNormalPart q.1 q.2 (W-Z)‖ := norm_add_le _ _
    _ ≤ 4*‖normalColumns p-normalColumns q‖*‖W‖ + 4*‖normalColumns q‖*‖W-Z‖ :=
      add_le_add (norm_realNormalPart_change p q W) (norm_realNormalPart_columns q (W-Z))
    _ ≤ (4*(L:ℝ))*‖p-q‖*‖W‖ + (4*max D 0)*‖W-Z‖ := by
      have hcq := (hD q hqK).trans (le_max_left D 0)
      nlinarith [mul_le_mul_of_nonneg_right hcols (show 0 ≤ 4*‖W‖ by positivity),
        mul_le_mul_of_nonneg_right hcq (show 0 ≤ 4*‖W-Z‖ by positivity)]

end ClosedSurfaceR4.RealModes

end

end OAI
