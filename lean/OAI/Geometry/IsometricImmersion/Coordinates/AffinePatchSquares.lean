import OAI.Geometry.IsometricImmersion.Coordinates.OrientedCenterNets
import OAI.Geometry.IsometricImmersion.Coordinates.AffinePullback

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter Set Metric

namespace SmoothLocal.Geometry

def closedPatchBox : Set Coord := {x | ∀ i, x i ∈ Set.Icc (-4 : ℝ) 4}

theorem mem_closedPatchBox_iff_norm_le (x : Coord) :
    x ∈ closedPatchBox ↔ ‖x‖ ≤ 4 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  simp only [closedPatchBox, Set.mem_ofPred_eq, Set.mem_Icc, Real.norm_eq_abs, abs_le]

theorem closedPatchBox_eq_closedBall : closedPatchBox = Metric.closedBall 0 4 := by
  ext x
  simpa only [Metric.mem_closedBall, dist_zero_right] using mem_closedPatchBox_iff_norm_le x

theorem closedPatchBox_isCompact : IsCompact closedPatchBox := by
  rw [closedPatchBox_eq_closedBall]
  exact isCompact_closedBall 0 4

def closedAffineSquare (c : Coord) (scale : ℝ) (R : Matrix (Fin 2) (Fin 2) ℝ) : Set Coord :=
  affineCoordinates c (scale • R) '' closedPatchBox

theorem closedAffineSquare_isCompact (c : Coord) (scale : ℝ)
    (R : Matrix (Fin 2) (Fin 2) ℝ) : IsCompact (closedAffineSquare c scale R) :=
  closedPatchBox_isCompact.image (affineCoordinates_contDiff c (scale • R)).continuous

theorem center_mem_closedAffineSquare (c : Coord) (scale : ℝ)
    (R : Matrix (Fin 2) (Fin 2) ℝ) : c ∈ closedAffineSquare c scale R := by
  refine ⟨0, ?_, affineCoordinates_zero c (scale • R)⟩
  exact (mem_closedPatchBox_iff_norm_le 0).mpr (by simp)

theorem closedAffineSquare_dist_le (c : Coord) {scale : ℝ} (hscale : 0 ≤ scale)
    (R : Matrix (Fin 2) (Fin 2) ℝ) {p : Coord} (hp : p ∈ closedAffineSquare c scale R) :
    dist p c ≤ scale * (4 * ‖matrixContinuousLinear R‖) := by
  obtain ⟨x, hx, rfl⟩ := hp
  have hxnorm := (mem_closedPatchBox_iff_norm_le x).mp hx
  have hmap := (matrixContinuousLinear R).le_opNorm_of_le hxnorm
  calc
    dist (affineCoordinates c (scale • R) x) c = scale * ‖matrixContinuousLinear R x‖ := by
      simp only [affineCoordinates, Matrix.smul_mulVec, dist_eq_norm,
        add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale,
        matrixContinuousLinear_apply]
    _ ≤ scale * (‖matrixContinuousLinear R‖ * 4) := mul_le_mul_of_nonneg_left hmap hscale
    _ = _ := by ring

private theorem finite_positive_lower_bound {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) : ∃ δ > 0, ∀ i ∈ s, δ < a i := by
  classical
  revert ha
  induction s using Finset.induction_on with
  | empty => intro ha; exact ⟨1, by norm_num, by simp⟩
  | @insert i s hi ih =>
      intro ha
      obtain ⟨δ, hδ, hδa⟩ := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      have hai := ha i (Finset.mem_insert_self i s)
      refine ⟨min (a i / 2) δ, lt_min (by positivity) hδ, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      · exact lt_of_le_of_lt (min_le_right _ _) (hδa j hj)

theorem exists_finite_affine_square_scale {ι : Type*} [Fintype ι]
    (c : ι → Coord) (hc : Function.Injective c) {U : Set Coord}
    (hU : IsOpen U) (hcU : ∀ i, c i ∈ U)
    (R : Matrix (Fin 2) (Fin 2) ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ scale > 0, scale ≤ η ∧
      (∀ i, closedAffineSquare (c i) scale R ⊆ U) ∧
      Pairwise (fun i j => Disjoint (closedAffineSquare (c i) scale R)
        (closedAffineSquare (c j) scale R)) ∧
      ∀ i p, p ∈ closedAffineSquare (c i) scale R → dist p (c i) ≤ η := by
  classical
  have hballs : ∀ i, ∃ a > 0, Metric.ball (c i) a ⊆ U :=
    fun i => Metric.mem_nhds_iff.mp (hU.mem_nhds (hcU i))
  choose a ha haU using hballs
  obtain ⟨ρ, hρ, hρa⟩ := finite_positive_lower_bound Finset.univ a (by simpa using ha)
  let separation : ι × ι → ℝ := fun ij => if ij.1 = ij.2 then 1 else dist (c ij.1) (c ij.2)
  have hsep : ∀ ij ∈ (Finset.univ : Finset (ι × ι)), 0 < separation ij := by
    intro ij _
    dsimp only [separation]
    split_ifs with hij
    · norm_num
    · exact dist_pos.mpr (fun h => hij (hc h))
  obtain ⟨δ, hδ, hδsep⟩ := finite_positive_lower_bound Finset.univ separation hsep
  let t : ℝ := min ρ (min δ η) / 4
  have ht : 0 < t := by dsimp only [t]; positivity
  have htρ : t ≤ ρ / 4 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have htδ : t ≤ δ / 4 := div_le_div_of_nonneg_right
    ((min_le_right ρ (min δ η)).trans (min_le_left δ η)) (by norm_num)
  have htη : t ≤ η / 4 := div_le_div_of_nonneg_right
    ((min_le_right ρ (min δ η)).trans (min_le_right δ η)) (by norm_num)
  let scale : ℝ := t / (1 + 4 * ‖matrixContinuousLinear R‖)
  have hden : 0 < 1 + 4 * ‖matrixContinuousLinear R‖ := by positivity
  have hscale : 0 < scale := div_pos ht hden
  have hscaleeq : scale * (1 + 4 * ‖matrixContinuousLinear R‖) = t :=
    div_mul_cancel₀ t hden.ne'
  have hscalet : scale ≤ t := by
    nlinarith [mul_nonneg hscale.le (norm_nonneg (matrixContinuousLinear R))]
  have hsize : scale * (4 * ‖matrixContinuousLinear R‖) ≤ t := by nlinarith
  have hcontain (i : ι) : closedAffineSquare (c i) scale R ⊆ Metric.closedBall (c i) t := by
    intro p hp
    exact (closedAffineSquare_dist_le (c i) hscale.le R hp).trans hsize
  refine ⟨scale, hscale, by linarith, ?_, ?_, ?_⟩
  · intro i
    apply Set.Subset.trans (hcontain i)
    apply Set.Subset.trans (Metric.closedBall_subset_ball (show t < a i from by
      have := hρa i (Finset.mem_univ i)
      linarith))
    exact haU i
  · intro i j hij
    have hd : δ < dist (c i) (c j) := by
      simpa only [separation, ite_eq_right hij] using hδsep (i, j) (Finset.mem_univ (i, j))
    exact (Metric.closedBall_disjoint_closedBall (show t + t < dist (c i) (c j) by
      linarith)).mono (hcontain i) (hcontain j)
  · intro i p hp
    have := hcontain i hp
    change dist p (c i) ≤ t at this
    linarith

theorem exists_finset_affine_square_scale (s : Finset Coord) {U : Set Coord}
    (hU : IsOpen U) (hsU : ∀ c ∈ s, c ∈ U)
    (R : Matrix (Fin 2) (Fin 2) ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ scale > 0, scale ≤ η ∧
      (∀ c ∈ s, closedAffineSquare c scale R ⊆ U) ∧
      (∀ c ∈ s, ∀ d ∈ s, c ≠ d → Disjoint (closedAffineSquare c scale R)
        (closedAffineSquare d scale R)) ∧
      ∀ c ∈ s, ∀ p ∈ closedAffineSquare c scale R, dist p c ≤ η := by
  classical
  obtain ⟨scale, hscale, hscaleη, hsub, hdisj, hbound⟩ :=
    exists_finite_affine_square_scale (fun c : {c // c ∈ s} => c.val)
      Subtype.val_injective hU (fun c => hsU c.val c.property) R hη
  exact ⟨scale, hscale, hscaleη, fun c hc => hsub ⟨c, hc⟩,
    fun c hc d hd hcd => hdisj (i := ⟨c, hc⟩) (j := ⟨d, hd⟩)
      (fun h => hcd (congrArg Subtype.val h)),
    fun c hc p hp => hbound ⟨c, hc⟩ p hp⟩

end SmoothLocal.Geometry

end

end OAI
