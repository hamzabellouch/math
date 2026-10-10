import OAI.Geometry.CylinderCovering.Nilpotent.SmoothRateDefinitions
import OAI.Geometry.CylinderCovering.Nilpotent.Rows
import OAI.Geometry.CylinderCovering.Nilpotent.Grid

namespace OAI

noncomputable section
open Set MeasureTheory

namespace CylinderCovering.NilpotentRate

theorem cell_cover {δ : ℝ} (hδ : 0 < δ) (b : Plane) : ∃ i : Index, b ∈ cell δ i := by
  refine ⟨(⌊b 0 / δ⌋, ⌊b 1 / δ⌋), ?_⟩
  have h0 := NilpotentGrid.floor_cell (x := b 0) hδ
  have h1 := NilpotentGrid.floor_cell (x := b 1) hδ
  exact ⟨h0.1, h0.2, h1.1, h1.2⟩

theorem choose_tags_frames {δ : ℝ} {D : Set Plane} {G : Plane → Plane}
    (hnil : ∀ p ∈ D, (fderiv ℝ G p).comp (fderiv ℝ G p) = 0) :
    ∃ tag : Index → Plane, ∃ Q : Index → Plane ≃ₗᵢ[ℝ] Plane,
      ∀ i ∈ coarseIndices δ D, tag i ∈ cell δ i ∩ D ∧
        IsShearFrame (fderiv ℝ G (tag i)) (Q i) := by
  classical
  have ht : ∀ i : Index, ∃ b : Plane, i ∈ coarseIndices δ D → b ∈ cell δ i ∩ D := by
    intro i
    by_cases hi : i ∈ coarseIndices δ D
    · obtain ⟨b, hb⟩ := hi
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  choose tag htag using ht
  have hQ : ∀ i : Index, ∃ Q : Plane ≃ₗᵢ[ℝ] Plane,
      i ∈ coarseIndices δ D → IsShearFrame (fderiv ℝ G (tag i)) Q := by
    intro i
    by_cases hi : i ∈ coarseIndices δ D
    · obtain ⟨Q, d, hQ⟩ := RuledApproximation.nilpotent_frame _ (hnil _ (htag i hi).2)
      exact ⟨Q, fun _ => ⟨d, hQ⟩⟩
    · exact ⟨LinearIsometryEquiv.refl ℝ Plane, fun h => (hi h).elim⟩
  choose Q hQ using hQ
  exact ⟨tag, Q, fun i hi => ⟨htag i hi, hQ i hi⟩⟩

theorem sliding_rows_of_frame {A : Plane →L[ℝ] Plane} {Q : Plane ≃ₗᵢ[ℝ] Plane}
    (hQ : IsShearFrame A Q) (q : Plane) {τ : ℝ} (hτ : 0 < τ) (s : ℝ) (x : Plane) :
    ∃ i : Index, ∃ p ∈ tile Q τ i,
      x = p + s • (A (τ • Q (integerVector i)) + q) ∧
        ‖x - (τ • Q (integerVector i) + s • (A (τ • Q (integerVector i)) + q))‖ ≤
          Real.sqrt 2 * τ := by
  obtain ⟨d, hQ⟩ := hQ
  let u : Plane := τ⁻¹ • Q.symm (x - s • q)
  obtain ⟨i, j, hi, hj⟩ := RuledApproximation.sliding_rows_cover (s * d) (u 0) (u 1)
  let k : Index := (i, j)
  let z : Plane := RuledApproximation.vec2 (u 0 - ((i : ℝ) + s * d * j)) (u 1 - j)
  have hz : z ∈ RuledApproximation.unitSquare := by
    intro n
    fin_cases n
    · exact hi
    · exact hj
  let l : Plane := τ • Q (integerVector k)
  have hul : τ • u = Q.symm x - s • Q.symm q := by
    dsimp [u]
    rw [smul_smul, mul_inv_cancel₀ hτ.ne', one_smul, map_sub, map_smul]
  have hal : Q.symm (A l) = τ • RuledApproximation.vec2 (d * (j : ℝ)) 0 := by
    dsimp [l]
    rw [map_smul, map_smul, hQ]
    rfl
  have hx : x = l + τ • Q z + s • (A l + q) := by
    apply Q.symm.injective
    simp only [map_add, map_smul, Q.symm_apply_apply]
    rw [hal]
    have hxl : Q.symm x = τ • u + s • Q.symm q := by rw [hul]; abel
    rw [hxl]
    simp only [l, map_smul, Q.symm_apply_apply]
    change τ • u + s • Q.symm q =
      τ • integerVector k + τ • z + s • (τ • RuledApproximation.vec2 (d * (j : ℝ)) 0 + Q.symm q)
    ext n
    fin_cases n <;> simp [z, k, integerVector, RuledApproximation.vec2] <;> ring
  refine ⟨k, l + τ • Q z, ?_, hx, ?_⟩
  · refine ⟨z, hz, ?_⟩
    simp [l, map_add, smul_add]
  · change ‖x - (l + s • (A l + q))‖ ≤ _
    have he : x - (l + s • (A l + q)) = τ • Q z := by rw [hx]; abel
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hτ, Q.norm_map]
    have hb := mul_le_mul_of_nonneg_left (RuledApproximation.unitSquare_norm_le hz) hτ.le
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]

theorem nilpotent_inverse_norm_bound {A : Plane →L[ℝ] Plane} (hA : A.comp A = 0)
    {M s : ℝ} (hM : 0 ≤ M) (hAM : ‖A‖ ≤ M) (hs : |s| ≤ 1) (v : Plane) :
    ‖v‖ ≤ (1 + M) * ‖v + s • A v‖ := by
  have hAA : A (A v) = 0 := congrArg (fun B : Plane →L[ℝ] Plane => B v) hA
  have he : v = (v + s • A v) - s • A (v + s • A v) := by
    rw [map_add, map_smul, hAA, smul_zero, add_zero]
    abel
  calc
    ‖v‖ = ‖(v + s • A v) - s • A (v + s • A v)‖ := congrArg norm he
    _ ≤ ‖v + s • A v‖ + ‖s • A (v + s • A v)‖ := norm_sub_le _ _
    _ ≤ ‖v + s • A v‖ + M * ‖v + s • A v‖ := by
      gcongr
      rw [norm_smul, Real.norm_eq_abs]
      calc
        _ ≤ |s| * (M * ‖v + s • A v‖) :=
          mul_le_mul_of_nonneg_left
            ((A.le_opNorm _).trans (mul_le_mul_of_nonneg_right hAM (norm_nonneg _)))
            (abs_nonneg _)
        _ ≤ M * ‖v + s • A v‖ :=
          (mul_le_mul_of_nonneg_right hs (mul_nonneg hM (norm_nonneg _))).trans_eq
            (one_mul _)
    _ = _ := by ring

theorem selected_center_near_cell {δ M K s : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    {G : Plane → Plane} {tag : Index → Plane} {i : Index} {b l : Plane}
    (hA : (fderiv ℝ G (tag i)).comp (fderiv ℝ G (tag i)) = 0)
    (hAM : ‖fderiv ℝ G (tag i)‖ ≤ M) (hs : |s| ≤ 1)
    (hrem : ‖G b - affineVelocity G tag i b‖ ≤ K * δ ^ 2)
    (hres : ‖b + s • G b - (l + s • affineVelocity G tag i l)‖ ≤ Real.sqrt 2 * δ ^ 2) :
    ‖l - b‖ ≤ collarRadius M K δ := by
  let A := fderiv ℝ G (tag i)
  have he : l - b + s • A (l - b) =
      -(b + s • G b - (l + s • affineVelocity G tag i l)) +
        s • (G b - affineVelocity G tag i b) := by
    simp only [affineVelocity, map_sub, A]
    module
  have hw : ‖l - b + s • A (l - b)‖ ≤ (Real.sqrt 2 + K) * δ ^ 2 := by
    rw [he]
    calc
      _ ≤ ‖-(b + s • G b - (l + s • affineVelocity G tag i l))‖ +
          ‖s • (G b - affineVelocity G tag i b)‖ := norm_add_le _ _
      _ ≤ Real.sqrt 2 * δ ^ 2 + K * δ ^ 2 := by
        rw [norm_neg, norm_smul, Real.norm_eq_abs]
        apply add_le_add hres
        exact (mul_le_mul_of_nonneg_left hrem (abs_nonneg s)).trans
          ((mul_le_mul_of_nonneg_right hs (mul_nonneg hK (pow_nonneg hδ.le 2))).trans_eq
            (one_mul _))
      _ = _ := by ring
  exact (nilpotent_inverse_norm_bound hA hM hAM hs (l - b)).trans
    ((mul_le_mul_of_nonneg_left hw (by linarith)).trans_eq (by unfold collarRadius; ring))

theorem construction_covers_of_bounds {δ M K : ℝ} (hδ : 0 < δ) (hM : 0 ≤ M) (hK : 0 ≤ K)
    {D : Set Plane} {G : Plane → Plane} {tag : Index → Plane}
    {Q : Index → Plane ≃ₗᵢ[ℝ] Plane}
    (hnil : ∀ p ∈ D, (fderiv ℝ G p).comp (fderiv ℝ G p) = 0)
    (hdata : ∀ i ∈ coarseIndices δ D, tag i ∈ cell δ i ∩ D ∧
      IsShearFrame (fderiv ℝ G (tag i)) (Q i) ∧ ‖fderiv ℝ G (tag i)‖ ≤ M ∧
      ∀ b ∈ cell δ i, ‖G b - affineVelocity G tag i b‖ ≤ K * δ ^ 2) :
    RuledApproximation.physicalRuled 1 D G 1 ⊆
      constructionCarrier δ (collarRadius M K δ) D G tag Q := by
  rintro z ⟨b, hbD, s, hs, rfl⟩
  obtain ⟨i, hbi⟩ := cell_cover hδ b
  have hi : i ∈ coarseIndices δ D := ⟨b, hbi, hbD⟩
  obtain ⟨htag, hframe, hAM, hrem⟩ := hdata i hi
  let A := fderiv ℝ G (tag i)
  let q := G (tag i) - A (tag i)
  obtain ⟨j, p, hp, hx, hres⟩ := sliding_rows_of_frame hframe q (sq_pos_of_pos hδ) s (b + s • G b)
  have hvel (l : Plane) : A l + q = affineVelocity G tag i l := by
    simp only [affineVelocity, q, A, map_sub]
    abel
  change b + s • G b = p + s • (A (fineCenter δ (Q i) j) + q) at hx
  change ‖b + s • G b - (fineCenter δ (Q i) j + s • (A (fineCenter δ (Q i) j) + q))‖ ≤
      Real.sqrt 2 * δ ^ 2 at hres
  rw [hvel] at hx hres
  have hnear := selected_center_near_cell hδ hM hK (hnil _ htag.2) hAM hs (hrem b hbi) hres
  have hretain : (i, j) ∈ retainedIndices δ (collarRadius M K δ) D Q := by
    refine ⟨hi, ?_⟩
    exact (Metric.infDist_le_dist_of_mem hbi).trans (by simpa only [dist_eq_norm] using hnear)
  apply mem_iUnion.mpr
  refine ⟨(i, j), mem_iUnion.mpr ⟨hretain, ?_⟩⟩
  refine ⟨s, p, hp, ?_⟩
  ext n
  fin_cases n
  · rfl
  · exact congrArg (fun w : Plane => w 0) hx
  · simpa [RuledApproximation.axial, RuledApproximation.vec3] using congrArg (fun w : Plane => w 1) hx

end CylinderCovering.NilpotentRate

end

end OAI
