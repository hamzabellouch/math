import OAI.Probability.SLE.Gauge.SerpentinePieces
import OAI.Probability.SLE.Gauge.SerpentineStepCount

namespace OAI

/-! Explicit arclength parametrization of the finite serpentine array,
continued vertically along its last column. -/

noncomputable section
open Set Metric
open scoped NNReal

namespace SLEExactGauge.Serpentine

lemma columnEntry_succ (A : ℝ) (m j : ℕ) :
    columnEntry A m (j + 1) = columnEntry A m j + 200 * m + 50 * Real.pi := by
  simp only [columnEntry, Nat.cast_add, Nat.cast_one]
  ring

def arraySpine (m : ℕ) : ℕ → ℝ → ℂ
  | 0 => straightPiece m 0
  | j + 1 => curveJoin (columnEntry 0 m (j + 1))
      (curveJoin (columnEntry 0 m j + 200 * m) (arraySpine m j)
        (fun t => circularPiece m j (t - (columnEntry 0 m j + 200 * m))))
      (fun t => straightPiece m (j + 1) (t - columnEntry 0 m (j + 1)))

def arrayTangent (m : ℕ) : ℕ → ℝ → ℂ
  | 0 => fun _ => straightTangent 0
  | j + 1 => curveJoin (columnEntry 0 m (j + 1))
      (curveJoin (columnEntry 0 m j + 200 * m) (arrayTangent m j)
        (fun t => circularTangent j (t - (columnEntry 0 m j + 200 * m))))
      (fun _ => straightTangent (j + 1))

lemma arraySpine_tail (m j : ℕ) {t : ℝ} (ht : columnEntry 0 m j ≤ t) :
    arraySpine m j t = straightPiece m j (t - columnEntry 0 m j) := by
  cases j with
  | zero => simp [arraySpine, columnEntry]
  | succ j =>
    by_cases hlt : columnEntry 0 m (j + 1) < t
    · simp only [arraySpine, curveJoin_of_gt hlt]
    · have he : t = columnEntry 0 m (j + 1) := le_antisymm (le_of_not_gt hlt) ht
      subst t
      have hcut : columnEntry 0 m j + 200 * m < columnEntry 0 m (j + 1) := by
        rw [columnEntry_succ]
        linarith [Real.pi_pos]
      simp only [arraySpine, curveJoin_of_le le_rfl, curveJoin_of_gt hcut, sub_self]
      rw [columnEntry_succ]
      have he : columnEntry 0 m j + 200 * m + 50 * Real.pi -
          (columnEntry 0 m j + 200 * m) = 50 * Real.pi := by ring
      rw [he, circular_straight_position_match]

lemma arrayTangent_tail (m j : ℕ) {t : ℝ} (ht : columnEntry 0 m j ≤ t) :
    arrayTangent m j t = straightTangent j := by
  cases j with
  | zero => rfl
  | succ j =>
    by_cases hlt : columnEntry 0 m (j + 1) < t
    · simp only [arrayTangent, curveJoin_of_gt hlt]
    · have he : t = columnEntry 0 m (j + 1) := le_antisymm (le_of_not_gt hlt) ht
      subst t
      have hcut : columnEntry 0 m j + 200 * m < columnEntry 0 m (j + 1) := by
        rw [columnEntry_succ]
        linarith [Real.pi_pos]
      simp only [arrayTangent, curveJoin_of_le le_rfl, curveJoin_of_gt hcut]
      rw [columnEntry_succ]
      have he : columnEntry 0 m j + 200 * m + 50 * Real.pi -
          (columnEntry 0 m j + 200 * m) = 50 * Real.pi := by ring
      rw [he, circular_straight_tangent_match]

lemma arrayTangent_norm (m j : ℕ) (t : ℝ) : ‖arrayTangent m j t‖ = 1 := by
  induction j with
  | zero => exact straightTangent_norm 0
  | succ j ih =>
    unfold arrayTangent curveJoin
    split
    · split
      · exact ih
      · exact circularTangent_norm _ _
    · exact straightTangent_norm _

lemma arraySpine_hasDerivAt (m j : ℕ) (t : ℝ) :
    HasDerivAt (arraySpine m j) (arrayTangent m j t) t := by
  induction j generalizing t with
  | zero => exact straightPiece_hasDerivAt m 0 t
  | succ j ih =>
    let a := columnEntry 0 m j + 200 * m
    let b := columnEntry 0 m (j + 1)
    have hc (t : ℝ) : HasDerivAt (fun t => circularPiece m j (t - a))
        (circularTangent j (t - a)) t := by
      convert (circularPiece_hasDerivAt m j (t - a)).scomp t
        ((hasDerivAt_id t).sub_const a) using 1 <;> first | rfl | simp only [one_smul]
    have hs (t : ℝ) : HasDerivAt (fun t => straightPiece m (j + 1) (t - b))
        (straightTangent (j + 1)) t := by
      convert (straightPiece_hasDerivAt m (j + 1) (t - b)).scomp t
        ((hasDerivAt_id t).sub_const b) using 1 <;> first | rfl | simp only [one_smul]
    have ha0 : columnEntry 0 m j ≤ a := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) m]
    have hab : a < b := by dsimp [a, b]; rw [columnEntry_succ]; linarith [Real.pi_pos]
    have habv : b - a = 50 * Real.pi := by dsimp [a, b]; rw [columnEntry_succ]; ring
    have he₁ : arraySpine m j a = circularPiece m j (a - a) := by
      rw [arraySpine_tail m j ha0]
      have he : a - columnEntry 0 m j = 200 * m := by dsimp [a]; ring
      rw [he, sub_self, straight_circular_position_match]
    have hd₁ : arrayTangent m j a = circularTangent j (a - a) := by
      rw [arrayTangent_tail m j ha0, sub_self, straight_circular_tangent_match]
    have hfirst := curveJoin_hasDerivAt a (arraySpine m j)
      (fun t => circularPiece m j (t - a)) (arrayTangent m j)
      (fun t => circularTangent j (t - a)) ih hc he₁ hd₁
    have he₂ : curveJoin a (arraySpine m j) (fun t => circularPiece m j (t - a)) b =
        straightPiece m (j + 1) (b - b) := by
      rw [curveJoin_of_gt hab, habv, sub_self, circular_straight_position_match]
    have hd₂ : curveJoin a (arrayTangent m j) (fun t => circularTangent j (t - a)) b =
        straightTangent (j + 1) := by
      rw [curveJoin_of_gt hab, habv, circular_straight_tangent_match]
    exact curveJoin_hasDerivAt b _ _ _ _ hfirst hs he₂ hd₂ t

lemma arrayTangent_lipschitz (m j : ℕ) : LipschitzWith (1 / 50) (arrayTangent m j) := by
  induction j with
  | zero => exact (LipschitzWith.const _).weaken (by norm_num)
  | succ j ih =>
    let a := columnEntry 0 m j + 200 * m
    let b := columnEntry 0 m (j + 1)
    have hc : LipschitzWith (1 / 50) (fun t => circularTangent j (t - a)) := by
      apply lipschitzWith_iff_dist_le_mul.mpr
      intro u v
      simpa only [dist_sub_right] using (circularTangent_lipschitz j).dist_le_mul (u - a) (v - a)
    have hs : LipschitzWith (1 / 50) (fun _ : ℝ => straightTangent (j + 1)) :=
      (LipschitzWith.const _).weaken (by norm_num)
    have ha0 : columnEntry 0 m j ≤ a := by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) m]
    have hab : a < b := by dsimp [a, b]; rw [columnEntry_succ]; linarith [Real.pi_pos]
    have habv : b - a = 50 * Real.pi := by dsimp [a, b]; rw [columnEntry_succ]; ring
    have hd₁ : arrayTangent m j a = circularTangent j (a - a) := by
      rw [arrayTangent_tail m j ha0, sub_self, straight_circular_tangent_match]
    have hfirst := curveJoin_lipschitz ih hc hd₁
    have hd₂ : curveJoin a (arrayTangent m j) (fun t => circularTangent j (t - a)) b =
        straightTangent (j + 1) := by
      rw [curveJoin_of_gt hab, habv, circular_straight_tangent_match]
    exact curveJoin_lipschitz hfirst hs hd₂

/-- Every length-four normal coordinate patch of the explicit array has
uniform upper and inverse Lipschitz constants equal to two. -/
theorem array_normal_patch_bounds (m j : ℕ) (k : ℝ) :
    LipschitzOnWith 2 (normalRibbon (arraySpine m j) (arrayTangent m j))
      (RibbonCoordinates.ribbonStepPatch k) ∧
    ∀ z ∈ RibbonCoordinates.ribbonStepPatch k,
      ∀ w ∈ RibbonCoordinates.ribbonStepPatch k,
        dist z w ≤ 2 * dist (normalRibbon (arraySpine m j) (arrayTangent m j) z)
          (normalRibbon (arraySpine m j) (arrayTangent m j) w) := by
  have hbound z (hz : z ∈ RibbonCoordinates.ribbonStepPatch k)
      w (hw : w ∈ RibbonCoordinates.ribbonStepPatch k) :=
    normalRibbon_patch_bounds (arraySpine m j) (arrayTangent m j) (k - 1) (k + 3)
      (by ring_nf; norm_num)
      (fun t _ => (arraySpine_hasDerivAt m j t).hasDerivWithinAt)
      (fun t _ => arrayTangent_norm m j t) (arrayTangent_lipschitz m j).lipschitzOnWith
      z w ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩ ⟨⟨hw.1, hw.2.1⟩, hw.2.2⟩
  exact ⟨lipschitzOnWith_iff_dist_le_mul.mpr (fun z hz w hw => (hbound z hz w hw).1),
    fun z hz w hw => (hbound z hz w hw).2⟩


end SLEExactGauge.Serpentine

end

end OAI
