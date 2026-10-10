import OAI.MeasureTheory.Falconer.Incidence.RoundedRowPencils

namespace OAI

/-! Normalize the rounded product rows into the bounded line chart without
changing their first coordinate. All size losses are explicit. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def verticalQuarter (p : Space 2) : Space 2 := rowPoint (p 0) (p 1/4)
noncomputable def verticalFour (p : Space 2) : Space 2 := rowPoint (p 0) (4*p 1)

@[simp] theorem verticalQuarter_zero (p : Space 2) : verticalQuarter p 0 = p 0 := rfl
@[simp] theorem verticalQuarter_one (p : Space 2) : verticalQuarter p 1 = p 1/4 := rfl

theorem verticalFour_verticalQuarter (p : Space 2) : verticalFour (verticalQuarter p) = p := by
  ext i
  fin_cases i
  · rfl
  · change 4*(p 1/4) = p 1
    ring

theorem verticalQuarter_verticalFour (p : Space 2) : verticalQuarter (verticalFour p) = p := by
  ext i
  fin_cases i
  · rfl
  · change (4*p 1)/4 = p 1
    ring

theorem verticalQuarter_injective : Function.Injective verticalQuarter :=
  Function.LeftInverse.injective verticalFour_verticalQuarter

theorem verticalQuarter_row_distance {p q : Space 2} (h : p 0 = q 0) :
    dist (verticalQuarter p) (verticalQuarter q) = dist p q/4 := by
  have hp : p = rowPoint (p 0) (p 1) := by ext i; fin_cases i <;> rfl
  have hq : q = rowPoint (p 0) (q 1) := by
    ext i
    fin_cases i
    · exact h.symm
    · rfl
  conv_rhs => rw [hp,hq,rowPoint_dist]
  change dist (rowPoint (p 0) (p 1/4)) (rowPoint (q 0) (q 1/4)) = _
  rw [← h,rowPoint_dist,← sub_div,abs_div]
  norm_num

theorem verticalQuarter_row_separated {δ y : ℝ} (P : Finset (Space 2))
    (hrow : ∀ p ∈ P, p 0 = y) (hsep : FiniteSeparatedAt δ P) :
    FiniteSeparatedAt (δ/4) (P.image verticalQuarter) := by
  intro p hp q hq hpq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hq
  rw [verticalQuarter_row_distance ((hrow x hx).trans (hrow z hz).symm)]
  exact div_le_div_of_nonneg_right
    (hsep x hx z hz (fun h => hpq (congrArg _ h))) (by norm_num)

theorem verticalQuarter_row_regular {δ s K y : ℝ} (hδ : 0 < δ)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (P : Finset (Space 2))
    (hrow : ∀ p ∈ P, p 0 = y) (hreg : NormalizedFiniteBallBound δ s K P) :
    NormalizedFiniteBallBound (δ/4) s (K*(4:ℝ)^s) (P.image verticalQuarter) := by
  intro z r hr _
  have hr0 : 0 < r := (by linarith : 0 < δ/4).trans_le hr
  have hsub : (P.image verticalQuarter).filter (fun p => dist p z ≤ r) ⊆
      (P.filter (fun p => dist p (rowPoint y (4*z 1)) ≤ 4*r)).image verticalQuarter := by
    intro p hp
    obtain ⟨hp,hpr⟩ := Finset.mem_filter.mp hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩,rfl⟩
    rw [row_dist_projection (hrow x hx)]
    have hh : |x 1/4-z 1| ≤ r :=
      (show |x 1/4-z 1| ≤ dist (verticalQuarter x) z by
        simpa only [Real.dist_eq,verticalQuarter_one] using PiLp.dist_apply_le (verticalQuarter x) z 1).trans hpr
    have he : |x 1-4*z 1| = 4*|x 1/4-z 1| := by
      rw [← abs_of_pos (by norm_num : (0:ℝ) < 4),← abs_mul]
      congr 1
      ring
    rw [he]
    linarith only [hh]
  have hc : (((P.image verticalQuarter).filter (fun p => dist p z ≤ r)).card:ℝ) ≤
      ((P.filter (fun p => dist p (rowPoint y (4*z 1)) ≤ 4*r)).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Finset.card_image_of_injective _ verticalQuarter_injective]
  calc
    _ ≤ ((P.filter (fun p => dist p (rowPoint y (4*z 1)) ≤ 4*r)).card:ℝ) := hc
    _ ≤ K*(4*r)^s*(P.card:ℝ) :=
      normalized_ball_bound_all_radii hs hK hreg _ _ (by linarith only [hr])
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hr0.le]; ring

theorem quarter_adjusted_incident {δ : ℝ} (hδ : 0 < δ) (p l : Space 2) :
    TubeIncident (δ/4) (verticalQuarter p) (planarQuarter (rowAdjustedLine δ p l)) := by
  have hd : 1 ≤ Real.sqrt (1+(planarQuarter (rowAdjustedLine δ p l) 0)^2) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).2
    nlinarith only [sq_nonneg (planarQuarter (rowAdjustedLine δ p l) 0)]
  have he : verticalQuarter p 1-planarQuarter (rowAdjustedLine δ p l) 0*verticalQuarter p 0-
      planarQuarter (rowAdjustedLine δ p l) 1 =
      (p 1-rowAdjustedLine δ p l 0*p 0-rowAdjustedLine δ p l 1)/4 := by
    simp only [verticalQuarter_zero,verticalQuarter_one,planarQuarter_apply]
    ring
  unfold TubeIncident
  rw [he,abs_div]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 4)]
  apply (div_le_iff₀ (zero_lt_one.trans_le hd)).2
  exact (div_le_div_of_nonneg_right (rowAdjustedLine_residual hδ p l) (by norm_num)).trans
    (le_mul_of_one_le_right (by positivity) hd)

theorem quarter_adjusted_chart {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1/8)
    (p l : Space 2) (hp : |p 0| ≤ 1) (hl : |l 0| ≤ 1 ∧ |l 1| ≤ 1)
    (hi : TubeIncident (3*δ) p l) :
    |planarQuarter (rowAdjustedLine δ p l) 0| ≤ 1 ∧
    |planarQuarter (rowAdjustedLine δ p l) 1| ≤ 1 := by
  obtain ⟨h0,h1⟩ := rowAdjustedLine_coordinate_error hδ p l hp hl.1 hi
  have h0' : |rowAdjustedLine δ p l 0| ≤ |l 0|+δ := by
    have hh := abs_sub_le (rowAdjustedLine δ p l 0) (l 0) 0
    simp only [sub_zero] at hh
    rw [abs_sub_comm (rowAdjustedLine δ p l 0) (l 0)] at hh
    linarith only [hh,h0]
  have h1' : |rowAdjustedLine δ p l 1| ≤ |l 1|+8*δ := by
    have hh := abs_sub_le (rowAdjustedLine δ p l 1) (l 1) 0
    simp only [sub_zero] at hh
    rw [abs_sub_comm (rowAdjustedLine δ p l 1) (l 1)] at hh
    linarith only [hh,h1]
  simp only [planarQuarter_apply,abs_div,abs_of_pos (by norm_num : (0:ℝ) < 4)]
  constructor <;> linarith only [h0',h1',hl.1,hl.2,hδsmall]

end Falconer

end OAI
