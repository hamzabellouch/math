import OAI.Geometry.DoublingHilbert.Energy

namespace OAI

open MeasureTheory Set Filter
open scoped BigOperators Topology

open Metric

/-! Selected period crossings and finite-dimensional obstruction. -/

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace DoublingHilbert

/-- One full period, recording its integral horizontal and vertical origins. -/
structure ColorBlock (j : ℕ) where
  ax : ℤ
  ay : ℤ

namespace ColorBlock
variable {j : ℕ}

def rectangle (B : ColorBlock j) : Rectangle :=
  ⟨Segment.grid (B.ax * xPeriod j) (stripWidth j) (colors j)
      (stripWidth_pos j) (colors_pos j),
   Segment.grid (B.ay * yPeriod j) (scale j) (colors j)
      (scale_pos j) (colors_pos j)⟩

def column (B : ColorBlock j) (i : Fin (colors j)) : Segment :=
  Segment.cell (B.ax * xPeriod j) (stripWidth j) (stripWidth_pos j) i

def row (B : ColorBlock j) (i : Fin (colors j)) : Segment :=
  Segment.cell (B.ay * yPeriod j) (scale j) (scale_pos j) i

theorem column_subset (B : ColorBlock j) (i : Fin (colors j)) :
    Icc (B.column i).lo (B.column i).hi ⊆ Icc B.rectangle.x.lo B.rectangle.x.hi :=
  Segment.cell_subset_grid _ _ (stripWidth_pos j) (colors_pos j) i

theorem row_subset (B : ColorBlock j) (i : Fin (colors j)) :
    Icc (B.row i).lo (B.row i).hi ⊆ Icc B.rectangle.y.lo B.rectangle.y.hi :=
  Segment.cell_subset_grid _ _ (scale_pos j) (colors_pos j) i

theorem column_color (B : ColorBlock j) (i : Fin (colors j)) {x : ℝ}
    (hx : x ∈ Ioo (B.column i).lo (B.column i).hi) :
    stripColor (colors j) (colors_pos j) (stripWidth j) x = i ∧
      inColoredStrip (stripWidth j) (colors j) i x := by
  apply color_in_block _ _ (stripWidth_pos j) B.ax i
  simp only [column, Segment.cell, Nat.cast_add, Nat.cast_one, mem_Ioo] at hx
  dsimp [xPeriod] at hx
  constructor <;> nlinarith [hx.1, hx.2]

theorem row_color (B : ColorBlock j) (i : Fin (colors j)) {y : ℝ}
    (hy : y ∈ Ioo (B.row i).lo (B.row i).hi) :
    stripColor (colors j) (colors_pos j) (scale j) y = i ∧
      inColoredStrip (scale j) (colors j) i y := by
  apply color_in_block _ _ (scale_pos j) B.ay i
  simp only [row, Segment.cell, Nat.cast_add, Nat.cast_one, mem_Ioo] at hy
  dsimp [yPeriod] at hy
  constructor <;> nlinarith [hy.1, hy.2]

theorem x_length (B : ColorBlock j) :
    B.rectangle.x.length = (colors j : ℝ) * widthFactor j * scale j := by
  simp only [rectangle, Segment.grid_length, stripWidth]
  ring

theorem y_length (B : ColorBlock j) :
    B.rectangle.y.length = (colors j : ℝ) * scale j := by
  simp only [rectangle, Segment.grid_length]

theorem row_energy_le (B : ColorBlock j) (i : Fin (colors j))
    {g : Base → ℝ} (hg : IsBoundedField g) (hnonneg : ∀ p, 0 ≤ g p) :
    (∫ p, g p ∂(Rectangle.mk B.rectangle.x (B.row i)).law) ≤
      colors j * (∫ p, g p ∂B.rectangle.law) :=
  Rectangle.integral_row_le_mul_grid _ _ (scale_pos j) (colors_pos j) _ hg hnonneg i

theorem column_energy_le (B : ColorBlock j) (i : Fin (colors j))
    {g : Base → ℝ} (hg : IsBoundedField g) (hnonneg : ∀ p, 0 ≤ g p) :
    (∫ p, g p ∂(Rectangle.mk (B.column i) B.rectangle.y).law) ≤
      colors j * (∫ p, g p ∂B.rectangle.law) :=
  Rectangle.integral_column_le_mul_grid _ _ (stripWidth_pos j) (colors_pos j) _ hg hnonneg i

end ColorBlock

namespace PeriodGrid
variable {j : ℕ}

def colorBlock (G : PeriodGrid j) (a : Fin G.nx) (b : Fin G.ny) : ColorBlock j :=
  ⟨G.ax + a, G.ay + b⟩

theorem block_eq_colorBlock (G : PeriodGrid j) (a : Fin G.nx) (b : Fin G.ny) :
    G.block a b = (G.colorBlock a b).rectangle := by
  have hx := G.block_x a b
  have hy := G.block_y a b
  cases heq : G.block a b with
  | mk x y =>
    rw [heq] at hx hy
    simp only [Rectangle.mk.injEq, ColorBlock.rectangle, colorBlock]
    constructor
    · simpa only [Int.cast_add, Int.cast_natCast] using hx
    · simpa only [Int.cast_add, Int.cast_natCast] using hy

end PeriodGrid

section LineSelection
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Fubini selects a genuine interior horizontal line with an all-points oscillation bound. -/
theorem exists_horizontal_line (I J : Segment) {F G : Base → E} {C C' : NNReal}
    (hF : LipschitzWith C F) (hG : LipschitzWith C' G)
    {e : Base → ℝ} (he : IsBoundedField e) {c : ℝ} (hc : 0 ≤ c)
    (hdom : ∀ y ∈ Ioo J.lo J.hi, ∀ x : ℝ,
      c * ‖column G (1, 0) (x, y) - column F (1, 0) (x, y)‖ ^ 2 ≤ e (x, y)) :
    ∃ y ∈ Ioo J.lo J.hi, ∀ a ∈ Icc I.lo I.hi, ∀ b ∈ Icc I.lo I.hi,
      c * ‖(G (b, y) - F (b, y)) - (G (a, y) - F (a, y))‖ ^ 2 ≤
        I.length ^ 2 * (∫ p, e p ∂(Rectangle.mk I J).law) := by
  have hgood := J.ae_mem.and
    ((J.ae_of_ae (ae_integral_column_x hG)).and (J.ae_of_ae (ae_integral_column_x hF)))
  obtain ⟨y, ⟨hy, hGy, hFy⟩, hye⟩ :=
    exists_good_le_integral ((he.integral_fst I.law).integrable J.law) hgood
  refine ⟨y, hy, ?_⟩
  intro a ha b hb
  let g : ℝ → E := fun x => column G (1, 0) (x, y) - column F (1, 0) (x, y)
  have hg : IsBoundedField g :=
    ((boundedField_column hG (1, 0)).sub (boundedField_column hF (1, 0))).comp_measurable
      (measurable_id.prodMk measurable_const)
  have hFTC : ∀ a b, (∫ x in a..b, g x) =
      (G (b, y) - F (b, y)) - (G (a, y) - F (a, y)) := by
    intro a b
    dsimp [g]
    rw [intervalIntegral.integral_sub (intervalIntegrable_column_x hG _ y a b)
      (intervalIntegrable_column_x hF _ y a b), hGy, hFy]
    abel
  have hosc := oscillation_sq_le_segment_energy I hg hFTC ha hb
  have hline : c * (∫ x, ‖g x‖ ^ 2 ∂I.law) ≤ ∫ x, e (x, y) ∂I.law := by
    rw [← integral_const_mul]
    exact integral_mono ((hg.norm_sq.const_mul c).integrable I.law)
      ((he.comp_measurable (measurable_id.prodMk measurable_const)).integrable I.law)
      (fun x => hdom y hy x)
  have hbnd := mul_le_mul_of_nonneg_left hline (sq_nonneg I.length)
  have hbnd' := mul_le_mul_of_nonneg_left hye (sq_nonneg I.length)
  rw [← (Rectangle.mk I J).integral_eq_swap e (he.integrable _)] at hbnd'
  nlinarith [mul_le_mul_of_nonneg_left hosc hc]

/-- The independent vertical-line selection, with the same avoidance of FTC null sets. -/
theorem exists_vertical_line (I J : Segment) {F G : Base → E} {C C' : NNReal}
    (hF : LipschitzWith C F) (hG : LipschitzWith C' G)
    {e : Base → ℝ} (he : IsBoundedField e) {c : ℝ} (hc : 0 ≤ c)
    (hdom : ∀ x ∈ Ioo I.lo I.hi, ∀ y : ℝ,
      c * ‖column G (0, 1) (x, y) - column F (0, 1) (x, y)‖ ^ 2 ≤ e (x, y)) :
    ∃ x ∈ Ioo I.lo I.hi, ∀ a ∈ Icc J.lo J.hi, ∀ b ∈ Icc J.lo J.hi,
      c * ‖(G (x, b) - F (x, b)) - (G (x, a) - F (x, a))‖ ^ 2 ≤
        J.length ^ 2 * (∫ p, e p ∂(Rectangle.mk I J).law) := by
  have hgood := I.ae_mem.and
    ((I.ae_of_ae (ae_integral_column_y hG)).and (I.ae_of_ae (ae_integral_column_y hF)))
  obtain ⟨x, ⟨hx, hGx, hFx⟩, hxe⟩ :=
    exists_good_le_integral ((he.integral_snd J.law).integrable I.law) hgood
  refine ⟨x, hx, ?_⟩
  intro a ha b hb
  let g : ℝ → E := fun y => column G (0, 1) (x, y) - column F (0, 1) (x, y)
  have hg : IsBoundedField g :=
    ((boundedField_column hG (0, 1)).sub (boundedField_column hF (0, 1))).comp_measurable
      (measurable_const.prodMk measurable_id)
  have hFTC : ∀ a b, (∫ y in a..b, g y) =
      (G (x, b) - F (x, b)) - (G (x, a) - F (x, a)) := by
    intro a b
    dsimp [g]
    rw [intervalIntegral.integral_sub (intervalIntegrable_column_y hG _ x a b)
      (intervalIntegrable_column_y hF _ x a b), hGx, hFx]
    abel
  have hosc := oscillation_sq_le_segment_energy J hg hFTC ha hb
  have hline : c * (∫ y, ‖g y‖ ^ 2 ∂J.law) ≤ ∫ y, e (x, y) ∂J.law := by
    rw [← integral_const_mul]
    exact integral_mono ((hg.norm_sq.const_mul c).integrable J.law)
      ((he.comp_measurable (measurable_const.prodMk measurable_id)).integrable J.law)
      (fun y => hdom x hx y)
  have hbnd := mul_le_mul_of_nonneg_left hline (sq_nonneg J.length)
  have hbnd' := mul_le_mul_of_nonneg_left hxe (sq_nonneg J.length)
  rw [← (Rectangle.mk I J).integral_eq e (he.integrable _)] at hbnd'
  nlinarith [mul_le_mul_of_nonneg_left hosc hc]

end LineSelection
end DoublingHilbert

namespace DoublingHilbert
section BlockSelection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Finite averaging chooses one complete period without increasing the mean energy. -/
theorem exists_small_energy_block {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (N : ℕ) (hN : 0 < N) {η : ℝ} (hη : 0 < η) :
    ∃ (w : Tuple) (j : ℕ) (B : ColorBlock j), colors j = N ∧ w j = 0 ∧
      B.rectangle.closed ⊆ sheetDomain w ∧
      (∫ p, combinedEnergy hf w j p ∂B.rectangle.law) < η := by
  obtain ⟨w, j, G, hjN, hjw, hQ, hE⟩ := exists_small_energy_grid hf N hN hη
  obtain ⟨a, b, hab⟩ := G.exists_block_integral_le (bounded_combinedEnergy hf w j)
  refine ⟨w, j, G.colorBlock a b, hjN, hjw, ?_, ?_⟩
  · rw [← G.block_eq_colorBlock a b]
    exact (G.block_subset a b).trans hQ
  · rw [← G.block_eq_colorBlock a b]
    exact hab.trans_lt hE

/-- Every color has a selected horizontal line; the anisotropic weight is retained. -/
theorem exists_color_row {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (B : ColorBlock j)
    (i : Fin (colors j)) :
    ∃ y ∈ Ioo (B.row i).lo (B.row i).hi,
      ∀ a ∈ Icc B.rectangle.x.lo B.rectangle.x.hi,
      ∀ b ∈ Icc B.rectangle.x.lo B.rectangle.x.hi,
      (widthFactor j : ℝ) ^ 2 *
        ‖(addedSheet hf w j i (b, y) - globalSheet hf w (b, y)) -
          (addedSheet hf w j i (a, y) - globalSheet hf w (a, y))‖ ^ 2 ≤
        B.rectangle.x.length ^ 2 *
          (colors j * (∫ p, combinedEnergy hf w j p ∂B.rectangle.law)) := by
  obtain ⟨C, hF⟩ := globalSheet_lipschitz hf w
  obtain ⟨C', hG⟩ := globalSheet_lipschitz hf (w.update j ((i : ℕ) + 1))
  have hdom : ∀ y ∈ Ioo (B.row i).lo (B.row i).hi, ∀ x : ℝ,
      (widthFactor j : ℝ) ^ 2 *
        ‖column (addedSheet hf w j i) (1, 0) (x, y) -
          column (globalSheet hf w) (1, 0) (x, y)‖ ^ 2 ≤ combinedEnergy hf w j (x, y) := by
    intro y hy x
    unfold combinedEnergy horizontalEnergy horizontalColumn
    rw [(B.row_color i hy).1]
    exact le_add_of_nonneg_right (sq_nonneg _)
  obtain ⟨y, hy, hosc⟩ := exists_horizontal_line B.rectangle.x (B.row i) hF hG
    (bounded_combinedEnergy hf w j) (sq_nonneg (widthFactor j : ℝ)) hdom
  refine ⟨y, hy, fun a ha b hb => (hosc a ha b hb).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (B.row_energy_le i (bounded_combinedEnergy hf w j) (combinedEnergy_nonneg hf w j))
    (sq_nonneg _)

/-- Independently select an interior vertical line for each color. -/
theorem exists_color_column {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (w : Tuple) (j : ℕ) (B : ColorBlock j)
    (i : Fin (colors j)) :
    ∃ x ∈ Ioo (B.column i).lo (B.column i).hi,
      ∀ a ∈ Icc B.rectangle.y.lo B.rectangle.y.hi,
      ∀ b ∈ Icc B.rectangle.y.lo B.rectangle.y.hi,
        ‖(addedSheet hf w j i (x, b) - globalSheet hf w (x, b)) -
          (addedSheet hf w j i (x, a) - globalSheet hf w (x, a))‖ ^ 2 ≤
        B.rectangle.y.length ^ 2 *
          (colors j * (∫ p, combinedEnergy hf w j p ∂B.rectangle.law)) := by
  obtain ⟨C, hF⟩ := globalSheet_lipschitz hf w
  obtain ⟨C', hG⟩ := globalSheet_lipschitz hf (w.update j ((i : ℕ) + 1))
  have hdom : ∀ x ∈ Ioo (B.column i).lo (B.column i).hi, ∀ y : ℝ,
      1 * ‖column (addedSheet hf w j i) (0, 1) (x, y) -
          column (globalSheet hf w) (0, 1) (x, y)‖ ^ 2 ≤ combinedEnergy hf w j (x, y) := by
    intro x hx y
    unfold combinedEnergy verticalEnergy verticalColumn
    rw [(B.column_color i hx).1, one_mul]
    exact le_add_of_nonneg_left (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  obtain ⟨x, hx, hosc⟩ := exists_vertical_line (B.column i) B.rectangle.y hF hG
    (bounded_combinedEnergy hf w j) (by norm_num : (0 : ℝ) ≤ 1) hdom
  simp only [one_mul] at hosc
  refine ⟨x, hx, fun a ha b hb => (hosc a ha b hb).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (B.column_energy_le i (bounded_combinedEnergy hf w j) (combinedEnergy_nonneg hf w j))
    (sq_nonneg _)

end BlockSelection
end DoublingHilbert

namespace DoublingHilbert

/-- The horizontal weight cancels exactly against the longer period side. -/
theorem small_oscillation_of_weighted_energy {n w r s e : ℝ}
    (hn : 0 < n) (hw : 0 < w) (hr : 0 < r) (hs : 0 ≤ s)
    (he : e ≤ 1 / (64 * n ^ 3))
    (hbound : w ^ 2 * s ^ 2 ≤ (n * w * r) ^ 2 * (n * e)) : s ≤ r / 8 := by
  have hright := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left he hn.le) (sq_nonneg (n * w * r))
  have heq : (n * w * r) ^ 2 * (n * (1 / (64 * n ^ 3))) = w ^ 2 * (r / 8) ^ 2 := by
    field_simp
    ring
  rw [heq] at hright
  have hsquared := (mul_le_mul_iff_right₀ (sq_pos_of_pos hw)).mp (hbound.trans hright)
  exact (sq_le_sq₀ hs (by positivity)).mp hsquared

section CrossingPacking
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Crossings of the selected lines force arbitrarily large separated families
in the fixed radius-D target ball. The lower bound is the genuine source distance. -/
theorem exists_separated_family {f : constructedSet → E} {D : NNReal}
    (hf : LipschitzWith D f) (hlower : ∀ p q, dist p q ≤ dist (f p) (f q))
    (N : ℕ) (hN : 0 < N) :
    ∃ z : Fin N → E, (∀ i, ‖z i‖ ≤ D) ∧
      ∀ i m, i ≠ m → 1 ≤ dist (z i) (z m) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨w, j, B, hjN, hjw, hB, henergy⟩ := exists_small_energy_block hf N hN
    (show 0 < 1 / (64 * (N : ℝ) ^ 3) by positivity)
  subst N
  choose y hy hyo using fun i => exists_color_row hf w j B i
  choose x hx hxo using fun i => exists_color_column hf w j B i
  have hxc (i) : x i ∈ Icc B.rectangle.x.lo B.rectangle.x.hi :=
    B.column_subset i ⟨(hx i).1.le, (hx i).2.le⟩
  have hyc (i) : y i ∈ Icc B.rectangle.y.lo B.rectangle.y.hi :=
    B.row_subset i ⟨(hy i).1.le, (hy i).2.le⟩
  let h (i : Fin (colors j)) (p : Base) := addedSheet hf w j i p - globalSheet hf w p
  let p (i : Fin (colors j)) : Base := (x i, y i)
  have hr := scale_pos j
  have hWR : (0 : ℝ) < widthFactor j := by exact_mod_cast widthFactor_pos j
  have hrow (i m : Fin (colors j)) :
      ‖h i (x m, y i) - h i (p i)‖ ≤ scale j / 8 := by
    apply small_oscillation_of_weighted_energy hNR hWR hr (norm_nonneg _) henergy.le
    have ho := hyo i (x i) (hxc i) (x m) (hxc m)
    rw [B.x_length] at ho
    exact ho
  have hcolumn (i m : Fin (colors j)) :
      ‖h m (x m, y i) - h m (p m)‖ ≤ scale j / 8 := by
    apply small_oscillation_of_weighted_energy (w := 1) hNR zero_lt_one hr
      (norm_nonneg _) henergy.le
    have ho := hxo m (y m) (hyc m) (y i) (hyc i)
    rw [B.y_length] at ho
    simpa only [one_pow, one_mul, mul_one] using ho
  have hcentral (i m : Fin (colors j)) (him : i ≠ m) :
      scale j ≤ ‖h i (p i) - h m (p m)‖ := by
    let c : Base := (x m, y i)
    have hiAllowed : allowed j i c := Or.inl (B.row_color i (hy i)).2
    have hmAllowed : allowed j m c := Or.inr (B.column_color m (hx m)).2
    have hsep := globalSheet_separation_sq hf hlower w j hjw
      (show (i : ℕ) ≠ (m : ℕ) from fun heq => him (Fin.ext heq))
      i.isLt m.isLt (hB ⟨hxc m, hyc i⟩) hiAllowed hmAllowed
    have hdiff : h i c - h m c = addedSheet hf w j i c - addedSheet hf w j m c := by
      dsimp [h]
      abel
    change 2 * scale j ^ 2 ≤ ‖addedSheet hf w j i c - addedSheet hf w j m c‖ ^ 2 at hsep
    rw [← hdiff] at hsep
    have ht₁ := dist_triangle (h i c) (h i (p i)) (h m c)
    have ht₂ := dist_triangle (h i (p i)) (h m (p m)) (h m c)
    simp only [dist_eq_norm] at ht₁ ht₂
    have hv := hcolumn i m
    have hv' : ‖h m (p m) - h m c‖ ≤ scale j / 8 := by
      simpa only [c, norm_sub_rev] using hv
    have hh := hrow i m
    change ‖h i c - h i (p i)‖ ≤ scale j / 8 at hh
    by_contra hn
    have hm : ‖h i (p i) - h m (p m)‖ < scale j := lt_of_not_ge hn
    have hbound : ‖h i c - h m c‖ ≤ 5 * scale j / 4 := by linarith
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hbound 2
    nlinarith [sq_pos_of_pos hr]
  let z (i : Fin (colors j)) : E := (scale j)⁻¹ • h i (p i)
  refine ⟨z, ?_, ?_⟩
  · intro i
    have hoff := globalSheet_offset hf w j hjw i.isLt (p := p i) (hB ⟨hxc i, hyc i⟩)
      (Or.inl (B.row_color i (hy i)).2)
    change ‖h i (p i)‖ ≤ D * scale j at hoff
    dsimp [z]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    calc
      _ ≤ (scale j)⁻¹ * (D * scale j) := mul_le_mul_of_nonneg_left hoff (inv_nonneg.mpr hr.le)
      _ = D := by field_simp
  · intro i m him
    rw [dist_eq_norm]
    dsimp [z]
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    calc
      1 = (scale j)⁻¹ * scale j := (inv_mul_cancel₀ hr.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcentral i m him) (inv_nonneg.mpr hr.le)

end CrossingPacking
end DoublingHilbert

end

end OAI
