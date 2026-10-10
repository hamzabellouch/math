import Mathlib
import OAI.Geometry.RecorderBoxes.Affine
import OAI.Analysis.RecorderRadix.Scales

namespace OAI

/-! Rectangle widths, chart bounds and centered affine displacement estimates. -/

namespace Solenoidal
namespace Bridge
variable {M : Machine}
noncomputable def Rectangle.center (P : Rectangle) : ℝ × ℝ :=
  ((P.lower.1 + P.upper.1) / 2, (P.lower.2 + P.upper.2) / 2)

noncomputable def Rectangle.halfWidth (P : Rectangle) : ℝ × ℝ :=
  ((P.upper.1 - P.lower.1) / 2, (P.upper.2 - P.lower.2) / 2)

def Rectangle.PositiveSides (P : Rectangle) : Prop :=
  P.lower.1 < P.upper.1 ∧ P.lower.2 < P.upper.2

theorem source_positive {m : ℕ} (a l : Fin (m + 1)) :
    (sourceBox a l).PositiveSides :=
  ⟨Radix.prefix_strictMono l (by norm_num), Radix.prefix_strictMono a (by norm_num)⟩

theorem target_positive {m : ℕ} (b l : Fin (m + 1)) (d : Move) :
    (targetBox b l d).PositiveSides := by
  cases d with
  | stay => exact source_positive b l
  | left => exact ⟨by norm_num [targetBox],
      Radix.prefix_strictMono l (Radix.prefix_strictMono b (by norm_num))⟩
  | right => exact ⟨Radix.prefix_strictMono b (Radix.prefix_strictMono l (by norm_num)),
      by norm_num [targetBox]⟩

theorem physical_sides_positive (s : Recorder.Control M) {P : Rectangle}
    (hp : P.PositiveSides) : (physicalBox s P).PositiveSides := by
  have hx := mul_lt_mul_of_pos_left hp.1 (kappa_pos M)
  have hy := mul_lt_mul_of_pos_left hp.2 (kappa_pos M)
  constructor <;> dsimp [physicalBox, place] <;> linarith

theorem physical_halfWidth_le (s : Recorder.Control M) {P : Rectangle} (hp : P.InUnit) :
    (physicalBox s P).halfWidth.1 ≤ kappa M / 2 ∧
      (physicalBox s P).halfWidth.2 ≤ kappa M / 2 := by
  have hx : P.upper.1 - P.lower.1 ≤ 1 := by linarith [hp.1, hp.2.2.1]
  have hy : P.upper.2 - P.lower.2 ≤ 1 := by linarith [hp.2.2.2.1, hp.2.2.2.2.2]
  have hx' := mul_le_mul_of_nonneg_left hx (kappa_pos M).le
  have hy' := mul_le_mul_of_nonneg_left hy (kappa_pos M).le
  constructor <;> dsimp [Rectangle.halfWidth, physicalBox, place] <;> nlinarith

 
theorem rectangle_widths {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1)) (i : Branch M) :
    (sourceRectangle e i).PositiveSides ∧ (targetRectangle e i).PositiveSides ∧
    (sourceRectangle e i).halfWidth.1 ≤ kappa M / 2 ∧
    (sourceRectangle e i).halfWidth.2 ≤ kappa M / 2 ∧
    (targetRectangle e i).halfWidth.1 ≤ kappa M / 2 ∧
    (targetRectangle e i).halfWidth.2 ≤ kappa M / 2 := by
  have hs := physical_halfWidth_le i.src (source_in_unit (e i.read) (e i.left))
  have ht := physical_halfWidth_le i.dst (target_in_unit (e i.written) (e i.left) i.move)
  exact ⟨physical_sides_positive i.src (source_positive _ _),
    physical_sides_positive i.dst (target_positive _ _ _), hs.1, hs.2, ht.1, ht.2⟩

 
theorem Rectangle.offset_bound {P : Rectangle} {p : ℝ × ℝ} (hp : p ∈ P.carrier) :
    |p.1 - P.center.1| ≤ P.halfWidth.1 ∧
      |p.2 - P.center.2| ≤ P.halfWidth.2 := by
  constructor <;> apply abs_le.mpr <;> dsimp [Rectangle.center, Rectangle.halfWidth] <;>
    constructor <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]

theorem Rectangle.center_in_unit {P : Rectangle} (hp : P.InUnit) :
    0 ≤ P.center.1 ∧ P.center.1 ≤ 1 ∧ 0 ≤ P.center.2 ∧ P.center.2 ≤ 1 := by
  dsimp only [Rectangle.center]
  constructor
  · linarith [hp.1, hp.2.1]
  constructor
  · linarith [hp.2.1, hp.2.2.1]
  constructor <;> linarith [hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2]

theorem physical_center (s : Recorder.Control M) (P : Rectangle) :
    (physicalBox s P).center = place s P.center := by
  apply Prod.ext <;> dsimp [Rectangle.center, physicalBox, place] <;> ring

theorem physical_center_bounds (s : Recorder.Control M) {P : Rectangle} (hp : P.InUnit) :
    origin s ≤ (physicalBox s P).center.1 ∧
    (physicalBox s P).center.1 ≤ origin s + kappa M ∧
    (3 / 8 : ℝ) ≤ (physicalBox s P).center.2 ∧
    (physicalBox s P).center.2 ≤ 3 / 8 + kappa M := by
  have hm := Rectangle.center_in_unit hp
  rw [physical_center]
  have hx₀ := mul_nonneg (kappa_pos M).le hm.1
  have hx₁ := mul_le_mul_of_nonneg_left hm.2.1 (kappa_pos M).le
  have hy₀ := mul_nonneg (kappa_pos M).le hm.2.2.1
  have hy₁ := mul_le_mul_of_nonneg_left hm.2.2.2 (kappa_pos M).le
  dsimp only [place]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

 
noncomputable def centerRegion : Rectangle := ⟨(1 / 8, 3 / 8), (13 / 16, 7 / 16)⟩

theorem physical_center_mem_region (s : Recorder.Control M) {P : Rectangle}
    (hp : P.InUnit) : (physicalBox s P).center ∈ centerRegion.carrier := by
  have hb := physical_center_bounds s hp
  have hs := state_extent s
  have hk := kappa_le M
  have hx₀ : (1 / 8 : ℝ) ≤ origin s := by
    cases he : terminalControl s <;> simp only [he, Bool.false_eq_true, ↓reduceIte] at hs <;>
      linarith [hs.1]
  have hx₁ : origin s + kappa M < (13 / 16 : ℝ) := by
    cases he : terminalControl s <;> simp only [he, Bool.false_eq_true, ↓reduceIte] at hs <;>
      linarith [hs.2]
  exact ⟨⟨hx₀.trans hb.1, (hb.2.1.trans_lt hx₁).le⟩, ⟨hb.2.2.1, by
    dsimp [centerRegion]; linarith [hb.2.2.2]⟩⟩

 
theorem chart_bounds {c v : ℝ × ℝ} (hc : c ∈ centerRegion.carrier)
    (hv₁ : |v.1| ≤ kappa M) (hv₂ : |v.2| ≤ kappa M) :
    (1 / 32 : ℝ) < c.1 + v.1 ∧ c.1 + v.1 < 31 / 32 ∧
    (1 / 32 : ℝ) < c.2 + v.2 ∧ c.2 + v.2 < 31 / 32 := by
  have hk := kappa_le M
  rcases abs_le.mp hv₁ with ⟨hx₀, hx₁⟩
  rcases abs_le.mp hv₂ with ⟨hy₀, hy₁⟩
  change ((1 / 8 : ℝ) ≤ c.1 ∧ c.1 ≤ 13 / 16) ∧
    ((3 / 8 : ℝ) ≤ c.2 ∧ c.2 ≤ 7 / 16) at hc
  constructor
  · linarith [hc.1.1]
  constructor
  · linarith [hc.1.2]
  constructor <;> linarith [hc.2.1, hc.2.2]

 
theorem affine_lower {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1)) (i : Branch M) :
    affine e i (sourceRectangle e i).lower = (targetRectangle e i).lower := by
  simp only [affine, sourceRectangle, targetRectangle, physicalBox, unplace_place]
  congr 1
  cases hd : i.move <;> simp [branchSource, branchTarget, sourceBox, targetBox, Radix.update, hd]

theorem affine_upper {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1)) (i : Branch M) :
    affine e i (sourceRectangle e i).upper = (targetRectangle e i).upper := by
  simp only [affine, sourceRectangle, targetRectangle, physicalBox, unplace_place]
  congr 1
  cases hd : i.move <;> simp [branchSource, branchTarget, sourceBox, targetBox, Radix.update, hd]

 
theorem affine_center {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1)) (i : Branch M) :
    affine e i (sourceRectangle e i).center = (targetRectangle e i).center := by
  have hhalf := affine_linear_part e i (sourceRectangle e i).center
    (sourceRectangle e i).lower
  have hfull := affine_linear_part e i (sourceRectangle e i).upper
    (sourceRectangle e i).lower
  rw [affine_lower] at hhalf hfull
  rw [affine_upper] at hfull
  have h₁ := congrArg Prod.fst hhalf
  have h₂ := congrArg Prod.snd hhalf
  have h₃ := congrArg Prod.fst hfull
  have h₄ := congrArg Prod.snd hfull
  dsimp [Rectangle.center] at h₁ h₂ h₃ h₄ ⊢
  apply Prod.ext <;> dsimp <;> nlinarith

 
theorem affine_centered {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1)) (i : Branch M)
    (x : ℝ × ℝ) :
    affine e i x = (targetRectangle e i).center +
      (Radix.scale m i.move * (x.1 - (sourceRectangle e i).center.1),
        (x.2 - (sourceRectangle e i).center.2) / Radix.scale m i.move) := by
  have h := affine_linear_part e i x (sourceRectangle e i).center
  rw [affine_center] at h
  apply Prod.ext
  · have h₁ := congrArg Prod.fst h
    dsimp at h₁ ⊢
    linarith
  · have h₂ := congrArg Prod.snd h
    dsimp at h₂ ⊢
    simpa only [div_eq_mul_inv, mul_comm, add_comm] using eq_add_of_sub_eq h₂

 

theorem branch_offset_bounds {m : ℕ} (e : Recorder.Letter M ≃ Fin (m + 1)) (i : Branch M)
    {x : ℝ × ℝ} (hx : x ∈ (sourceRectangle e i).carrier) :
    |x.1 - (sourceRectangle e i).center.1| ≤ kappa M / 2 ∧
    |x.2 - (sourceRectangle e i).center.2| ≤ kappa M / 2 ∧
    |Radix.scale m i.move * (x.1 - (sourceRectangle e i).center.1)| ≤ kappa M / 2 ∧
    |(x.2 - (sourceRectangle e i).center.2) / Radix.scale m i.move| ≤ kappa M / 2 := by
  have hy : affine e i x ∈ (targetRectangle e i).carrier := by
    rw [← affine_image e i]
    exact Set.mem_image_of_mem _ hx
  have hs := Rectangle.offset_bound hx
  have ht := Rectangle.offset_bound hy
  have hw := rectangle_widths e i
  rw [affine_centered] at ht
  simp only [Prod.fst_add, Prod.snd_add, add_sub_cancel_left] at ht
  exact ⟨hs.1.trans hw.2.2.1, hs.2.trans hw.2.2.2.1,
    ht.1.trans hw.2.2.2.2.1, ht.2.trans hw.2.2.2.2.2⟩
end Bridge
end Solenoidal

end OAI
