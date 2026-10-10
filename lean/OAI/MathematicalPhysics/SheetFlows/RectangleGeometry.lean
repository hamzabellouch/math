import Mathlib
import OAI.MathematicalPhysics.SheetFlows.Model

namespace OAI

/-! SheetFlows rectangle geometry. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

namespace Rectangle

theorem halfWidth_pos (R : Rectangle) (j : Fin 2) : 0 < R.halfWidth j := by
  have h : (R.lower j : ℝ) < (R.upper j : ℝ) := by exact_mod_cast R.positive j
  dsimp [halfWidth]
  linarith

theorem center_sub_halfWidth (R : Rectangle) (j : Fin 2) :
    R.center j - R.halfWidth j = (R.lower j : ℝ) := by
  dsimp [center, halfWidth]
  ring

theorem center_add_halfWidth (R : Rectangle) (j : Fin 2) :
    R.center j + R.halfWidth j = (R.upper j : ℝ) := by
  dsimp [center, halfWidth]
  ring

theorem mem_iff_abs (R : Rectangle) (y : Plane) :
    y ∈ R.carrier ↔ ∀ j, |y j - R.center j| ≤ R.halfWidth j := by
  simp only [carrier, Set.mem_ofPred_eq, abs_le]
  constructor
  · intro h j
    have hl := (h j).1
    have hu := (h j).2
    dsimp [center, halfWidth]
    constructor <;> linarith
  · intro h j
    have hl := (h j).1
    have hu := (h j).2
    dsimp [center, halfWidth] at hl hu
    constructor <;> linarith

theorem center_mem (R : Rectangle) : R.center ∈ R.carrier := by
  rw [mem_iff_abs]
  intro j
  simpa using le_of_lt (halfWidth_pos R j)

theorem upper_mem (R : Rectangle) : (fun j => (R.upper j : ℝ)) ∈ R.carrier := by
  intro j
  have h : (R.lower j : ℝ) < (R.upper j : ℝ) := by exact_mod_cast R.positive j
  exact ⟨h.le, le_rfl⟩

theorem halfWidth_le_half (R : Rectangle) (h : R.inCodingSquare) (j : Fin 2) :
    R.halfWidth j ≤ 1 / 2 := by
  have hl : (2 : ℝ) ≤ R.lower j := by exact_mod_cast (h j).1
  have hu : (R.upper j : ℝ) ≤ 3 := by exact_mod_cast (h j).2
  dsimp [halfWidth]
  linarith

theorem offset_bound (R : Rectangle) (hR : R.inCodingSquare)
    {y : Plane} (hy : y ∈ R.carrier) (j : Fin 2) :
    |y j - R.center j| ≤ 1 / 2 :=
  ((R.mem_iff_abs y).mp hy j).trans (R.halfWidth_le_half hR j)

end Rectangle

theorem diagonalMap_upper (P Q : Rectangle) (r : Fin 2 → ℚ)
    (hr : ∀ j, 0 < r j)
    (himage : diagonalMap P Q r '' P.carrier = Q.carrier) :
    diagonalMap P Q r (fun j => (P.upper j : ℝ)) = fun j => (Q.upper j : ℝ) := by
  have hmax : ∀ y ∈ P.carrier, ∀ j,
      diagonalMap P Q r y j ≤ diagonalMap P Q r (fun k => (P.upper k : ℝ)) j := by
    intro y hy j
    have hj : (0 : ℝ) ≤ (r j : ℝ) := by exact_mod_cast (hr j).le
    dsimp [diagonalMap]
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (sub_le_sub_right (hy j).2 _) hj)
  have hup : diagonalMap P Q r (fun j => (P.upper j : ℝ)) ∈ Q.carrier := by
    rw [← himage]
    exact ⟨_, P.upper_mem, rfl⟩
  obtain ⟨y, hy, he⟩ : ∃ y ∈ P.carrier,
      diagonalMap P Q r y = (fun j => (Q.upper j : ℝ)) := by
    have h := Q.upper_mem
    rw [← himage] at h
    exact h
  funext j
  apply le_antisymm (hup j).2
  simpa only [he] using hmax y hy j

theorem SheetData.ratio_mul_halfWidth {N : ℕ} (D : SheetData N)
    (i : Fin N) (j : Fin 2) :
    (D.ratio i j : ℝ) * (D.source i).halfWidth j = (D.target i).halfWidth j := by
  have h := congrFun (diagonalMap_upper (D.source i) (D.target i) (D.ratio i)
    (D.ratio_positive i) (D.image_eq i)) j
  dsimp [diagonalMap, Rectangle.center] at h
  dsimp [Rectangle.halfWidth]
  linarith

theorem SheetData.ratio_eq_halfWidth_ratio {N : ℕ} (D : SheetData N)
    (i : Fin N) (j : Fin 2) :
    (D.ratio i j : ℝ) = (D.target i).halfWidth j / (D.source i).halfWidth j := by
  apply (eq_div_iff (ne_of_gt ((D.source i).halfWidth_pos j))).mpr
  exact D.ratio_mul_halfWidth i j

theorem SheetData.scaled_offset_bound {N : ℕ} (D : SheetData N)
    (i : Fin N) {y : Plane} (hy : y ∈ (D.source i).carrier) (j : Fin 2) :
    |(D.ratio i j : ℝ) * (y j - (D.source i).center j)| ≤ 1 / 2 := by
  have hr : (0 : ℝ) < (D.ratio i j : ℝ) := by exact_mod_cast D.ratio_positive i j
  rw [abs_mul, abs_of_pos hr]
  calc
    (D.ratio i j : ℝ) * |y j - (D.source i).center j| ≤
        (D.ratio i j : ℝ) * (D.source i).halfWidth j :=
      mul_le_mul_of_nonneg_left (((D.source i).mem_iff_abs y).mp hy j) hr.le
    _ = (D.target i).halfWidth j := D.ratio_mul_halfWidth i j
    _ ≤ 1 / 2 := (D.target i).halfWidth_le_half (D.target_inside i) j

abbrev OffsetHeight := ℝ × ℝ

def verticalShear (a : ℝ) (p : OffsetHeight) : OffsetHeight :=
  (p.1, p.2 + a * p.1)

def horizontalShear (b : ℝ) (p : OffsetHeight) : OffsetHeight :=
  (p.1 + b * p.2, p.2)

def threeShears (κ μ : ℝ) (p : OffsetHeight) : OffsetHeight :=
  verticalShear (-κ / μ)
    (horizontalShear ((μ - 1) / κ) (verticalShear κ p))

theorem threeShears_action {κ μ : ℝ} (hκ : κ ≠ 0) (hμ : μ ≠ 0)
    (ξ ζ : ℝ) :
    threeShears κ μ (ξ, ζ) = (μ * ξ + (μ - 1) / κ * ζ, ζ / μ) := by
  ext <;> dsimp [threeShears, verticalShear, horizontalShear]
  · field_simp
    ring
  · field_simp
    ring

theorem threeShears_on_sheet {κ μ : ℝ} (hκ : κ ≠ 0) (hμ : μ ≠ 0) (ξ : ℝ) :
    threeShears κ μ (ξ, 0) = (μ * ξ, 0) := by
  simp [threeShears_action hκ hμ]

def coreMatrix₂ (κ μ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![μ, (μ - 1) / κ; 0, 1 / μ]

theorem coreMatrix₂_det (κ : ℝ) {μ : ℝ} (hμ : μ ≠ 0) :
    (coreMatrix₂ κ μ).det = 1 := by
  simp [coreMatrix₂, Matrix.det_fin_two, hμ]

def tripleX (κ μ : ℝ) (x : Space) : Space :=
  ![(threeShears κ μ (x 0, x 2)).1, x 1, (threeShears κ μ (x 0, x 2)).2]

def tripleY (κ μ : ℝ) (x : Space) : Space :=
  ![x 0, (threeShears κ μ (x 1, x 2)).1, (threeShears κ μ (x 1, x 2)).2]

def sixShears (κ μ₁ μ₂ : ℝ) (x : Space) : Space :=
  tripleY κ μ₂ (tripleX κ μ₁ x)

theorem sixShears_action {κ μ₁ μ₂ : ℝ}
    (hκ : κ ≠ 0) (h₁ : μ₁ ≠ 0) (h₂ : μ₂ ≠ 0) (x : Space) :
    sixShears κ μ₁ μ₂ x =
      ![μ₁ * x 0 + (μ₁ - 1) / κ * x 2,
        μ₂ * x 1 + (μ₂ - 1) / κ * (x 2 / μ₁),
        x 2 / (μ₁ * μ₂)] := by
  simp [sixShears, tripleX, tripleY, threeShears_action hκ h₁,
    threeShears_action hκ h₂, div_div]

theorem sixShears_on_sheet {κ μ₁ μ₂ : ℝ}
    (hκ : κ ≠ 0) (h₁ : μ₁ ≠ 0) (h₂ : μ₂ ≠ 0) (y : Plane) :
    sixShears κ μ₁ μ₂ ![y 0, y 1, 0] = ![μ₁ * y 0, μ₂ * y 1, 0] := by
  simp [sixShears_action hκ h₁ h₂]

def coreMatrix₃ (κ μ₁ μ₂ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![μ₁, 0, (μ₁ - 1) / κ;
     0, μ₂, (μ₂ - 1) / (κ * μ₁);
     0, 0, 1 / (μ₁ * μ₂)]

theorem coreMatrix₃_mulVec {κ μ₁ μ₂ : ℝ}
    (hκ : κ ≠ 0) (h₁ : μ₁ ≠ 0) (h₂ : μ₂ ≠ 0) (x : Space) :
    (coreMatrix₃ κ μ₁ μ₂).mulVec x = sixShears κ μ₁ μ₂ x := by
  rw [sixShears_action hκ h₁ h₂]
  ext j
  fin_cases j <;> simp [coreMatrix₃, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  all_goals ring

theorem coreMatrix₃_det (κ : ℝ) {μ₁ μ₂ : ℝ}
    (h₁ : μ₁ ≠ 0) (h₂ : μ₂ ≠ 0) :
    (coreMatrix₃ κ μ₁ μ₂).det = 1 := by
  simp [coreMatrix₃, Matrix.det_fin_three]
  field_simp

def centeredCore (p q : Plane) (height κ μ₁ μ₂ : ℝ) (x : Space) : Space :=
  ![q 0, q 1, height] + sixShears κ μ₁ μ₂ (x - ![p 0, p 1, height])

theorem centeredCore_on_sheet (P Q : Rectangle) (r : Fin 2 → ℚ)
    (hr : ∀ j, 0 < r j) (y : Plane) :
    centeredCore P.center Q.center 2 1 (r 0 : ℝ) (r 1 : ℝ) (sheet y) =
      sheet (diagonalMap P Q r y) := by
  have h₀ : (r 0 : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (hr 0)
  have h₁ : (r 1 : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (hr 1)
  rw [centeredCore, sixShears_action one_ne_zero h₀ h₁]
  ext j
  fin_cases j <;> simp [sheet, diagonalMap]

theorem abs_convex_combination_le {a b B θ : ℝ}
    (ha : |a| ≤ B) (hb : |b| ≤ B) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    |(1 - θ) * a + θ * b| ≤ B := by
  rcases abs_le.mp ha with ⟨ha₀, ha₁⟩
  rcases abs_le.mp hb with ⟨hb₀, hb₁⟩
  have hθ : 0 ≤ 1 - θ := sub_nonneg.mpr hθ₁
  apply abs_le.mpr
  constructor
  · have ea := mul_le_mul_of_nonneg_left ha₀ hθ
    have eb := mul_le_mul_of_nonneg_left hb₀ hθ₀
    nlinarith
  · have ea := mul_le_mul_of_nonneg_left ha₁ hθ
    have eb := mul_le_mul_of_nonneg_left hb₁ hθ₀
    nlinarith

theorem first_phase (ξ θ : ℝ) : verticalShear θ (ξ, 0) = (ξ, θ * ξ) := by
  simp [verticalShear]

theorem middle_phase (μ ξ θ : ℝ) :
    horizontalShear (θ * (μ - 1)) (verticalShear 1 (ξ, 0)) =
      ((1 - θ) * ξ + θ * (μ * ξ), ξ) := by
  ext <;> dsimp [horizontalShear, verticalShear] <;> ring

theorem last_phase {μ : ℝ} (hμ : μ ≠ 0) (ξ θ : ℝ) :
    verticalShear (-θ / μ)
        (horizontalShear (μ - 1) (verticalShear 1 (ξ, 0))) =
      (μ * ξ, (1 - θ) * ξ) := by
  ext <;> dsimp [horizontalShear, verticalShear]
  · ring
  · field_simp
    ring

theorem triple_path_bounds {μ ξ θ : ℝ} (hμ : μ ≠ 0)
    (hξ : |ξ| ≤ 1 / 2) (hμξ : |μ * ξ| ≤ 1 / 2)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (|((verticalShear θ (ξ, 0)).1)| ≤ 1 / 2 ∧
      |((verticalShear θ (ξ, 0)).2)| ≤ 1 / 2) ∧
    (|((horizontalShear (θ * (μ - 1)) (verticalShear 1 (ξ, 0))).1)| ≤ 1 / 2 ∧
      |((horizontalShear (θ * (μ - 1)) (verticalShear 1 (ξ, 0))).2)| ≤ 1 / 2) ∧
    (|((verticalShear (-θ / μ)
        (horizontalShear (μ - 1) (verticalShear 1 (ξ, 0)))).1)| ≤ 1 / 2 ∧
      |((verticalShear (-θ / μ)
        (horizontalShear (μ - 1) (verticalShear 1 (ξ, 0)))).2)| ≤ 1 / 2) := by
  rw [first_phase, middle_phase, last_phase hμ]
  have hzero : |(0 : ℝ)| ≤ 1 / 2 := by norm_num
  have hfirst := abs_convex_combination_le hzero hξ hθ₀ hθ₁
  have hlast := abs_convex_combination_le hξ hzero hθ₀ hθ₁
  simp only [mul_zero, zero_add, add_zero] at hfirst hlast
  exact ⟨⟨hξ, hfirst⟩, ⟨abs_convex_combination_le hξ hμξ hθ₀ hθ₁, hξ⟩,
    ⟨hμξ, hlast⟩⟩

theorem processing_height_bound {ζ : ℝ} (hζ : |ζ| ≤ 1 / 2) :
    (9 / 2 : ℝ) ≤ 5 + ζ ∧ 5 + ζ ≤ 11 / 2 := by
  rcases abs_le.mp hζ with ⟨hl, hu⟩
  constructor <;> linarith

end Solenoidal
end

end OAI
