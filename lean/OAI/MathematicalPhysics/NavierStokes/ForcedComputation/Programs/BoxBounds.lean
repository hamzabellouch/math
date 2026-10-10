import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.InstructionRectangles

namespace OAI

namespace ForcedComputation.Radix

open ShearFlows

def InUnit (R : RationalBox 2) : Prop := ∀ j, 0 ≤ R.lower j ∧ R.upper j ≤ 1

theorem sourceBox_inUnit {B : ℚ} (hB : 0 < B) {l a : ℚ}
    (hl : 0 ≤ l ∧ l + 1 ≤ B) (ha : 0 ≤ a ∧ a + 1 ≤ B) :
    InUnit (sourceBox B l a) := by
  intro j
  fin_cases j
  · exact ⟨div_nonneg hl.1 hB.le, (div_le_one hB).mpr hl.2⟩
  · exact ⟨div_nonneg ha.1 hB.le, (div_le_one hB).mpr ha.2⟩

theorem targetBox_inUnit {B : ℚ} (hB : 0 < B) {l b : ℚ}
    (hl : 0 ≤ l ∧ l + 1 ≤ B) (hb : 0 ≤ b ∧ b + 1 ≤ B) (m : HeadMove) :
    InUnit (targetBox B l b m) := by
  have hp : 0 < B ^ 2 := pow_pos hB 2
  have nested {a c : ℚ} (ha : 0 ≤ a ∧ a + 1 ≤ B) (hc : 0 ≤ c ∧ c + 1 ≤ B) :
      0 ≤ a / B + c / B ^ 2 ∧ a / B + (c + 1) / B ^ 2 ≤ 1 := by
    refine ⟨add_nonneg (div_nonneg ha.1 hB.le) (div_nonneg hc.1 hp.le), ?_⟩
    calc
      a / B + (c + 1) / B ^ 2 ≤ a / B + B / B ^ 2 := by
        exact add_le_add (le_refl _) ((div_le_div_iff_of_pos_right hp).mpr hc.2)
      _ = (a + 1) / B := by field_simp
      _ ≤ 1 := (div_le_one hB).mpr ha.2
  intro j
  cases m <;> fin_cases j
  · exact ⟨le_rfl, le_rfl⟩
  · exact nested hl hb
  · exact ⟨div_nonneg hl.1 hB.le, (div_le_one hB).mpr hl.2⟩
  · exact ⟨div_nonneg hb.1 hB.le, (div_le_one hB).mpr hb.2⟩
  · exact nested hb hl
  · exact ⟨le_rfl, le_rfl⟩

theorem center_mem {R : RationalBox 2} (hR : R.positive) : R.center ∈ R.carrier := by
  intro j
  have h : (R.lower j : ℝ) < R.upper j := by exact_mod_cast hR j
  dsimp [RationalBox.center]
  constructor <;> linarith

theorem halfWidth_le_half {R : RationalBox 2} (hR : InUnit R) (j : Fin 2) :
    R.halfWidth j ≤ 1 / 2 := by
  have hl : (0 : ℝ) ≤ R.lower j := by exact_mod_cast (hR j).1
  have hu : (R.upper j : ℝ) ≤ 1 := by exact_mod_cast (hR j).2
  dsimp [RationalBox.halfWidth]
  linarith

theorem scaledBox_between {κ : ℚ} (hκ : 0 ≤ κ) (offset : Fin 2 → ℚ)
    {R : RationalBox 2} (hR : InUnit R) {x : Plane}
    (hx : x ∈ (scaledBox κ offset R).carrier) (j : Fin 2) :
    (offset j : ℝ) ≤ x j ∧ x j ≤ (offset j : ℝ) + (κ : ℝ) := by
  have hp : (0 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hl : (0 : ℝ) ≤ R.lower j := by exact_mod_cast (hR j).1
  have hu : (R.upper j : ℝ) ≤ 1 := by exact_mod_cast (hR j).2
  have hj := hx j
  simp only [scaledBox, Rat.cast_add, Rat.cast_mul] at hj
  exact ⟨(le_add_of_nonneg_right (mul_nonneg hp hl)).trans hj.1,
    hj.2.trans (by simpa only [mul_one] using (add_le_add (le_refl (offset j : ℝ)) (mul_le_mul_of_nonneg_left hu hp)))⟩

end ForcedComputation.Radix

end OAI
