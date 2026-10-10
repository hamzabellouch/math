import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Model

namespace OAI

/-! A criterion for the full closed rectangles of a reciprocal instruction. -/

noncomputable section
open Set

namespace ShearFlows

theorem RationalBox.mem_carrier_iff {R : RationalBox 2} {x : Plane} :
    x ∈ R.carrier ↔ ∀ j, |x j - R.center j| ≤ R.halfWidth j := by
  constructor
  · intro hx j
    have hj := hx j
    apply abs_le.mpr
    dsimp [RationalBox.center, RationalBox.halfWidth]
    constructor <;> linarith [hj.1, hj.2]
  · intro hx j
    have hj := abs_le.mp (hx j)
    dsimp [RationalBox.center, RationalBox.halfWidth] at hj
    constructor <;> linarith [hj.1, hj.2]

theorem Instruction.image_eq_of_halfWidths (b : Instruction) (hf : 0 < b.factor)
    (h₀ : b.target.halfWidth 0 = (b.factor : ℝ) * b.source.halfWidth 0)
    (h₁ : b.target.halfWidth 1 = b.source.halfWidth 1 / (b.factor : ℝ)) :
    b.affine '' b.source.carrier = b.target.carrier := by
  have hp : (0 : ℝ) < b.factor := by exact_mod_cast hf
  have hn : (b.factor : ℝ) ≠ 0 := hp.ne'
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply RationalBox.mem_carrier_iff.mpr
    have hm := RationalBox.mem_carrier_iff.mp hx
    intro j
    fin_cases j
    · change |b.target.center 0 + (b.factor : ℝ) * (x 0 - b.source.center 0) -
          b.target.center 0| ≤ b.target.halfWidth 0
      simp only [add_sub_cancel_left, abs_mul, abs_of_pos hp, h₀]
      exact mul_le_mul_of_nonneg_left (hm 0) hp.le
    · change |b.target.center 1 + (x 1 - b.source.center 1) / (b.factor : ℝ) -
          b.target.center 1| ≤ b.target.halfWidth 1
      simp only [add_sub_cancel_left, abs_div, abs_of_pos hp, h₁]
      exact (div_le_div_iff_of_pos_right hp).mpr (hm 1)
  · intro hy
    let x : Plane := ![b.source.center 0 + (y 0 - b.target.center 0) / (b.factor : ℝ),
      b.source.center 1 + (b.factor : ℝ) * (y 1 - b.target.center 1)]
    have hm := RationalBox.mem_carrier_iff.mp hy
    refine ⟨x, RationalBox.mem_carrier_iff.mpr ?_, ?_⟩
    · intro j
      fin_cases j
      · change |b.source.center 0 + (y 0 - b.target.center 0) / (b.factor : ℝ) -
          b.source.center 0| ≤ b.source.halfWidth 0
        simp only [add_sub_cancel_left, abs_div, abs_of_pos hp]
        apply (div_le_iff₀ hp).mpr
        simpa only [h₀, mul_comm] using hm 0
      · change |b.source.center 1 + (b.factor : ℝ) * (y 1 - b.target.center 1) -
          b.source.center 1| ≤ b.source.halfWidth 1
        simp only [add_sub_cancel_left, abs_mul, abs_of_pos hp]
        have hh := mul_le_mul_of_nonneg_left (hm 1) hp.le
        rw [h₁, mul_div_cancel₀ _ hn] at hh
        exact hh
    · funext j
      fin_cases j <;> dsimp [Instruction.affine, x] <;> field_simp <;> ring

end ShearFlows

end

end OAI
