import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLevelReciprocity

namespace OAI

/-! Existence and cubic phases of the inverse residue used in the
primary-level rational transformation. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaLevel_inverse_exists {q x : Eisenstein} (hq : primary q)
    (hx : IsCoprime q x) : ∃ y : Eisenstein,q∣9*x*y-1 := by
  have h9 : IsCoprime q (9:Eisenstein) := by
    convert (primary_coprime_three hq).pow_right (n:=2) using 1
    norm_num
  obtain ⟨a,b,h⟩ := h9.mul_right hx
  refine ⟨b,⟨-a,?_⟩⟩
  linear_combination h

lemma cubicThetaLevel_inverse_symmetric {q x y : Eisenstein}
    (hxy : q∣9*x*y-1) : q∣9*y*x-1 := by
  convert hxy using 1
  ring

theorem cubicThetaLevel_inverse_phases {q x y : Eisenstein} (hq : primary q)
    (hxy : q∣9*x*y-1) : cubicSymbol q (3*x)*cubicSymbol q (3*y)=1 := by
  rw [←cubicSymbol_mul_upper hq]
  have he : q∣(3*x)*(3*y)-1 := by convert hxy using 1; ring
  rw [cubicSymbol_congr (residue_eq_of_dvd_sub he),
    cubic_reciprocity hq primary_one,cubicSymbol_one_lower]

theorem cubicThetaLevel_inverse_phase_ne_zero {q x y : Eisenstein} (hq : primary q)
    (hxy : q∣9*x*y-1) : cubicSymbol q (3*x)≠0 := by
  intro h
  have he := cubicThetaLevel_inverse_phases hq hxy
  rw [h,zero_mul] at he
  exact zero_ne_one he

end CubicFirstMoment

end

end OAI
