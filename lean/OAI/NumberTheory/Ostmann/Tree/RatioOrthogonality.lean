import OAI.NumberTheory.Ostmann.Tree.CharacterFourth
import OAI.NumberTheory.Ostmann.Tree.DoubleMellinEnergy

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance ratioOrthogonalityFintype : Fintype (MulChar F ℂ) := Fintype.ofFinite _

def ratioArgument (y d : F) : F := d/(d-y)

omit [Fintype F] [DecidableEq F] in
theorem ratioArgument_eq_zero (y d : F) : ratioArgument y d=0 ↔ d=0 ∨ d=y := by
  simp only [ratioArgument,div_eq_zero_iff,sub_eq_zero]

omit [Fintype F] [DecidableEq F] in
theorem ratioArgument_injective (y : F) (hy : y≠0) {d e : F}
    (hd : ratioArgument y d≠0) (heq : ratioArgument y d=ratioArgument y e) : d=e := by
  have hdy : d-y≠0 := by intro h; apply hd; simp [ratioArgument,h]
  have hey : e-y≠0 := by intro h; apply hd; rw [heq]; simp [ratioArgument,h]
  have hc := (div_eq_div_iff hdy hey).mp heq
  apply mul_left_cancel₀ hy
  linear_combination -hc

omit [Fintype F] [DecidableEq F] in
theorem ratioArgument_kernel (y : F) (hy : y≠0) (d e : F) :
    (ratioArgument y d=ratioArgument y e ∧ ratioArgument y d≠0) ↔
      (d=e ∧ d≠0 ∧ d≠y) := by
  constructor
  · rintro ⟨hde,hd⟩
    exact ⟨ratioArgument_injective y hy hd hde,
      fun h => hd ((ratioArgument_eq_zero y d).mpr (Or.inl h)),
      fun h => hd ((ratioArgument_eq_zero y d).mpr (Or.inr h))⟩
  · rintro ⟨rfl,hd,hy⟩
    exact ⟨rfl,fun h => (ratioArgument_eq_zero y d).mp h |>.elim hd hy⟩

omit [Fintype F] [DecidableEq F] in
theorem ratioCharacter (χ : MulChar F ℂ) (y d : F) :
    χ d*χ⁻¹ (d-y)=χ (ratioArgument y d) := by
  rw [MulChar.inv_apply',← map_mul]
  rw [ratioArgument,div_eq_mul_inv]

omit [Field F] [DecidableEq F] in
theorem norm_sum_sq_expansion (z : F → ℂ) :
    (‖∑ d,z d‖^2:ℂ)=∑ d,∑ e,z d*conj (z e) := by
  rw [← Complex.mul_conj']
  simp only [map_sum,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem ratio_character_energy (f : F → ℂ) (y : F) (hy : y≠0) :
    (∑ χ : MulChar F ℂ, ‖∑ d : F,f d*χ d*χ⁻¹ (d-y)‖^2) =
      (Fintype.card Fˣ:ℝ)*∑ d : F,if d=0 ∨ d=y then 0 else ‖f d‖^2 := by
  classical
  have hpoint (χ : MulChar F ℂ) (d : F) : f d*χ d*χ⁻¹ (d-y)=f d*χ (ratioArgument y d) := by
    rw [mul_assoc,ratioCharacter]
  simp_rw [hpoint]
  apply Complex.ofReal_injective
  push_cast
  simp_rw [norm_sum_sq_expansion]
  have hs : (∑ χ : MulChar F ℂ,∑ d : F,∑ e : F,
      (f d*χ (ratioArgument y d))*conj (f e*χ (ratioArgument y e))) =
      ∑ d : F,∑ e : F,∑ χ : MulChar F ℂ,
      (f d*χ (ratioArgument y d))*conj (f e*χ (ratioArgument y e)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_comm]
  rw [hs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  have he (e : F) : (∑ χ : MulChar F ℂ,
      (f d*χ (ratioArgument y d))*conj (f e*χ (ratioArgument y e))) =
      (f d*conj (f e))*(if d=e ∧ d≠0 ∧ d≠y then (Fintype.card Fˣ:ℂ) else 0) := by
    calc
      _ = (f d*conj (f e))*(∑ χ : MulChar F ℂ,
          χ (ratioArgument y d)*conj (χ (ratioArgument y e))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro χ _
        rw [map_mul]
        ring
      _ = _ := by simp only [sum_mulChar_field_kernel,ratioArgument_kernel y hy]
  simp_rw [he]
  by_cases hd : d=0 ∨ d=y
  · rcases hd with hd | hd <;> simp [hd]
  · have hd0 : d≠0 := fun h => hd (Or.inl h)
    have hdy : d≠y := fun h => hd (Or.inr h)
    simp [hd0,hdy,Complex.mul_conj',mul_comm]

end
end Ostmann.FiniteField

end OAI
