import OAI.NumberTheory.Ostmann.Tree.MellinSquare
import OAI.NumberTheory.Ostmann.Tree.PairMobius

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
theorem mobius_character_weight (c r : Fˣ) (χ : MulChar F ℂ) (hr : (r:F) ≠ 1) :
    χ⁻¹ (pairMobiusValue c r)*χ (pairMobiusValue c r-c) = conj (χ r) := by
  let e : F := (c:F)/((r:F)-1)
  have he : e ≠ 0 := div_ne_zero (Units.ne_zero c) (sub_ne_zero.mpr hr)
  have hdiff : pairMobiusValue c r-(c:F)=e := pairMobiusValue_sub c r hr
  have hd : pairMobiusValue c r=(r:F)*e := by
    dsimp [pairMobiusValue,e]
    ring
  have hχ : χ⁻¹ e*χ e=1 := by
    rw [← MulChar.mul_apply, inv_mul_cancel]
    exact MulChar.one_apply_coe (Units.mk0 e he)
  rw [hdiff,hd,map_mul]
  calc
    _ = χ⁻¹ r*(χ⁻¹ e*χ e) := by ring
    _ = χ⁻¹ r := by rw [hχ,mul_one]
    _ = conj (χ r) := (MulChar.star_apply' χ r).symm

theorem mellin_mobius_pullback (H : F → ℂ) (c : Fˣ) (χ : MulChar F ℂ)
    (hH0 : H 0=0) :
    mellin (fun r : Fˣ => H (pairMobiusValue c r)) χ =
      (Fintype.card Fˣ:ℂ)⁻¹ * ∑ d : F, H d*(χ⁻¹ d*χ (d-c)) := by
  let Ψ : F → ℂ := fun d => H d*(χ⁻¹ d*χ (d-c))
  have hp (r : Fˣ) : H (pairMobiusValue c r)*conj (χ r) = Ψ (pairMobiusValue c r) := by
    by_cases hr : (r:F)=1
    · simp [Ψ,pairMobiusValue,hr,hH0]
    · dsimp [Ψ]
      rw [mobius_character_weight c r χ hr]
  have hΨ0 : Ψ 0=0 := by simp [Ψ,hH0]
  have hΨc : Ψ c=0 := by simp [Ψ, χ.map_zero]
  have hcomp0 : Ψ (pairMobiusValue c 0)=0 := by simpa [pairMobiusValue] using hΨ0
  unfold mellin
  simp_rw [hp]
  rw [sum_units_of_zero (fun r => Ψ (pairMobiusValue c r)) hcomp0,
    pairMobius_sum c Ψ hΨ0 hΨc]

end
end Ostmann.FiniteField

end OAI
