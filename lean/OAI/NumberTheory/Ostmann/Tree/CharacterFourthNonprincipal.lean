import OAI.NumberTheory.Ostmann.Tree.CharacterFourth

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance nonprincipalFourthFintype : Fintype (MulChar F ℂ) := Fintype.ofFinite _

theorem weightedCharacterSum_principal (w : F → ℝ) (a : F) :
    weightedCharacterSum w 1 a = ((∑ b,w b)-w a:ℝ) := by
  classical
  have he (b : F) : (w b:ℂ)*(1:MulChar F ℂ) (a-b) =
      if b=a then 0 else (w b:ℂ) := by
    by_cases h : b=a
    · simp [h,MulChar.map_zero]
    · have hn : a-b≠0 := sub_ne_zero.mpr (Ne.symm h)
      rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hn)]
      simp [h]
  simp only [weightedCharacterSum,he]
  rw [Finset.sum_ite, Finset.sum_const_zero,zero_add]
  have hs := Finset.sum_erase_add (Finset.univ : Finset F) (fun b => (w b:ℂ)) (Finset.mem_univ a)
  have hf : Finset.univ.filter (fun b : F => ¬ b=a)=Finset.univ.erase a := by ext b; simp [ne_eq,eq_comm]
  rw [hf]
  push_cast
  exact eq_sub_iff_add_eq.mpr hs

omit [Field F] [DecidableEq F] in
theorem principal_fourth_lower (w : F → ℝ) :
    ((Fintype.card F:ℝ)-4)*(∑ b,w b)^4 ≤ ∑ a, ((∑ b,w b)-w a)^4 := by
  let J := ∑ b,w b
  have hp (a : F) : J^4-4*J^3*w a ≤ (J-w a)^4 := by
    have h : 0≤(w a)^2*((w a-2*J)^2+2*J^2) := by positivity
    nlinarith only [h]
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun a _ => hp a)
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    ← Finset.mul_sum] at hs
  change _ ≤ ∑ a,(J-w a)^4
  change (Fintype.card F:ℝ)*J^4-4*J^3*J ≤ _ at hs
  nlinarith only [hs]

theorem weightedCharacterSum_nonprincipal_fourth_bound (w : F → ℝ)
    (hw : ∀ x,0≤w x) :
    (∑ χ : MulChar F ℂ, if χ=1 then 0 else ∑ a : F, ‖weightedCharacterSum w χ a‖^4) ≤
      2*(Fintype.card Fˣ:ℝ)*(Fintype.card F:ℝ)*(∑ x,w x^2)^2+3*(∑ x,w x)^4 := by
  classical
  have hall := weightedCharacterSum_fourth_bound w hw
  have hp := principal_fourth_lower w
  have hprincipal : (∑ a : F, ‖weightedCharacterSum w (1:MulChar F ℂ) a‖^4) =
      ∑ a,((∑ b,w b)-w a)^4 := by
    simp only [weightedCharacterSum_principal,Complex.norm_real,Real.norm_eq_abs,
      show ∀ x : ℝ, |x|^4=x^4 from fun x => by rw [show 4=2*2 from rfl,pow_mul,sq_abs,pow_mul]]
  have hsplit :
      (∑ χ : MulChar F ℂ, if χ=1 then 0 else ∑ a : F, ‖weightedCharacterSum w χ a‖^4) +
      (∑ a : F, ‖weightedCharacterSum w (1:MulChar F ℂ) a‖^4) =
      ∑ χ : MulChar F ℂ, ∑ a : F, ‖weightedCharacterSum w χ a‖^4 := by
    have he : (∑ χ : MulChar F ℂ, if χ=1 then ∑ a : F, ‖weightedCharacterSum w χ a‖^4 else 0) =
        ∑ a : F, ‖weightedCharacterSum w (1:MulChar F ℂ) a‖^4 := by simp
    rw [← he, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro χ _
    split_ifs <;> simp_all
  have hcard : (Fintype.card Fˣ:ℝ)=(Fintype.card F:ℝ)-1 := by
    rw [Fintype.card_units,Nat.cast_sub (Nat.succ_le_of_lt Fintype.card_pos),Nat.cast_one]
  rw [hprincipal] at hsplit
  rw [hcard] at hall ⊢
  nlinarith only [hall,hp,hsplit]

end
end Ostmann.FiniteField

end OAI
