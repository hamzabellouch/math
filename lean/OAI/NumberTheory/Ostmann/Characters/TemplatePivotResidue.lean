import Mathlib.Data.ZMod.Units
import OAI.NumberTheory.Ostmann.Characters.TemplateOutgoingPivot

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
variable {K:Type*} [Fintype K] [DecidableEq K]

def groupedPivotResidue (q:K→ℕ) (H:ℕ) (hH:H.Coprime (∏i,q i)) (v:ℤ) : ZMod (∏i,q i) :=
  (v:ZMod (∏i,q i))*((ZMod.unitOfCoprime H hH)⁻¹:(ZMod (∏i,q i))ˣ)

omit [DecidableEq K] in
theorem groupedPivotResidue_cast (q:K→ℕ) [∀i,Fact (q i).Prime]
    (H:ℕ) (hH:H.Coprime (∏i,q i)) (v:ℤ) (i:K) :
    ZMod.castHom (Finset.dvd_prod_of_mem q (Finset.mem_univ i)) (ZMod (q i))
      (groupedPivotResidue q H hH v)=(v:ZMod (q i))/(H:ZMod (q i)) := by
  unfold groupedPivotResidue
  rw [map_mul,map_intCast,map_units_inv]
  simp only [ZMod.coe_unitOfCoprime,map_natCast,div_eq_mul_inv]

def outgoingPivotProduct (q:K→ℕ) [∀i,Fact (q i).Prime]
    (χ:∀i,MulChar (ZMod (q i)) ℂ) (a:∀i,ZMod (q i))
    (κ:K→ℂ) (ε:K→ℤ) (Y:ℕ) (u:ZMod (∏i,q i)) : ℂ :=
  ∏i,outgoingPivotFactor (χ i) (a i) (κ i) (ε i)
    (Construction.otherProduct q i*Y)
    (ZMod.castHom (Finset.dvd_prod_of_mem q (Finset.mem_univ i)) (ZMod (q i)) u)

theorem norm_character_zpow_le_one {p:ℕ} [Fact p.Prime]
    (χ:MulChar (ZMod p) ℂ) (x:ZMod p) (e:ℤ) : ‖χ x^e‖≤1 := by
  by_cases hx:x=0
  · subst x
    by_cases he:e=0
    · simp [he]
    · simp [MulChar.map_zero,zero_zpow e he]
  · simp [norm_zpow,norm_character_of_ne_zero χ hx]

theorem norm_outgoingPivotFactor_le {p:ℕ} [Fact p.Prime]
    (χ:MulChar (ZMod p) ℂ) (a:ZMod p) (κ:ℂ) (hκ:‖κ‖≤1)
    (ε:ℤ) (D:ℕ) (u:ZMod p) : ‖outgoingPivotFactor χ a κ ε D u‖≤1 := by
  simp only [outgoingPivotFactor,norm_mul,(ZMod.stdAddChar:AddChar (ZMod p) ℂ).norm_apply,one_mul]
  calc
    _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hκ (norm_nonneg _)
    _ ≤ 1 := by simpa using norm_character_zpow_le_one χ _ ε

theorem norm_outgoingPivotProduct_le (q:K→ℕ) [∀i,Fact (q i).Prime]
    (χ:∀i,MulChar (ZMod (q i)) ℂ) (a:∀i,ZMod (q i))
    (κ:K→ℂ) (hκ:∀i,‖κ i‖≤1) (ε:K→ℤ) (Y:ℕ) (u:ZMod (∏i,q i)) :
    ‖outgoingPivotProduct q χ a κ ε Y u‖≤1 := by
  rw [outgoingPivotProduct,norm_prod]
  apply Finset.prod_le_one₀
  · intro i _; exact norm_nonneg _
  · intro i _; exact norm_outgoingPivotFactor_le _ _ _ (hκ i) _ _ _

end Ostmann.Characters.Template

end

end OAI
