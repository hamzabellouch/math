import OAI.NumberTheory.Ostmann.Characters.TemplateInitialPhase

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem regular_character_row {ι:Type*} [Fintype ι] [DecidableEq ι]
    (p:ι→ℕ) [∀i,Fact (p i).Prime] (i:ι) (χ:MulChar (ZMod (p i)) ℂ)
    (B:ι→ℤ) (ε:ℤ) (hself:B i=0) (hreg:∀j,j≠i→B j=ε) :
    (∏j:ι,χ (p j)^B j)=χ (Construction.otherProduct p i)^ε := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  simp only [hself,zpow_zero,mul_one]
  rw [Construction.otherProduct,Nat.cast_prod,map_prod,← Finset.prod_zpow]
  apply Finset.prod_congr rfl
  intro j hj
  rw [hreg j (Finset.mem_erase.mp hj).1]

theorem regular_frequency_row {ι:Type*} [Fintype ι] [DecidableEq ι]
    (p:ι→ℕ) [∀i,Fact (p i).Prime] (i:ι) (χ:MulChar (ZMod (p i)) ℂ)
    (B:ι→ℤ) (ε:ℤ) (hself:B i=0) (hreg:∀j,j≠i→B j=ε)
    (κ:ℂ) (v:ℤ) :
    (κ*χ (v:ZMod (p i))^(-ε))*(∏j:ι,χ (p j)^B j)=
      κ*χ ((Construction.otherProduct p i:ZMod (p i))/(v:ZMod (p i)))^ε := by
  rw [regular_character_row p i χ B ε hself hreg]
  simp only [div_eq_mul_inv,map_mul,← MulChar.inv_apply',MulChar.inv_apply_eq_inv',
    mul_zpow,zpow_neg,inv_zpow]
  ring

theorem constituent_regular_frequency_row (k n:ℕ) (hn:n≤k) (width:Role→ℕ)
    (p:(schedule k n).Constituent width→ℕ) [∀i,Fact (p i).Prime]
    (i:(schedule k n).Constituent width)
    (hi:(schedule k n).IsRegular n i.1) (χ:MulChar (ZMod (p i)) ℂ) (κ:ℂ) (v:ℤ) :
    (κ*χ (v:ZMod (p i))^(-(rowSign k n i.1:ℤ)))*
      (∏h,χ (p h)^constituentGraph k n width i h)=
      κ*χ ((Construction.otherProduct p i:ZMod (p i))/(v:ZMod (p i)))^
        (rowSign k n i.1:ℤ) := by
  apply regular_frequency_row
  · simp [constituentGraph,liftGraph]
  · exact constituentGraph_regular k n hn width i hi

end Ostmann.Characters.Template

end

end OAI
