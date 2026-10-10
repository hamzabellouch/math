import OAI.NumberTheory.Ostmann.Characters.TemplatePrimeRowUnits

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
variable {H Y:Type*} [Fintype H] [Fintype Y] [DecidableEq H] [DecidableEq Y]

def oldPrimeSharedRow (p:OutputPrimeIndex H Y→ℕ) (i:Y) (t:Bool)
    (χ:MulChar (ZMod (p (.inr i))) ℂ)
    (b:Option (H⊕Y)→Option (H⊕Y)→ℤ) (P:ℤ) : ℂ :=
    χ (P:ZMod (p (.inr i)))^b (some (.inr i)) none *
      (∏h:H,χ (p (.inl (h,t)))^b (some (.inr i)) (some (.inl h))) *
      (∏y:Y,χ (p (.inr y))^b (some (.inr i)) (some (.inr y)))

private theorem sharedUnitRow_coe (p:OutputPrimeIndex H Y→ℕ)
    [∀i,Fact (p i).Prime] (hc:Pairwise (fun i j => (p i).Coprime (p j)))
    (i:Y) (t:Bool) (χ:MulChar (ZMod (p (.inr i))) ℂ)
    (b:Option (H⊕Y)→Option (H⊕Y)→ℤ)
    (hself:b (some (.inr i)) (some (.inr i))=0) (P:ℤ)
    (hP:(P:ZMod (p (.inr i)))≠0) :
    (((χ.toUnitHom (Units.mk0 (P:ZMod (p (.inr i))) hP))^b (some (.inr i)) none *
      (∏h:H,χ.toUnitHom (primeRowUnits p hc (.inr i) (.inl (h,t)))^
        b (some (.inr i)) (some (.inl h))) *
      (∏y:Y,χ.toUnitHom (primeRowUnits p hc (.inr i) (.inr y))^
        b (some (.inr i)) (some (.inr y))):ℂˣ):ℂ)=
      oldPrimeSharedRow p i t χ b P := by
  simp only [oldPrimeSharedRow,Units.val_mul,Units.coe_prod,
    Units.val_zpow_eq_zpow_val,MulChar.coe_toUnitHom,Units.val_mk0]
  congr 1
  apply Finset.prod_congr rfl
  intro y _
  by_cases he:y=i
  · subst y; simp [hself]
  · simp [primeRowUnits_coe p hc (.inr i) (.inr y) (by simpa using he)]

theorem prime_shared_character_transport (p:OutputPrimeIndex H Y→ℕ)
    [∀i,Fact (p i).Prime] (hc:Pairwise (fun i j => (p i).Coprime (p j)))
    (i:Y) (χ:MulChar (ZMod (p (.inr i))) ℂ)
    (b:Option (H⊕Y)→Option (H⊕Y)→ℤ)
    (hself:b (some (.inr i)) (some (.inr i))=0) (νL νR:ℂˣ) (P:ℤ)
    (hP:(P:ZMod (p (.inr i)))≠0) :
    ((νL:ℂ)*oldPrimeSharedRow p i true χ b P)/
      ((νR:ℂ)*oldPrimeSharedRow p i false χ b P) =
      ((νL:ℂ)/(νR:ℂ))*
        ∏h:OutputPrimeIndex H Y,χ (p h)^transferGraph b (.inr i) h := by
  let z := fun h => χ.toUnitHom (primeRowUnits p hc (.inr i) h)
  let R (t:Bool) : ℂˣ :=
    (χ.toUnitHom (Units.mk0 (P:ZMod (p (.inr i))) hP))^b (some (.inr i)) none *
      (∏h:H,z (.inl (h,t))^b (some (.inr i)) (some (.inl h))) *
      (∏y:Y,z (.inr y)^b (some (.inr i)) (some (.inr y)))
  have hrow (t:Bool) : (R t:ℂ)=oldPrimeSharedRow p i t χ b P :=
    sharedUnitRow_coe p hc i t χ b hself P hP
  have hh : (νL*R true)/(νR*R false)=
      (νL/νR)*rowProduct (transferGraph b (.inr i)) z := by
    simpa only [R,mul_assoc] using shared_row_transport b i νL νR
      (χ.toUnitHom (Units.mk0 (P:ZMod (p (.inr i))) hP)) z
  have hb : transferGraph b (.inr i) (.inr i)=0 := rfl
  calc
    _ = ((νL:ℂ)*(R true:ℂ))/((νR:ℂ)*(R false:ℂ)) := by rw [hrow,hrow]
    _ = (((νL*R true)/(νR*R false):ℂˣ):ℂ) := by
      simp only [Units.val_div_eq_div_val,Units.val_mul]
    _ = (((νL/νR)*rowProduct (transferGraph b (.inr i)) z:ℂˣ):ℂ) :=
      congrArg (fun a:ℂˣ => (a:ℂ)) hh
    _ = _ := by
      rw [Units.val_mul,Units.val_div_eq_div_val,
        primeRowUnits_character_row p hc (.inr i) χ _ hb]

end Ostmann.Characters.Template

end

end OAI
