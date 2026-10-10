import OAI.NumberTheory.Ostmann.Characters.TemplatePivotUnits

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
variable {H Y:Type*} [Fintype H] [Fintype Y] [DecidableEq H] [DecidableEq Y]

private theorem unit_character_power {ι:Type*} [DecidableEq ι] (p:ι→ℕ)
    (hc:Pairwise (fun i j => (p i).Coprime (p j))) (i j:ι)
    (χ:MulChar (ZMod (p i)) ℂ) (e:ℤ) (he:j=i→e=0) :
    (((χ.toUnitHom (primeRowUnits p hc i j))^e:ℂˣ):ℂ)=χ (p j)^e := by
  by_cases h:j=i
  · simp [he h]
  · simp [Units.val_zpow_eq_zpow_val,primeRowUnits_coe p hc i j h]

def oldPrimeCopiedRow (p:OutputPrimeIndex H Y→ℕ) (i:H) (t:Bool)
    (χ:MulChar (ZMod (p (.inl (i,t)))) ℂ)
    (b:Option (H⊕Y)→Option (H⊕Y)→ℤ) (P:ℤ) : ℂ :=
    χ (P:ZMod (p (.inl (i,t))))^b (some (.inl i)) none *
      (∏h:H,χ (p (.inl (h,t)))^b (some (.inl i)) (some (.inl h))) *
      (∏y:Y,χ (p (.inr y))^b (some (.inl i)) (some (.inr y)))

private theorem oldCopiedRow_coe (p:OutputPrimeIndex H Y→ℕ)
    [∀i,Fact (p i).Prime] (hc:Pairwise (fun i j => (p i).Coprime (p j)))
    (i:H) (t:Bool) (χ:MulChar (ZMod (p (.inl (i,t)))) ℂ)
    (b:Option (H⊕Y)→Option (H⊕Y)→ℤ)
    (hself:b (some (.inl i)) (some (.inl i))=0) (P:ℤ)
    (hP:(P:ZMod (p (.inl (i,t))))≠0) :
    ((oldCopiedRow b i t (χ.toUnitHom (Units.mk0 (P:ZMod (p (.inl (i,t)))) hP))
      (fun h => χ.toUnitHom (primeRowUnits p hc (.inl (i,t)) h)):ℂˣ):ℂ) =
      oldPrimeCopiedRow p i t χ b P := by
  simp only [oldCopiedRow,oldPrimeCopiedRow,Units.val_mul,Units.coe_prod,
    Units.val_zpow_eq_zpow_val,MulChar.coe_toUnitHom,Units.val_mk0]
  congr 2
  · apply Finset.prod_congr rfl
    intro h _
    by_cases he:h=i
    · subst h; simp [hself]
    · simp [primeRowUnits_coe p hc (.inl (i,t)) (.inl (h,t)) (by simpa using he)]

theorem prime_copied_character_transport (p:OutputPrimeIndex H Y→ℕ)
    [∀i,Fact (p i).Prime] (hc:Pairwise (fun i j => (p i).Coprime (p j)))
    (i:H) (t:Bool) (χ:MulChar (ZMod (p (.inl (i,t)))) ℂ)
    (b:Option (H⊕Y)→Option (H⊕Y)→ℤ)
    (hself:b (some (.inl i)) (some (.inl i))=0) (ν:ℂˣ) (P s v w:ℤ)
    (he:s*P=v*(primeCopyProduct p false:ℤ)-w*(primeCopyProduct p true:ℤ))
    (hP:(P:ZMod (p (.inl (i,t))))≠0)
    (hf:(signedChildFrequency v w t:ZMod (p (.inl (i,t))))≠0) :
    ((ν:ℂ)*oldPrimeCopiedRow p i t χ b P)^copySign t =
      ((ν:ℂ)^copySign t*
        χ ((signedChildFrequency v w t:ZMod (p (.inl (i,t))))/(s:ZMod (p (.inl (i,t)))))^
          (copySign t*b (some (.inl i)) none))*
        ∏h:OutputPrimeIndex H Y,χ (p h)^transferGraph b (.inl (i,t)) h := by
  let Pu := Units.mk0 (P:ZMod (p (.inl (i,t)))) hP
  let u := Units.mk0 (signedChildFrequency v w t:ZMod (p (.inl (i,t)))) hf /
    Units.mk0 (s:ZMod (p (.inl (i,t)))) (reversal_root_residue_ne_zero p hc P s v w he i t hf)
  let z := fun h => χ.toUnitHom (primeRowUnits p hc (.inl (i,t)) h)
  have hp : χ.toUnitHom Pu=χ.toUnitHom u*∏h:H,z (.inl (h,!t)) := by
    have hh := congrArg χ.toUnitHom (reversal_pivot_units p hc P s v w he i t hP hf)
    simpa only [map_mul,map_prod] using hh
  have hh := congrArg (fun a:ℂˣ => (a:ℂ))
    (copied_row_transport b i t ν (χ.toUnitHom Pu) (χ.toUnitHom u) z hself hp)
  have hb : transferGraph b (.inl (i,t)) (.inl (i,t))=0 := by simp [transferGraph]
  rw [Units.val_zpow_eq_zpow_val,Units.val_mul,oldCopiedRow_coe p hc i t χ b hself P hP,
    Units.val_mul,Units.val_mul,Units.val_zpow_eq_zpow_val,
    Units.val_zpow_eq_zpow_val,
    primeRowUnits_character_row p hc (.inl (i,t)) χ _ hb] at hh
  simpa only [Pu,u,MulChar.coe_toUnitHom,Units.val_div_eq_div_val,Units.val_mk0] using hh

end Ostmann.Characters.Template

end

end OAI
