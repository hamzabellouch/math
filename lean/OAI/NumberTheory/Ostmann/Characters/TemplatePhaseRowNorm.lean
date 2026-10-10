import OAI.NumberTheory.Ostmann.Characters.MixedIndicator
import OAI.NumberTheory.Ostmann.Characters.TemplatePrimeCharacterTransport
import OAI.NumberTheory.Ostmann.Characters.TemplateSharedCharacterTransport

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template

theorem norm_prime_character_power {ι:Type*} [DecidableEq ι] (p:ι→ℕ)
    [∀i,Fact (p i).Prime] (hc:Pairwise (fun i j => (p i).Coprime (p j)))
    (i j:ι) (χ:MulChar (ZMod (p i)) ℂ) (e:ℤ) (he:j=i→e=0) :
    ‖χ (p j)^e‖=1 := by
  by_cases h:j=i
  · simp [he h]
  · rw [norm_zpow,norm_character_of_ne_zero χ
      (((ZMod.isUnit_iff_coprime _ _).mpr (hc h)).ne_zero),one_zpow]

variable {H Y:Type*} [Fintype H] [Fintype Y] [DecidableEq H] [DecidableEq Y]

theorem norm_oldPrimeCopiedRow (p:OutputPrimeIndex H Y→ℕ)
    [∀i,Fact (p i).Prime] (hc:Pairwise (fun i j => (p i).Coprime (p j)))
    (i:H) (t:Bool) (χ:MulChar (ZMod (p (.inl (i,t)))) ℂ)
    (b:Option (H⊕Y)→Option (H⊕Y)→ℤ)
    (hself:b (some (.inl i)) (some (.inl i))=0) (P:ℤ)
    (hP:(P:ZMod (p (.inl (i,t))))≠0) :
    ‖oldPrimeCopiedRow p i t χ b P‖=1 := by
  have hcopy (h:H) : ‖χ (p (.inl (h,t)))^b (some (.inl i)) (some (.inl h))‖=1 := by
    apply norm_prime_character_power p hc (.inl (i,t)) (.inl (h,t)) χ
    intro he
    have hh : h=i := by simpa using he
    subst h
    exact hself
  have hshared (y:Y) : ‖χ (p (.inr y))^b (some (.inl i)) (some (.inr y))‖=1 := by
    apply norm_prime_character_power p hc (.inl (i,t)) (.inr y) χ
    simp
  simp only [oldPrimeCopiedRow,norm_mul,norm_prod,hcopy,hshared,
    norm_zpow,norm_character_of_ne_zero χ hP,one_zpow,Finset.prod_const_one,one_mul]

theorem norm_oldPrimeSharedRow (p:OutputPrimeIndex H Y→ℕ)
    [∀i,Fact (p i).Prime] (hc:Pairwise (fun i j => (p i).Coprime (p j)))
    (i:Y) (t:Bool) (χ:MulChar (ZMod (p (.inr i))) ℂ)
    (b:Option (H⊕Y)→Option (H⊕Y)→ℤ)
    (hself:b (some (.inr i)) (some (.inr i))=0) (P:ℤ)
    (hP:(P:ZMod (p (.inr i)))≠0) :
    ‖oldPrimeSharedRow p i t χ b P‖=1 := by
  have hcopy (h:H) : ‖χ (p (.inl (h,t)))^b (some (.inr i)) (some (.inl h))‖=1 := by
    apply norm_prime_character_power p hc (.inr i) (.inl (h,t)) χ
    simp
  have hshared (y:Y) : ‖χ (p (.inr y))^b (some (.inr i)) (some (.inr y))‖=1 := by
    apply norm_prime_character_power p hc (.inr i) (.inr y) χ
    intro he
    have hh : y=i := by simpa using he
    subst y
    exact hself
  simp only [oldPrimeSharedRow,norm_mul,norm_prod,hcopy,hshared,
    norm_zpow,norm_character_of_ne_zero χ hP,one_zpow,Finset.prod_const_one,one_mul]

end Ostmann.Characters.Template

end

end OAI
