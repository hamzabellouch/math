import OAI.NumberTheory.Ostmann.Characters.TemplateInitialPhase
import OAI.NumberTheory.Ostmann.Characters.TemplatePhaseTransport
import OAI.NumberTheory.Ostmann.Characters.TemplatePrimeCharacterTransport
import OAI.NumberTheory.Ostmann.Characters.TemplateSharedCharacterTransport

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
variable {H Y:Type*} [Fintype H] [Fintype Y] [DecidableEq H] [DecidableEq Y]

def transferredUnary (p:OutputPrimeIndex H Y→ℕ) [∀i,Fact (p i).Prime]
    (χ:∀i,MulChar (ZMod (p i)) ℂ)
    (b:Option (H⊕Y)→Option (H⊕Y)→ℤ)
    (ν:H×Bool→ℂˣ) (ξ:Y→Bool→ℂˣ) (s v w:ℤ) : OutputPrimeIndex H Y→ℂ
  | .inl (i,t) => (ν (i,t):ℂ)^copySign t*
      χ (.inl (i,t)) ((signedChildFrequency v w t:ZMod (p (.inl (i,t))))/
        (s:ZMod (p (.inl (i,t)))))^(copySign t*b (some (.inl i)) none)
  | .inr i => (ξ i true:ℂ)/(ξ i false:ℂ)

theorem character_product_transport (p:OutputPrimeIndex H Y→ℕ)
    [∀i,Fact (p i).Prime] (hc:Pairwise (fun i j => (p i).Coprime (p j)))
    (χ:∀i,MulChar (ZMod (p i)) ℂ)
    (b:Option (H⊕Y)→Option (H⊕Y)→ℤ) (hself:∀i,b (some i) (some i)=0)
    (ν:H×Bool→ℂˣ) (ξ:Y→Bool→ℂˣ) (P s v w:ℤ)
    (he:s*P=v*(primeCopyProduct p false:ℤ)-w*(primeCopyProduct p true:ℤ))
    (hP:∀i,(P:ZMod (p i))≠0)
    (hf:∀(i:H)(t:Bool),(signedChildFrequency v w t:ZMod (p (.inl (i,t))))≠0) :
    (∏it:H×Bool,((ν it:ℂ)*oldPrimeCopiedRow p it.1 it.2 (χ (.inl it)) b P)^copySign it.2)*
      (∏i:Y,((ξ i true:ℂ)*oldPrimeSharedRow p i true (χ (.inr i)) b P)/
        ((ξ i false:ℂ)*oldPrimeSharedRow p i false (χ (.inr i)) b P)) =
      primeGraphPhase (transferGraph b) p χ (transferredUnary p χ b ν ξ s v w) := by
  have hcopy (it:H×Bool) := prime_copied_character_transport p hc it.1 it.2
    (χ (.inl it)) b (hself (.inl it.1)) (ν it) P s v w he (hP _) (hf it.1 it.2)
  have hshared (i:Y) := prime_shared_character_transport p hc i (χ (.inr i))
    b (hself (.inr i)) (ξ i true) (ξ i false) P (hP _)
  simp_rw [hcopy,hshared]
  simp only [primeGraphPhase,Fintype.prod_sum_type,transferredUnary]

theorem complete_phase_product_transport (p:OutputPrimeIndex H Y→ℕ)
    [∀i,Fact (p i).Prime] (hc:Pairwise (fun i j => (p i).Coprime (p j)))
    (χ:∀i,MulChar (ZMod (p i)) ℂ) (a:∀i,ZMod (p i))
    (b:Option (H⊕Y)→Option (H⊕Y)→ℤ) (hself:∀i,b (some i) (some i)=0)
    (ν:H×Bool→ℂˣ) (ξ:Y→Bool→ℂˣ) (P s v w:ℤ)
    (he:s*P=v*(primeCopyProduct p false:ℤ)-w*(primeCopyProduct p true:ℤ))
    (hP:∀i,(P:ZMod (p i))≠0)
    (hf:∀(i:H)(t:Bool),(signedChildFrequency v w t:ZMod (p (.inl (i,t))))≠0) :
    ((∏i:H,leftTranslation p a P v i)*conj (∏i:H,rightTranslation p a P w i)*
      (∏i:Y,outsideTranslation p a P v true i*conj (outsideTranslation p a P w false i)))*
    ((∏it:H×Bool,((ν it:ℂ)*oldPrimeCopiedRow p it.1 it.2 (χ (.inl it)) b P)^copySign it.2)*
      (∏i:Y,((ξ i true:ℂ)*oldPrimeSharedRow p i true (χ (.inr i)) b P)/
        ((ξ i false:ℂ)*oldPrimeSharedRow p i false (χ (.inr i)) b P))) =
    crtPhase p a s*primeGraphPhase (transferGraph b) p χ
      (transferredUnary p χ b ν ξ s v w) := by
  rw [translation_product_transport p hc a P s v w he hP,
    character_product_transport p hc χ b hself ν ξ P s v w he hP hf]

end Ostmann.Characters.Template

end

end OAI
