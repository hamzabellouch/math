import OAI.NumberTheory.Ostmann.Characters.TemplatePhaseProduct
import OAI.NumberTheory.Ostmann.Characters.TemplatePhaseRowNorm

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
variable {H Y:Type*} [Fintype H] [Fintype Y] [DecidableEq H] [DecidableEq Y]

theorem copied_phase_conjugate (p:OutputPrimeIndex H Y→ℕ) [∀i,Fact (p i).Prime]
    (hc:Pairwise (fun i j => (p i).Coprime (p j))) (χ:∀i,MulChar (ZMod (p i)) ℂ)
    (b:Option (H⊕Y)→Option (H⊕Y)→ℤ) (hself:∀i,b (some i) (some i)=0)
    (ν:H×Bool→ℂˣ) (hν:∀it,‖(ν it:ℂ)‖=1) (P:ℤ) (hP:∀i,(P:ZMod (p i))≠0) :
    (∏it:H×Bool,((ν it:ℂ)*oldPrimeCopiedRow p it.1 it.2 (χ (.inl it)) b P)^copySign it.2)=
    (∏i:H,(ν (i,true):ℂ)*oldPrimeCopiedRow p i true (χ (.inl (i,true))) b P)*
      conj (∏i:H,(ν (i,false):ℂ)*oldPrimeCopiedRow p i false (χ (.inl (i,false))) b P) := by
  have hn (i:H) : ‖(ν (i,false):ℂ)*oldPrimeCopiedRow p i false (χ (.inl (i,false))) b P‖=1 := by
    rw [norm_mul,hν,norm_oldPrimeCopiedRow p hc i false _ b (hself _) P (hP _),one_mul]
  simp only [Fintype.prod_prod_type,Fintype.prod_bool,copySign,ite_true,Bool.false_eq_true,
    ite_false,zpow_one,zpow_neg_one]
  simp_rw [Complex.inv_eq_conj (hn _)]
  rw [Finset.prod_mul_distrib,map_prod]

theorem character_product_conjugate_transport (p:OutputPrimeIndex H Y→ℕ)
    [∀i,Fact (p i).Prime] (hc:Pairwise (fun i j => (p i).Coprime (p j)))
    (χ:∀i,MulChar (ZMod (p i)) ℂ)
    (b:Option (H⊕Y)→Option (H⊕Y)→ℤ) (hself:∀i,b (some i) (some i)=0)
    (ν:H×Bool→ℂˣ) (hν:∀it,‖(ν it:ℂ)‖=1)
    (ξ:Y→Bool→ℂˣ) (hξ:∀i t,‖(ξ i t:ℂ)‖=1) (P s v w:ℤ)
    (he:s*P=v*(primeCopyProduct p false:ℤ)-w*(primeCopyProduct p true:ℤ))
    (hP:∀i,(P:ZMod (p i))≠0)
    (hf:∀(i:H)(t:Bool),(signedChildFrequency v w t:ZMod (p (.inl (i,t))))≠0) :
    ((∏i:H,(ν (i,true):ℂ)*oldPrimeCopiedRow p i true (χ (.inl (i,true))) b P)*
      conj (∏i:H,(ν (i,false):ℂ)*oldPrimeCopiedRow p i false (χ (.inl (i,false))) b P))*
    (∏i:Y,((ξ i true:ℂ)*oldPrimeSharedRow p i true (χ (.inr i)) b P)*
      conj ((ξ i false:ℂ)*oldPrimeSharedRow p i false (χ (.inr i)) b P)) =
    primeGraphPhase (transferGraph b) p χ (transferredUnary p χ b ν ξ s v w) := by
  rw [← copied_phase_conjugate p hc χ b hself ν hν P hP]
  have hn (i:Y) : ‖(ξ i false:ℂ)*oldPrimeSharedRow p i false (χ (.inr i)) b P‖=1 := by
    rw [norm_mul,hξ,norm_oldPrimeSharedRow p hc i false _ b (hself _) P (hP _),one_mul]
  simp_rw [← Complex.inv_eq_conj (hn _),← div_eq_mul_inv]
  exact character_product_transport p hc χ b hself ν ξ P s v w he hP hf

end Ostmann.Characters.Template

end

end OAI
