import OAI.NumberTheory.Ostmann.Characters.TemplatePhaseProducts
import OAI.NumberTheory.Ostmann.Characters.TemplatePhaseTransportCore

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
variable {K S:Type*} [Fintype K] [Fintype S] [DecidableEq K] [DecidableEq S]

def survivingPrimeRow (r:S→ℕ) [∀i,Fact (r i).Prime]
    (i:S) (χ:MulChar (ZMod (r i)) ℂ) (a:ZMod (r i))
    (ν:ℂ) (b:S→ℤ) (bP:ℤ) (P:ℕ) (v:ℤ) : ℂ :=
  translatedAdditivePhase a (v:ZMod (r i))
    ((P:ZMod (r i))*Construction.otherProduct r i)*
    (ν*χ (P:ZMod (r i))^bP*(∏j:S,χ (r j)^b j))

theorem otherProduct_survivor (q:K→ℕ) (r:S→ℕ) (i:S) (hi:r i≠0) :
    Construction.otherProduct (Sum.elim q r) (.inr i)=(∏k,q k)*Construction.otherProduct r i := by
  apply mul_right_cancel₀ hi
  change Construction.otherProduct (Sum.elim q r) (.inr i)*Sum.elim q r (.inr i)=_
  rw [Construction.otherProduct,Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
  simp only [Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr]
  rw [mul_assoc,Construction.otherProduct,Finset.prod_erase_mul _ _ (Finset.mem_univ _)]

omit [DecidableEq K] [DecidableEq S] in
theorem incoming_character_collapse [DecidableEq K] [DecidableEq S] (q:K→ℕ) (r:S→ℕ) (i:S)
    (χ:MulChar (ZMod (r i)) ℂ) (B:K⊕S→ℤ) (bP:ℤ)
    (hP:∀k:K,B (.inl k)=bP) :
    (∏j:K⊕S,χ ((Sum.elim q r j:ℕ):ZMod (r i))^B j)=
      χ (∏k,q k)^bP*(∏j:S,χ (r j)^B (.inr j)) := by
  simp only [Fintype.prod_sum_type,Sum.elim_inl,Sum.elim_inr,hP,
    map_prod,← Finset.prod_zpow]

theorem surviving_prime_row_factorization (q:K→ℕ) (r:S→ℕ) [∀i,Fact (r i).Prime]
    (i:S) (χ:MulChar (ZMod (r i)) ℂ) (a:ZMod (r i)) (ν:ℂ)
    (B:K⊕S→ℤ) (bP:ℤ) (hP:∀k:K,B (.inl k)=bP) (v:ℤ) :
    ZMod.stdAddChar (-(a*(show ZMod (r i) from Construction.crtFrequency (Sum.elim q r) v (.inr i))))*
      (ν*(∏j:K⊕S,χ ((Sum.elim q r j:ℕ):ZMod (r i))^B j))=
    survivingPrimeRow r i χ a ν (fun j => B (.inr j)) bP (∏k,q k) v := by
  rw [incoming_character_collapse q r i χ B bP hP]
  unfold survivingPrimeRow translatedAdditivePhase Construction.crtFrequency
  rw [otherProduct_survivor q r i (Fact.out : (r i).Prime).ne_zero]
  simp only [Nat.cast_mul,Nat.cast_prod,mul_assoc,div_eq_mul_inv]
  rfl

end Ostmann.Characters.Template

end

end OAI
