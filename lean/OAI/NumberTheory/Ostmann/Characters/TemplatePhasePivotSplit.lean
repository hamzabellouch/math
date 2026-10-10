import OAI.NumberTheory.Ostmann.Characters.TemplateInitialPhase
import OAI.NumberTheory.Ostmann.Characters.TemplateOutgoingProduct
import OAI.NumberTheory.Ostmann.Characters.TemplatePivotCollapse

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template

def completePrimePhase {ι:Type*} [Fintype ι] [DecidableEq ι]
    (p:ι→ℕ) [∀i,Fact (p i).Prime] (χ:∀i,MulChar (ZMod (p i)) ℂ)
    (a:∀i,ZMod (p i)) (ν:ι→ℂ) (B:ι→ι→ℤ) (v:ℤ) : ℂ :=
  (∏i,ZMod.stdAddChar (-(a i*Construction.crtFrequency p v i)))*primeGraphPhase B p χ ν

variable {K H Y:Type*} [Fintype K] [Fintype H] [Fintype Y]
  [DecidableEq K] [DecidableEq H] [DecidableEq Y]

theorem complete_phase_pivot_split (p:InputPrimeIndex K H Y→ℕ)
    [∀i,Fact (p i).Prime] (hc:Pairwise (fun i j => (p i).Coprime (p j)))
    (χ:∀i,MulChar (ZMod (p i)) ℂ) (a:∀i,ZMod (p i))
    (ν:InputPrimeIndex K H Y→ℂ) (B:InputPrimeIndex K H Y→InputPrimeIndex K H Y→ℤ)
    (κ:K→ℂ) (ε:K→ℤ) (bP:H⊕Y→ℤ) (v:ℤ)
    (hν:∀i:K,ν (.inl i)=κ i*χ (.inl i) (v:ZMod (p (.inl i)))^(-ε i))
    (hself:∀i:K,B (.inl i) (.inl i)=0)
    (hreg:∀(i:K)j,j≠Sum.inl i→B (.inl i) j=ε i)
    (hcol:∀(i:H⊕Y)(k:K),B (.inr i) (.inl k)=bP i) :
    completePrimePhase p χ a ν B v =
    outgoingPivotProduct (fun i:K => p (.inl i)) (fun i => χ (.inl i)) (fun i => a (.inl i))
      κ ε (inputOutsideProduct p)
      (groupedPivotResidue (fun i:K => p (.inl i)) (inputCopiedProduct p)
        (copiedProduct_coprime_pivot p hc) v)*
    (∏i:H⊕Y,survivingPrimeRow (fun j:H⊕Y => p (.inr j)) i (χ (.inr i)) (a (.inr i))
      (ν (.inr i)) (fun j => B (.inr i) (.inr j)) (bP i) (∏k:K,p (.inl k)) v) := by
  have hp : Sum.elim (fun k:K => p (.inl k)) (fun i:H⊕Y => p (.inr i))=p := by
    funext i
    cases i <;> rfl
  have hremain (i:H⊕Y) :
      ZMod.stdAddChar (-(a (.inr i)*Construction.crtFrequency p v (.inr i)))*
        (ν (.inr i)*(∏j,χ (.inr i) (p j)^B (.inr i) j)) =
      survivingPrimeRow (fun j:H⊕Y => p (.inr j)) i (χ (.inr i)) (a (.inr i))
        (ν (.inr i)) (fun j => B (.inr i) (.inr j)) (bP i) (∏k:K,p (.inl k)) v := by
    simpa only [Construction.crtFrequency,hp] using! surviving_prime_row_factorization
      (fun k:K => p (.inl k)) (fun j:H⊕Y => p (.inr j)) i (χ (.inr i)) (a (.inr i))
      (ν (.inr i)) (B (.inr i)) (bP i) (hcol i) v
  unfold completePrimePhase primeGraphPhase
  rw [← Finset.prod_mul_distrib,Fintype.prod_sum_type]
  simp_rw [hν,hremain]
  rw [outgoing_pivot_product_factorization p hc (fun i => χ (.inl i)) (fun i => a (.inl i))
    κ ε (fun i => B (.inl i)) hself hreg v]

end Ostmann.Characters.Template

end

end OAI
