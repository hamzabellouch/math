import OAI.NumberTheory.Ostmann.Characters.TemplateRegularPhase

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
variable {K H Y:Type*} [Fintype K] [Fintype H] [Fintype Y]
  [DecidableEq K] [DecidableEq H] [DecidableEq Y]

abbrev InputPrimeIndex (K H Y:Type*) := K⊕(H⊕Y)

def inputCopiedProduct (p:InputPrimeIndex K H Y→ℕ) : ℕ := ∏h:H,p (.inr (.inl h))
def inputOutsideProduct (p:InputPrimeIndex K H Y→ℕ) : ℕ := ∏y:Y,p (.inr (.inr y))
def pivotOutsideComplement (p:InputPrimeIndex K H Y→ℕ) (i:K) : ℕ :=
  Construction.otherProduct (fun k:K => p (.inl k)) i * inputOutsideProduct p

theorem otherProduct_pivot (p:InputPrimeIndex K H Y→ℕ) (i:K) (hp:p (.inl i)≠0) :
    Construction.otherProduct p (.inl i)=pivotOutsideComplement p i*inputCopiedProduct p := by
  apply mul_right_cancel₀ hp
  rw [Construction.otherProduct,Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
  simp only [Fintype.prod_sum_type]
  unfold pivotOutsideComplement inputCopiedProduct inputOutsideProduct
  calc
    _ = (Construction.otherProduct (fun k:K => p (.inl k)) i*p (.inl i))*
        ((∏h:H,p (.inr (.inl h)))*(∏y:Y,p (.inr (.inr y)))) := by
      rw [Construction.otherProduct,Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
    _ = _ := by ring

def outgoingPivotFactor {p:ℕ} [Fact p.Prime] (χ:MulChar (ZMod p) ℂ)
    (a:ZMod p) (κ:ℂ) (ε:ℤ) (D:ℕ) (u:ZMod p) : ℂ :=
  ZMod.stdAddChar (-(a*(u/(D:ZMod p))))*(κ*χ ((D:ZMod p)/u)^ε)

theorem outgoing_pivot_factorization (p:InputPrimeIndex K H Y→ℕ)
    [∀i,Fact (p i).Prime] (i:K) (χ:MulChar (ZMod (p (.inl i))) ℂ)
    (a:ZMod (p (.inl i))) (κ:ℂ) (ε:ℤ)
    (B:InputPrimeIndex K H Y→ℤ) (hself:B (.inl i)=0)
    (hreg:∀j,j≠Sum.inl i→B j=ε) (v:ℤ) :
    ZMod.stdAddChar (-(a*Construction.crtFrequency p v (.inl i)))*
      ((κ*χ (v:ZMod (p (.inl i)))^(-ε))*∏j,χ (p j)^B j)=
    outgoingPivotFactor χ a κ ε (pivotOutsideComplement p i)
      ((v:ZMod (p (.inl i)))/(inputCopiedProduct p:ZMod (p (.inl i)))) := by
  rw [regular_frequency_row p (.inl i) χ B ε hself hreg]
  unfold outgoingPivotFactor Construction.crtFrequency
  rw [otherProduct_pivot p i (Fact.out : (p (.inl i)).Prime).ne_zero]
  simp only [Nat.cast_mul,div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring_nf

end Ostmann.Characters.Template

end

end OAI
