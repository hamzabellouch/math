import OAI.NumberTheory.Ostmann.Characters.TemplatePivotResidue

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
variable {K H Y:Type*} [Fintype K] [Fintype H] [Fintype Y]
  [DecidableEq K] [DecidableEq H] [DecidableEq Y]

omit [Fintype Y] [DecidableEq K] [DecidableEq H] [DecidableEq Y] in
theorem copiedProduct_coprime_pivot [Fintype Y] [DecidableEq K] [DecidableEq H]
    [DecidableEq Y] (p:InputPrimeIndex K H Y→ℕ)
    (hc:Pairwise (fun i j => (p i).Coprime (p j))) :
    (inputCopiedProduct p).Coprime (∏i:K,p (.inl i)) := by
  apply Nat.Coprime.prod_left
  intro h _
  apply Nat.Coprime.prod_right
  intro i _
  exact hc (by simp)

theorem outgoing_pivot_product_factorization (p:InputPrimeIndex K H Y→ℕ)
    [∀i,Fact (p i).Prime] (hc:Pairwise (fun i j => (p i).Coprime (p j)))
    (χ:∀i:K,MulChar (ZMod (p (.inl i))) ℂ) (a:∀i:K,ZMod (p (.inl i)))
    (κ:K→ℂ) (ε:K→ℤ) (B:K→InputPrimeIndex K H Y→ℤ)
    (hself:∀i,B i (.inl i)=0) (hreg:∀i j,j≠Sum.inl i→B i j=ε i) (v:ℤ) :
    (∏i:K,ZMod.stdAddChar (-(a i*Construction.crtFrequency p v (.inl i)))*
      ((κ i*χ i (v:ZMod (p (.inl i)))^(-ε i))*∏j,χ i (p j)^B i j)) =
    outgoingPivotProduct (fun i:K => p (.inl i)) χ a κ ε (inputOutsideProduct p)
      (groupedPivotResidue (fun i:K => p (.inl i)) (inputCopiedProduct p)
        (copiedProduct_coprime_pivot p hc) v) := by
  unfold outgoingPivotProduct
  apply Finset.prod_congr rfl
  intro i _
  rw [groupedPivotResidue_cast (fun k:K => p (.inl k)) (inputCopiedProduct p)
    (copiedProduct_coprime_pivot p hc) v i]
  exact outgoing_pivot_factorization p i (χ i) (a i) (κ i) (ε i) (B i)
    (hself i) (hreg i) v

end Ostmann.Characters.Template

end

end OAI
