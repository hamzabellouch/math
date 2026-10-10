import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationPrimePriors

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators SchwartzMap
namespace Ostmann.Characters.TemplateOneSidedCancellation
open Construction Preliminaries PrimeDyadicCover TemplateOneSidedPrior Filter
open Template.OneSidedPhase

def OriginalPrimePriorBound (τ : Type) [Fintype τ]
    (C z c : ℝ) (d : ℕ) (α β γLong βLong δ L : ℝ) : Prop :=
    ∀ {A : ℕ} {σ : Type} [Fintype σ],
    ∀ (Elong Eshort : Finset (PrimeUpTo A))
      (hElong : 0 < primeShellMass Elong) (hEshort : 0 < primeShellMass Eshort)
      (ρ : 𝓢(ℝ,ℂ)) (Q : ℕ) (_hQ : 0 < Q)
      (χ : ∀j:↥Eshort,MulChar (ZMod j.val.val) ℂ) (_hχ : ∀j,χ j ≠ 1)
      (U : PrimeUpTo A → ℂ) (V : ↥Eshort → ℂ)
      (F : PrimeUpTo A → ↥Eshort → ℂ)
      (data : Index (sourceUpper βLong L) → Fin Q → ↥Eshort → HistoryPolynomialData σ τ)
      (lo hi : Index (sourceUpper βLong L) → τ → ℝ)
      (M : Index (sourceUpper βLong L) → ℝ),
    Real.exp (-c*L) ≤ primeShellMass Elong →
    Real.exp (-c*L) ≤ primeShellMass Eshort →
    (∀p∈Eshort,Real.exp (α*L) ≤ Real.log p.val) →
    (∀p∈Eshort,Real.log p.val ≤ Real.exp (β*L)) →
    (∀p∈Elong,Real.exp (γLong*L) ≤ Real.log p.val) →
    (∀p∈Elong,Real.log p.val ≤ Real.exp (βLong*L)) →
    (∀p∈Elong,‖U p‖ ≤ 1) → (∀j,‖V j‖ ≤ 1) →
    (Q:ℝ) ≤ Real.exp (historyPolynomialCost C z d L) →
    (∀i,(block Q (sourceUpper βLong L) (sourceNaturals Elong) i).Nonempty →
      (∀r j,(data i r j).Ranges ρ (lo i) (hi i) (M i)) ∧
      (∀r j,((data i r j).degreeCost:ℝ) ≤ Real.exp (historyPolynomialCost C z d L)) ∧
      M i ≤ Real.exp (historyPolynomialCost C z d L) ∧
      3+(∑t:τ,(hi i t-lo i t)) ≤ Real.exp (historyPolynomialCost C z d L)) →
    (∀i,∀p∈Elong,p.val∈block Q (sourceUpper βLong L) (sourceNaturals Elong) i →
      ∀r:Fin Q,∀n:ℕ,Q*n+r.val=p.val → ∀j:↥Eshort,
        (data i r j).weight ρ ((Q*n+r.val:ℕ):ℝ)=F p j) →
    ‖(primeShellPrior Elong hElong).cmean (fun p=>U p*
      ∑j:↥Eshort,((primeShellPrior Eshort hEshort).mass j.val:ℂ)*V j*
        χ j (p.val:ZMod j.val.val)*F p j)‖ ≤ Real.exp (-δ*Real.exp (α*L))

theorem OriginalPrimePriorBound.mono {τ : Type} [Fintype τ]
    {C z c : ℝ} {d : ℕ} {α β γLong βLong δ δ' L : ℝ}
    (h : OriginalPrimePriorBound τ C z c d α β γLong βLong δ L) (hδ : δ' ≤ δ) :
    OriginalPrimePriorBound τ C z c d α β γLong βLong δ' L := by
  intro A σ _ Elong Eshort hElong hEshort ρ Q hQ χ hχ U V F data lo hi M
    hZlong hZshort hshortlo hshorthi hlonglo hlonghi hU hV hQcost hdata hrepr
  exact (h Elong Eshort hElong hEshort ρ Q hQ χ hχ U V F data lo hi M
    hZlong hZshort hshortlo hshorthi hlonglo hlonghi hU hV hQcost hdata hrepr).trans
      (Real.exp_le_exp.mpr (by nlinarith [Real.exp_pos (α*L)]))

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
