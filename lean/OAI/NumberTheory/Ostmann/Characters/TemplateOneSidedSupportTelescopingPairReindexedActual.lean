import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTelescopingPairBudget
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTelescopingPairLiteral
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTelescopingPairReindexed

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSupportTelescoping
open SymbolicHistory TemplateSupportRemoval Template Filter
open TemplateOneSidedSupportTransport TemplateOneSidedRelabel
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

theorem eventually_reindexed_weight_pair_outside_enlargement (C z : ℝ) (d j : ℕ) (W Wc : ℝ)
    (hpairC : fixedPairBound j W Wc≤C) {α c : ℝ}
    (hC : 0≤C) (hz : 0≤z) (hα : 0<α) (hc : 0<c) :
    ∀ᶠ L : ℝ in atTop,∀ {κ : Type} [Fintype κ] [DecidableEq κ],
    ∀ (width : κ→ℕ) (k : ℕ) (B₀ V₀ : (j:ℕ)→State k (j+1)→ℤ)
      (extra : (j:ℕ)→ℤ→State k j→HistoryReconstruction.Tree j→Prop)
      (o : Bool→SampleOrigins k j κ) (s : Bool→ℤ)
      (e : Bool→Expressions (ι:=(Σr:κ,Fin (width r))) k j)
      (t : Bool→HistoryReconstruction.Tree j)
      (S : (Σr:κ,Fin (width r))→Finset ℤ) (μ : (Σr:κ,Fin (width r))→ℤ→ℝ)
      (B : (Σr:κ,Fin (width r))→Finset ℕ)
      (_hS : ∀i,S i=(B i).image (fun p:ℕ=>(p:ℤ)))
      (π : Bool→Equiv.Perm (Σr:κ,Fin (width r)))
      (H : ℝ) (_hH : Real.log 2≤H)
      (_hμ : ∀i v,v∈S i → 0≤μ i v) (_hmass : ∀i,∑v∈S i,μ i v=1)
      (_hatom : ∀i v,v∈S i → μ i v≤Real.exp (-c*Real.exp (α*L)))
      (_hprime : ∀i p,p∈B i → p.Prime)
      (Z : ℕ)
      (_hsyntax : ∀r i q,q∈actualFamilies k width j (o r) (s r) (e r) (t r) i → q.syntaxSize≤Z)
      (_hfixed : ∀r i q,q∈actualFamilies k width j (o r) (s r) (e r) (t r) i → q.FixedLogBound H)
      (_hvars : ∀i v,v∈S i → |(v:ℝ)|≤Real.exp H)
      (mask : ((Σr:κ,Fin (width r))→ℤ)→Bool)
      (wmask : (j:ℕ)→ℤ→State k j→Prop) (X Δ T : ℝ) (_hX : 0<X) (_hΔ : 0≤Δ)
      (P : ((Σr:κ,Fin (width r))→ℤ)→ℤ)
      (phase : ((Σr:κ,Fin (width r))→ℤ)→ℂ)
      (_hphase : ∀x,(∀u,x u∈S u) → ‖phase x‖≤1)
      (_hgood : ∀r x,(∀u,x u∈S (π r u)) → ∀u,HistoryReconstruction.Good x (e r u))
      (_hfreq : ∀r i q,q∈actualFamilies k width j (o r) (s r) (e r) (t r) i →
        ∀x,(∀u,x u∈S (π r u)) →
          TransferCoreSupport k B₀ V₀ extra j (s r) (evalExpressions x (e r)) (t r) →
            q.DivisorsBelow (x i).toNat),
      (2^(j+1):ℝ)≤Real.exp (historyPolynomialCost C z d L) →
      (Z:ℝ)≤Real.exp (historyPolynomialCost C z d L) →
      H≤Real.exp (historyPolynomialCost C z d L) →
      ‖fullProductMean S μ (fun x=>if mask x=true ∧
          ∀r,SampledTransferSupport k (fun u=>∏b,x (π r ⟨u,b⟩)) B₀ V₀ extra j
            (o r) (s r) (evalExpressions x (relabelExpressions (π r) (e r))) (t r) then pairedHistoryMultiplier k wmask X Δ W T Wc j s
            (fun r x=>evalExpressions x (relabelExpressions (π r) (e r))) t P phase x else 0) -
        fullProductMean S μ (fun x=>if mask x=true ∧
          (∀r,TransferCoreSupport k B₀ V₀ extra j (s r)
            (evalExpressions x (relabelExpressions (π r) (e r))) (t r)) ∧
          (∀r i,familyPolynomial
            (relabelFamilies (π r) (actualFamilies k width j (o r) (s r) (e r) (t r))) i) then pairedHistoryMultiplier k wmask X Δ W T Wc j s
            (fun r x=>evalExpressions x (relabelExpressions (π r) (e r))) t P phase x else 0)‖ ≤
        (2*(Fintype.card (Σr:κ,Fin (width r)):ℝ))*Real.exp (-(c/2)*Real.exp (α*L)) := by
  filter_upwards [eventually_reindexed_pair_outside_enlargement C z d hC hz hα hc] with L hL
  intro κ _ _ width k B₀ V₀ extra o s e t S μ B hS π H hH hμ hmass hatom hprime
    Z hsyntax hfixed hvars mask wmask X Δ T hX hΔ P phase hphase hgood hfreq htree hZ hHt
  exact hL width k B₀ V₀ extra j o s e t S μ B hS π H (fixedPairBound j W Wc) hH
    (fixedPairBound_nonneg j W Wc) hμ hmass hatom hprime Z hsyntax hfixed hvars mask
    (pairedHistoryMultiplier k wmask X Δ W T Wc j s (fun r x=>evalExpressions x (relabelExpressions (π r) (e r))) t P phase)
    (fun x hx=>pairedHistoryMultiplier_norm_le_fixed k wmask X Δ W T Wc hX hΔ j s
      (fun r x=>evalExpressions x (relabelExpressions (π r) (e r))) t P phase x (hphase x hx))
    hgood hfreq htree hZ hHt (fixedPairBound_le_budget j W Wc z L d hpairC)

end Ostmann.Characters.TemplateOneSidedSupportTelescoping

end

end OAI
