import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTelescoping
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTransport

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSupportTransport
open SymbolicHistory TemplateSupportRemoval TemplateOneSidedSupportTelescoping
open TemplateOneSidedRelabel Template Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem eventually_reindexed_outside_enlargement (C z : ℝ) (d : ℕ) {α c : ℝ}
    (hC : 0≤C) (hz : 0≤z) (hα : 0<α) (hc : 0<c) :
    ∀ᶠ L : ℝ in atTop,∀ {κ : Type} [Fintype κ] [DecidableEq κ],
    ∀ (width : κ→ℕ) (k : ℕ) (B₀ V₀ : (j:ℕ)→State k (j+1)→ℤ)
      (extra : (j:ℕ)→ℤ→State k j→HistoryReconstruction.Tree j→Prop)
      (j : ℕ) (o : SampleOrigins k j κ) (s : ℤ)
      (e : Expressions (ι:=(Σr:κ,Fin (width r))) k j) (t : HistoryReconstruction.Tree j)
      (S : (Σr:κ,Fin (width r))→Finset ℤ) (μ : (Σr:κ,Fin (width r))→ℤ→ℝ)
      (B : (Σr:κ,Fin (width r))→Finset ℕ)
      (_hS : ∀i,S i=(B i).image (fun p:ℕ=>(p:ℤ)))
      (π : Equiv.Perm (Σr:κ,Fin (width r)))
      (H A : ℝ) (_hH : Real.log 2≤H) (_hA : 0≤A)
      (_hμ : ∀i v,v∈S i → 0≤μ i v) (_hmass : ∀i,∑v∈S i,μ i v=1)
      (_hatom : ∀i v,v∈S i → μ i v≤Real.exp (-c*Real.exp (α*L)))
      (_hprime : ∀i p,p∈B i → p.Prime)
      (Z : ℕ)
      (_hsyntax : ∀i q,q∈actualFamilies k width j o s e t i → q.syntaxSize≤Z)
      (_hfixed : ∀i q,q∈actualFamilies k width j o s e t i → q.FixedLogBound H)
      (_hvars : ∀i v,v∈S i → |(v:ℝ)|≤Real.exp H)
      (mask : ((Σr:κ,Fin (width r))→ℤ)→Bool) (f : ((Σr:κ,Fin (width r))→ℤ)→ℂ)
      (_hf : ∀x,(∀u,x u∈S (π u)) → ‖f x‖≤A)
      (_hgood : ∀x,(∀u,x u∈S (π u)) → ∀u,HistoryReconstruction.Good x (e u))
      (_hfreq : ∀i q,q∈actualFamilies k width j o s e t i →
        ∀x,(∀u,x u∈S (π u)) → mask x=true →
          TransferCoreSupport k B₀ V₀ extra j s (evalExpressions x e) t → q.DivisorsBelow (x i).toNat),
      (2^(j+1):ℝ)≤Real.exp (historyPolynomialCost C z d L) →
      (Z:ℝ)≤Real.exp (historyPolynomialCost C z d L) →
      H≤Real.exp (historyPolynomialCost C z d L) → A≤Real.exp (historyPolynomialCost C z d L) →
      ‖fullProductMean S μ (fun a=>if mask (fun i=>a (π i)) then
          if SampledTransferSupport k (fun r=>∏b,a (π ⟨r,b⟩)) B₀ V₀ extra j o s
            (evalExpressions a (relabelExpressions π e)) t
            then f (fun i=>a (π i)) else 0 else 0) -
        fullProductMean S μ (fun a=>if mask (fun i=>a (π i))=true ∧
          TransferCoreSupport k B₀ V₀ extra j s (evalExpressions a (relabelExpressions π e)) t ∧
          ∀i,familyPolynomial (relabelFamilies π (actualFamilies k width j o s e t)) i
          then f (fun i=>a (π i)) else 0)‖ ≤
        (Fintype.card (Σr:κ,Fin (width r)):ℝ)*Real.exp (-(c/2)*Real.exp (α*L)) := by
  filter_upwards [eventually_actual_outside_enlargement C z d hC hz hα hc] with L hL
  intro κ _ _ width k B₀ V₀ extra j o s e t S μ B hS π H A hH hA hμ hmass
    hatom hprime Z hsyntax hfixed hvars mask f hf hgood hfreq htree hZ hHt hAt
  have hb := hL width k B₀ V₀ extra j o s e t
    (fun i=>S (π i)) (fun i=>μ (π i)) (fun i=>B (π i)) (fun i=>hS (π i))
    H A hH hA (fun i=>hμ (π i)) (fun i=>hmass (π i))
    (fun i=>hatom (π i)) (fun i=>hprime (π i)) Z hsyntax hfixed
    (fun i=>hvars (π i)) mask f hf hgood hfreq htree hZ hHt hAt
  have hp : (∀i,familyPolynomial (relabelFamilies π (actualFamilies k width j o s e t)) i) ↔
      ∀i,∀q∈actualFamilies k width j o s e t i,eraseCoordinate i q.numerator≠0 := by
    constructor
    · intro h i
      exact (familyPolynomial_relabel π _ i).mp (h (π i))
    · intro h i
      obtain ⟨u,rfl⟩ := π.surjective i
      exact (familyPolynomial_relabel π _ u).mpr (h u)
  have hleft := fullProductMean_reindex π S μ
    (fun x=>if mask x then
      if SampledTransferSupport k (fun r=>∏b,x ⟨r,b⟩) B₀ V₀ extra j o s (evalExpressions x e) t
        then f x else 0 else 0)
  have hright := fullProductMean_reindex π S μ
    (fun x=>if mask x=true ∧
      TransferCoreSupport k B₀ V₀ extra j s (evalExpressions x e) t ∧
      ∀i,∀q∈actualFamilies k width j o s e t i,eraseCoordinate i q.numerator≠0 then f x else 0)
  have he := congrArg (fun z : ℂ=>‖z‖)
    (congrArg₂ (fun u v : ℂ=>u-v) hleft.symm hright.symm)
  simpa only [relabelExpressions_eval,hp] using he.trans_le hb

end Ostmann.Characters.TemplateOneSidedSupportTransport

end

end OAI
