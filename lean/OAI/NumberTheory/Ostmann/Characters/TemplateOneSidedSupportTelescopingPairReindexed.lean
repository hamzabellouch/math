import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTransportEstimateReindexed

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSupportTelescoping
open SymbolicHistory TemplateSupportRemoval Template Filter
open TemplateOneSidedSupportTransport TemplateOneSidedRelabel
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

private theorem pair_start_indicator (m p q : Prop) (z : ℂ) :
    (if @decide (m∧q) (Classical.propDecidable _) then if p then z else 0 else 0) =
      @ite ℂ (m∧p∧q) (Classical.propDecidable _) z 0 := by
  by_cases hm:m <;> by_cases hp:p <;> by_cases hq:q <;> simp [hm,hp,hq]

private theorem pair_middle_right_indicator (m c p q : Prop) (z : ℂ) :
    (if @decide (m∧c∧p) (Classical.propDecidable _) then if q then z else 0 else 0) =
      @ite ℂ (m∧c∧p∧q) (Classical.propDecidable _) z 0 := by
  by_cases hm:m <;> by_cases hc:c <;> by_cases hp:p <;> by_cases hq:q <;> simp [hm,hc,hp,hq]

private theorem indicator_congr (p q : Prop) (dp : Decidable p) (dq : Decidable q)
    (z : ℂ) (h : p↔q) : @ite ℂ p dp z 0 = @ite ℂ q dq z 0 := by
  by_cases hp:p
  · rw [ite_eq_left hp,ite_eq_left (h.mp hp)]
  · rw [ite_eq_right hp,ite_eq_right (fun hq=>hp (h.mpr hq))]

theorem eventually_reindexed_pair_outside_enlargement (C z : ℝ) (d : ℕ) {α c : ℝ}
    (hC : 0≤C) (hz : 0≤z) (hα : 0<α) (hc : 0<c) :
    ∀ᶠ L : ℝ in atTop,∀ {κ : Type} [Fintype κ] [DecidableEq κ],
    ∀ (width : κ→ℕ) (k : ℕ) (B₀ V₀ : (j:ℕ)→State k (j+1)→ℤ)
      (extra : (j:ℕ)→ℤ→State k j→HistoryReconstruction.Tree j→Prop)
      (j : ℕ) (o : Bool→SampleOrigins k j κ) (s : Bool→ℤ)
      (e : Bool→Expressions (ι:=(Σr:κ,Fin (width r))) k j)
      (t : Bool→HistoryReconstruction.Tree j)
      (S : (Σr:κ,Fin (width r))→Finset ℤ) (μ : (Σr:κ,Fin (width r))→ℤ→ℝ)
      (B : (Σr:κ,Fin (width r))→Finset ℕ)
      (_hS : ∀i,S i=(B i).image (fun p:ℕ=>(p:ℤ)))
      (π : Bool→Equiv.Perm (Σr:κ,Fin (width r)))
      (H A : ℝ) (_hH : Real.log 2≤H) (_hA : 0≤A)
      (_hμ : ∀i v,v∈S i → 0≤μ i v) (_hmass : ∀i,∑v∈S i,μ i v=1)
      (_hatom : ∀i v,v∈S i → μ i v≤Real.exp (-c*Real.exp (α*L)))
      (_hprime : ∀i p,p∈B i → p.Prime)
      (Z : ℕ)
      (_hsyntax : ∀r i q,q∈actualFamilies k width j (o r) (s r) (e r) (t r) i → q.syntaxSize≤Z)
      (_hfixed : ∀r i q,q∈actualFamilies k width j (o r) (s r) (e r) (t r) i → q.FixedLogBound H)
      (_hvars : ∀i v,v∈S i → |(v:ℝ)|≤Real.exp H)
      (mask : ((Σr:κ,Fin (width r))→ℤ)→Bool) (f : ((Σr:κ,Fin (width r))→ℤ)→ℂ)
      (_hf : ∀x,(∀u,x u∈S u) → ‖f x‖≤A)
      (_hgood : ∀r x,(∀u,x u∈S (π r u)) → ∀u,HistoryReconstruction.Good x (e r u))
      (_hfreq : ∀r i q,q∈actualFamilies k width j (o r) (s r) (e r) (t r) i →
        ∀x,(∀u,x u∈S (π r u)) →
          TransferCoreSupport k B₀ V₀ extra j (s r) (evalExpressions x (e r)) (t r) →
            q.DivisorsBelow (x i).toNat),
      (2^(j+1):ℝ)≤Real.exp (historyPolynomialCost C z d L) →
      (Z:ℝ)≤Real.exp (historyPolynomialCost C z d L) →
      H≤Real.exp (historyPolynomialCost C z d L) → A≤Real.exp (historyPolynomialCost C z d L) →
      ‖fullProductMean S μ (fun x=>if mask x=true ∧
          ∀r,SampledTransferSupport k (fun u=>∏b,x (π r ⟨u,b⟩)) B₀ V₀ extra j
            (o r) (s r) (evalExpressions x (relabelExpressions (π r) (e r))) (t r) then f x else 0) -
        fullProductMean S μ (fun x=>if mask x=true ∧
          (∀r,TransferCoreSupport k B₀ V₀ extra j (s r)
            (evalExpressions x (relabelExpressions (π r) (e r))) (t r)) ∧
          (∀r i,familyPolynomial
            (relabelFamilies (π r) (actualFamilies k width j (o r) (s r) (e r) (t r))) i) then f x else 0)‖ ≤
        (2*(Fintype.card (Σr:κ,Fin (width r)):ℝ))*Real.exp (-(c/2)*Real.exp (α*L)) := by
  filter_upwards [eventually_reindexed_outside_enlargement C z d hC hz hα hc] with L hL
  intro κ _ _ width k B₀ V₀ extra j o s e t S μ B hS π H A hH hA hμ hmass hatom hprime
    Z hsyntax hfixed hvars mask f hf hgood hfreq htree hZ hHt hAt
  let original (r : Bool) (x : (Σr:κ,Fin (width r))→ℤ) : Prop :=
    SampledTransferSupport k (fun u=>∏b,x (π r ⟨u,b⟩)) B₀ V₀ extra j
      (o r) (s r) (evalExpressions x (relabelExpressions (π r) (e r))) (t r)
  let core (r : Bool) (x : (Σr:κ,Fin (width r))→ℤ) : Prop :=
    TransferCoreSupport k B₀ V₀ extra j (s r)
      (evalExpressions x (relabelExpressions (π r) (e r))) (t r)
  let polynomial (r : Bool) : Prop := ∀i,familyPolynomial
    (relabelFamilies (π r) (actualFamilies k width j (o r) (s r) (e r) (t r))) i
  let mask₀ : ((Σr:κ,Fin (width r))→ℤ)→Bool := fun x=>@decide
    (mask x=true ∧ original true x) (Classical.propDecidable _)
  let mask₁ : ((Σr:κ,Fin (width r))→ℤ)→Bool := fun x=>@decide
    (mask x=true ∧ core false x ∧ polynomial false) (Classical.propDecidable _)
  have hpre (r : Bool) (x : (Σr:κ,Fin (width r))→ℤ) (hx : ∀u,x u∈S (π r u)) :
      ∀u,x ((π r).symm u)∈S u := by
    intro u
    simpa only [Equiv.apply_symm_apply] using hx ((π r).symm u)
  have h₀ := hL width k B₀ V₀ extra j (o false) (s false) (e false) (t false)
    S μ B hS (π false) H A hH hA hμ hmass hatom hprime
    Z (hsyntax false) (hfixed false) hvars
    (fun x=>mask₀ (fun i=>x ((π false).symm i)))
    (fun x=>f (fun i=>x ((π false).symm i)))
    (fun x hx=>hf _ (hpre false x hx)) (hgood false)
    (fun i q hq x hx _ hh=>hfreq false i q hq x hx hh)
    htree hZ hHt hAt
  have h₁ := hL width k B₀ V₀ extra j (o true) (s true) (e true) (t true)
    S μ B hS (π true) H A hH hA hμ hmass hatom hprime
    Z (hsyntax true) (hfixed true) hvars
    (fun x=>mask₁ (fun i=>x ((π true).symm i)))
    (fun x=>f (fun i=>x ((π true).symm i)))
    (fun x hx=>hf _ (hpre true x hx)) (hgood true)
    (fun i q hq x hx _ hh=>hfreq true i q hq x hx hh)
    htree hZ hHt hAt
  simp only [Equiv.apply_symm_apply] at h₀ h₁
  let start : ℂ := fullProductMean S μ (fun x=>@ite ℂ
    (mask x=true ∧ original false x ∧ original true x) (Classical.propDecidable _) (f x) 0)
  let middle : ℂ := fullProductMean S μ (fun x=>@ite ℂ
    (mask x=true ∧ core false x ∧ polynomial false ∧ original true x) (Classical.propDecidable _) (f x) 0)
  let finish : ℂ := fullProductMean S μ (fun x=>@ite ℂ
    (mask x=true ∧ core false x ∧ core true x ∧ polynomial false ∧ polynomial true) (Classical.propDecidable _) (f x) 0)
  have h₀' : ‖start-middle‖≤(Fintype.card (Σr:κ,Fin (width r)):ℝ)*Real.exp (-(c/2)*Real.exp (α*L)) := by
    convert h₀ using 1
    congr 2
    · apply congrArg (fullProductMean S μ)
      funext x
      exact (pair_start_indicator (mask x=true) (original false x) (original true x) (f x)).symm
    · apply congrArg (fullProductMean S μ)
      funext x
      apply indicator_congr
      change (mask x=true ∧ core false x ∧ polynomial false ∧ original true x) ↔
        ((@decide (mask x=true ∧ original true x) (Classical.propDecidable _))=true ∧
          core false x ∧ polynomial false)
      rw [@decide_eq_true_eq (mask x=true ∧ original true x) (Classical.propDecidable _)]
      constructor
      · rintro ⟨hm,hc,hp,hq⟩; exact ⟨⟨hm,hq⟩,hc,hp⟩
      · rintro ⟨⟨hm,hq⟩,hc,hp⟩; exact ⟨hm,hc,hp,hq⟩
  have h₁' : ‖middle-finish‖≤(Fintype.card (Σr:κ,Fin (width r)):ℝ)*Real.exp (-(c/2)*Real.exp (α*L)) := by
    convert h₁ using 1
    congr 2
    · apply congrArg (fullProductMean S μ)
      funext x
      exact (pair_middle_right_indicator (mask x=true) (core false x) (polynomial false) (original true x) (f x)).symm
    · apply congrArg (fullProductMean S μ)
      funext x
      apply indicator_congr
      change (mask x=true ∧ core false x ∧ core true x ∧ polynomial false ∧ polynomial true) ↔
        ((@decide (mask x=true ∧ core false x ∧ polynomial false) (Classical.propDecidable _))=true ∧
          core true x ∧ polynomial true)
      rw [@decide_eq_true_eq (mask x=true ∧ core false x ∧ polynomial false) (Classical.propDecidable _)]
      constructor
      · rintro ⟨hm,hc,hd,hp,hq⟩; exact ⟨⟨hm,hc,hp⟩,hd,hq⟩
      · rintro ⟨⟨hm,hc,hp⟩,hd,hq⟩; exact ⟨hm,hc,hd,hp,hq⟩
  have htotal : ‖start-finish‖≤
      (2*(Fintype.card (Σr:κ,Fin (width r)):ℝ))*Real.exp (-(c/2)*Real.exp (α*L)) := by
    calc
      _ = ‖(start-middle)+(middle-finish)‖ := by congr 1; ring
      _ ≤ ‖start-middle‖+‖middle-finish‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  convert htotal using 1
  congr 2
  · apply congrArg (fullProductMean S μ)
    funext x
    apply indicator_congr
    change (mask x=true ∧ ∀r,original r x) ↔
      (mask x=true ∧ original false x ∧ original true x)
    rw [Bool.forall_bool]
  · apply congrArg (fullProductMean S μ)
    funext x
    apply indicator_congr
    change (mask x=true ∧ (∀r,core r x) ∧ ∀r,polynomial r) ↔
      (mask x=true ∧ core false x ∧ core true x ∧ polynomial false ∧ polynomial true)
    simp only [Bool.forall_bool,and_assoc]

end Ostmann.Characters.TemplateOneSidedSupportTelescoping

end

end OAI
