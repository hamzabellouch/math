import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportTelescopingFamily

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSupportTelescoping
open SymbolicHistory TemplateSupportRemoval Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem eventually_all_coordinates_enlargement (C z : ℝ) (d : ℕ) {a c : ℝ}
    (hC : 0≤C) (hz : 0≤z) (ha : 0<a) (hc : 0<c) :
    ∀ᶠ L : ℝ in atTop,∀ {ι : Type} [Fintype ι] [DecidableEq ι],
    ∀ (k : ℕ) (B₀ V₀ : (j:ℕ)→Template.State k (j+1)→ℤ) (j : ℕ)
      (b : Bool) (s : ℤ) (e : Template.Expressions (ι:=ι) k j) (t : HistoryReconstruction.Tree j)
      (D : ι→Finset (Expr ι))
      (_hD : ∀i q,q∈D i → q∈Template.obstructionExpressions k j b s e t)
      (S : ι→Finset ℤ) (μ : ι→ℤ→ℝ) (B : ι→Finset ℕ)
      (_hS : ∀i,S i=(B i).image (fun p:ℕ=>(p:ℤ)))
      (H A : ℝ) (_hH : Real.log 2≤H) (_hA : 0≤A)
      (_hμ : ∀i v,v∈S i → 0≤μ i v) (_hmass : ∀i,∑v∈S i,μ i v=1)
      (_hatom : ∀i v,v∈S i → μ i v≤Real.exp (-c*Real.exp (a*L)))
      (_hprime : ∀i p,p∈B i → p.Prime)
      (Z : ℕ) (_hsyntax : ∀i q,q∈D i → q.syntaxSize≤Z)
      (_hfixed : ∀i q,q∈D i → q.FixedLogBound H)
      (_hvars : ∀i v,v∈S i → |(v:ℝ)|≤Real.exp H)
      (core : (ι→ℤ)→Prop) (f : (ι→ℤ)→ℂ)
      (_hf : ∀x,(∀u,x u∈S u) → ‖f x‖≤A)
      (_hgood : ∀x,(∀u,x u∈S u) → core x → ∀u,HistoryReconstruction.Good x (e u))
      (_hsupport : ∀x,(∀u,x u∈S u) → core x →
        Template.Supported k B₀ V₀ j s (Template.evalExpressions x e) t)
      (_hfreq : ∀i q,q∈D i → ∀x,(∀u,x u∈S u) → core x → q.DivisorsBelow (x i).toNat),
      (2^(j+1):ℝ)≤Real.exp (historyPolynomialCost C z d L) →
      (Z:ℝ)≤Real.exp (historyPolynomialCost C z d L) →
      H≤Real.exp (historyPolynomialCost C z d L) → A≤Real.exp (historyPolynomialCost C z d L) →
      ‖fullProductMean S μ (fun x=>if core x ∧ ∀i,∀q∈D i,IsCoprime (x i) (q.integerEval x)
          then f x else 0) -
        fullProductMean S μ (fun x=>if core x ∧ ∀i,∀q∈D i,eraseCoordinate i q.numerator≠0
          then f x else 0)‖ ≤
        (Fintype.card ι:ℝ)*Real.exp (-(c/2)*Real.exp (a*L)) := by
  filter_upwards [eventually_template_support_removal C z d hC hz ha hc] with L hremoval
  intro ι _ _ k B₀ V₀ j b s e t D hD S μ B hS H A hH hA hμ hmass hatom hprime
    Z hsyntax hfixed hvars core f hf hgood hsupport hfreq htree hZ hHt hAt
  let F : Finset ι→ℂ := fun removed=>fullProductMean S μ
    (hybridValue removed core (familyCoprime D) (familyPolynomial D) f)
  have hstep (removed : Finset ι) (i : ι) (hi : i∉removed) :
      ‖F removed-F (insert i removed)‖≤Real.exp (-(c/2)*Real.exp (a*L)) := by
    have hpS (p : ℕ) (hp : p∈B i) : (p:ℤ)∈S i := by
      rw [hS i]
      exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
    have hxS (x : Other i→ℤ) (hx : ∀u,x u∈S u.val) (p : ℕ) (hp : p∈B i) :
        ∀u,insertCoordinate i x (p:ℤ) u∈S u := by
      intro u
      by_cases hu : u=i
      · subst u
        simpa only [insertCoordinate_self] using hpS p hp
      · simpa only [insertCoordinate,dite_eq_right hu] using hx ⟨u,hu⟩
    have hpmass : (∑p∈B i,μ i (p:ℤ))=1 := by
      have hh := hmass i
      rw [hS i,Finset.sum_image] at hh
      · exact hh
      · intro p hp q hq he
        exact Int.ofNat_inj.mp he
    let r : (Other i→ℤ)→ℕ→Bool := fun x p=>decide
      (remainder removed i core (familyCoprime D) (familyPolynomial D)
        (insertCoordinate i x (p:ℤ)))
    have hcore (x : Other i→ℤ) (p : ℕ) (hr : r x p=true) :
        core (insertCoordinate i x (p:ℤ)) := (of_decide_eq_true hr).1
    have hest := hremoval k B₀ V₀ j b s e t (D i) (hD i) i
      (fun u:Other i=>S u.val) (fun u=>μ u.val) (B i) (fun p=>μ i (p:ℤ)) H A hH hA
      (fun u v hv=>hμ u.val v hv) (fun u=>hmass u.val) (fun u v hv=>hatom u.val v hv)
      (hprime i) (fun p hp=>hμ i _ (hpS p hp)) hpmass
      (fun p hp=>hatom i _ (hpS p hp)) Z (hsyntax i) (hfixed i)
      (fun u v hv=>hvars u.val v hv) r (fun x p=>f (insertCoordinate i x (p:ℤ)))
      (fun x hx p hp=>hf _ (hxS x hx p hp))
      (fun x hx p hp hr=>hgood _ (hxS x hx p hp) (hcore x p hr))
      (fun x hx p hp hr=>hsupport _ (hxS x hx p hp) (hcore x p hr))
      (fun q hq x hx p hp hr=>by
        simpa only [insertCoordinate_self,Int.toNat_natCast] using
          hfreq i q hq _ (hxS x hx p hp) (hcore x p hr)) htree hZ hHt hAt
    dsimp only [F]
    rw [fullProductMean_eq_independentPrimeMean i S μ (B i) (hS i),
      fullProductMean_eq_independentPrimeMean i S μ (B i) (hS i)]
    simpa only [hybridValue_eq_family D removed i hi core f _ _ (insertCoordinate_self ..),
      hybridValue_insert_eq_family D removed i hi core f,r] using hest
  have hfinal := norm_telescope_finset F (Real.exp (-(c/2)*Real.exp (a*L))) hstep Finset.univ
  have hzero : F ∅ = fullProductMean S μ (fun x=>
      if core x ∧ ∀i,∀q∈D i,IsCoprime (x i) (q.integerEval x) then f x else 0) := by
    apply congrArg (fullProductMean S μ)
    funext x
    rw [hybridValue_empty]
    split_ifs <;> rfl
  have hall : F Finset.univ = fullProductMean S μ (fun x=>
      if core x ∧ ∀i,∀q∈D i,eraseCoordinate i q.numerator≠0 then f x else 0) := by
    apply congrArg (fullProductMean S μ)
    funext x
    rw [hybridValue_univ]
  rw [hzero,hall] at hfinal
  simpa only [Finset.card_univ] using hfinal

end Ostmann.Characters.TemplateOneSidedSupportTelescoping

end

end OAI
