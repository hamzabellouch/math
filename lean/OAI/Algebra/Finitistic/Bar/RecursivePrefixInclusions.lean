import OAI.Algebra.Finitistic.Bar.LeadingTotalEmbedding

namespace OAI
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace DerivedBar.ParityBridge
universe u
local notation "c" => ComplexShape.down ℕ
section General
variable {D : Type u} [Ring D]

theorem hom_square_of_heq {U U' V V' : ModuleCat.{u} D} (hU : U=U') (hV : V=V')
    (f : U ⟶ V) (g : U' ⟶ V') (h : HEq f g) :
    f ≫ eqToHom hV = eqToHom hU ≫ g := by
  subst U'; subst V'
  cases h
  simp

theorem hom_heq_of_square {U V V' : ModuleCat.{u} D} (hV : V=V')
    (f : U ⟶ V) (g : U ⟶ V') (h : f ≫ eqToHom hV=g) : HEq f g := by
  subst V'
  simpa using h

theorem barInclusionStep_heq
    (G G' : ModuleCat.{u} D ⥤ ChainComplex (ModuleCat.{u} D) ℕ) [G.Additive] [G'.Additive]
    (hG : G=G')
    {U U' : ModuleCat.{u} D} {V V' : ChainComplex (ModuleCat.{u} D) ℕ}
    (hU : U=U') (hV : V=V') (i q n : ℕ) (h : i+q=n)
    (f : U ⟶ V.X q) (g : U' ⟶ V'.X q) (hf : HEq f g) :
    HEq ((G ⋙ HomologicalComplex.eval _ c i).map f ≫
      (RecursiveTotal.bicomplex (fun _ => G) 0 V).ιTotal c i q n h)
      ((G' ⋙ HomologicalComplex.eval _ c i).map g ≫
        (RecursiveTotal.bicomplex (fun _ => G') 0 V').ιTotal c i q n h) := by
  subst G'; subst U'; subst V'
  cases hf
  rfl

theorem barInclusionStep_target
    (G : ModuleCat.{u} D ⥤ ChainComplex (ModuleCat.{u} D) ℕ) [G.Additive]
    {U : ModuleCat.{u} D} {V V' : ChainComplex (ModuleCat.{u} D) ℕ}
    (hV : V=V') (i q n : ℕ) (h : i+q=n) (f : U ⟶ V.X q) :
    (G ⋙ HomologicalComplex.eval _ c i).map f ≫
      (RecursiveTotal.bicomplex (fun _ => G) 0 V).ιTotal c i q n h ≫
      eqToHom (congrArg (fun W => ((RecursiveTotal.bicomplex (fun _ => G) 0 W).total c).X n) hV) =
    (G ⋙ HomologicalComplex.eval _ c i).map (f ≫ eqToHom (congrArg (fun W => W.X q) hV)) ≫
      (RecursiveTotal.bicomplex (fun _ => G) 0 V').ιTotal c i q n h := by
  subst V'
  simp
  erw [Category.comp_id]
end General

open DerivedBar.RecursiveTotal
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
variable (N : ModuleCat.{u} D)
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)

theorem leadingIter_prefix (r m : ℕ) (h : m≤r) :
    iter (leadingBarSequence k D X r) Z m = iter B Z m :=
  (leadingBarSequence_prefix k D X Z r m h).trans (innerIter_eq_explicit k D X N m).symm

/-- Literal recursive inclusions depend only on the functors in their prefix. -/
theorem leadingInclusion_prefix_heq (r m n : ℕ) (h : m≤r) (t : Index m n) :
    HEq (inclusion (leadingBarSequence k D X r) Z m n t) (inclusion B Z m n t) := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    rcases t with ⟨⟨⟨i,q⟩,hq⟩,t⟩
    have hm : m<r := by omega
    have he := barInclusionStep_heq (leadingBarSequence k D X r m) XB
      (by simp only [leadingBarSequence, ite_eq_left hm])
      (leadingSummand_prefix k D X Z r m q (by omega) t)
      (leadingIter_prefix k D X N r m (by omega)) i q n hq
      (inclusion (leadingBarSequence k D X r) Z m q t) (inclusion B Z m q t)
      (ih q (by omega) t)
    exact he

theorem leadingInclusion_prefix (r m n : ℕ) (h : m≤r) (t : Index m n) :
    inclusion (leadingBarSequence k D X r) Z m n t ≫
      eqToHom (congrArg (fun W => W.X n) (leadingIter_prefix k D X N r m h)) =
    eqToHom (leadingSummand_prefix k D X Z r m n h t) ≫ inclusion B Z m n t :=
  hom_square_of_heq _ _ _ _ (leadingInclusion_prefix_heq k D X N r m n h t)

/-- The final total agrees with the actual exterior bar on the constant-X prefix. -/
theorem leadingIter_total (r : ℕ) :
    iter (leadingBarSequence k D X r) Z (r+1) = barTotal k D (iter B Z r) :=
  (leadingBarSequence_total k D X Z r).trans
    (congrArg (barTotal k D) (innerIter_eq_explicit k D X N r).symm)

theorem leadingSummand_last (r n i q : ℕ) (h : i+q=n) (t : Index r q) :
    summand (leadingBarSequence k D X r) Z (r+1) n ⟨⟨⟨i,q⟩,h⟩,t⟩ =
      (barFunctor k D ⋙ HomologicalComplex.eval _ c i).obj
        (summand (leadingBarSequence k D X r) Z r q t) := by
  simp only [summand, degreeFunctor, leadingBarSequence, lt_self_iff_false, ite_false]

/-- The exterior inclusion is exactly the free-bar map of the original inner inclusion. -/
theorem leadingInclusion_total (r n i q : ℕ) (h : i+q=n) (t : Index r q) :
    inclusion (leadingBarSequence k D X r) Z (r+1) n ⟨⟨⟨i,q⟩,h⟩,t⟩ ≫
      eqToHom (congrArg (fun W => W.X n) (leadingIter_total k D X N r)) =
    eqToHom (leadingSummand_last k D X N r n i q h t) ≫
    (barFunctor k D ⋙ HomologicalComplex.eval _ c i).map
      (eqToHom (leadingSummand_prefix k D X Z r r q le_rfl t) ≫ inclusion B Z r q t) ≫
        (barBicomplex k D (iter B Z r)).ιTotal c i q n h := by
  have hi := hom_heq_of_square
    (congrArg (fun W => W.X q) (leadingIter_prefix k D X N r r le_rfl))
    (inclusion (leadingBarSequence k D X r) Z r q t)
    (eqToHom (leadingSummand_prefix k D X Z r r q le_rfl t) ≫ inclusion B Z r q t)
    (leadingInclusion_prefix k D X N r r q le_rfl t)
  have he := barInclusionStep_heq (leadingBarSequence k D X r r) (barFunctor k D)
    (by simp only [leadingBarSequence, lt_self_iff_false, ite_false]) rfl
    (leadingIter_prefix k D X N r r le_rfl) i q n h
    (inclusion (leadingBarSequence k D X r) Z r q t)
    (eqToHom (leadingSummand_prefix k D X Z r r q le_rfl t) ≫ inclusion B Z r q t) hi
  exact hom_square_of_heq _ _ _ _ he
end DerivedBar.ParityBridge

end

end OAI
