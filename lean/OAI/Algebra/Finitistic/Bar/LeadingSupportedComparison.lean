import OAI.Algebra.Finitistic.Bar.SupportedOuterCoordinates
import OAI.Algebra.Finitistic.Bar.RecursivePrefixInclusions

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal

private theorem mapIso_trans_congr {R : Type*} [Ring R]
    (F : ModuleCat R ⥤ ModuleCat R) {U V W Z T : ModuleCat R}
    (e : U ≅ V) (f : V ≅ W) (g : W ≅ Z)
    (j : F.obj Z ≅ T) (j' : F.obj W ≅ T) (h : F.mapIso g ≪≫ j = j') :
    F.mapIso (e ≪≫ (f ≪≫ g)) ≪≫ j = F.mapIso (e ≪≫ f) ≪≫ j' := by
  simpa only [Functor.mapIso_trans, Iso.trans_assoc] using
    congrArg (fun t => F.mapIso (e ≪≫ f) ≪≫ t) h

universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance (V : ModuleCat.{u} D) : Module k V := BimoduleTensor.scalarModule k D V
local instance (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance leadingSupportedComparisonIndexDecidableEq (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)
local notation "c" => ComplexShape.down ℕ
local instance : Module A N := inflatedModule D X N
local instance : IsScalarTower k A N := IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

def supportedLeadingIso (r n : ℕ) (t : Index (r+1) n) (h : inputDegree (r+1) t=0) :
    summand (leadingBarSequence k D X r) Z (r+1) n t ≅
      ModuleCat.of D (D ⊗[k] patternTerm k D X N (leadingPattern r n t)) := by
  rcases t with ⟨⟨⟨i,q⟩,hq⟩,t⟩
  exact eqToIso (leadingSummand_last k D X N r n i q hq t) ≪≫
    (barFunctor k D ⋙ HomologicalComplex.eval _ c i).mapIso
    (eqToIso (leadingSummand_prefix k D X Z r r q le_rfl t) ≪≫
      supportedInnerIso k D X N r q t h) ≪≫ freeBarPatternIso k D X N i (innerPattern r t)

theorem iso_mpr_source {U U' V : ModuleCat.{u} D} (h : U=U') (e : U' ≅ V) :
    Eq.mpr (congrArg (fun W : ModuleCat D => W ≅ V) h) e = eqToIso h ≪≫ e := by
  subst U'
  simp

theorem leadingSummandIso_explicit (r n i q : ℕ) (hq : i+q=n) (t : Index r q) :
    leadingSummandIso k D X Z r n ⟨⟨⟨i,q⟩,hq⟩,t⟩ =
      eqToIso (leadingSummand_last k D X N r n i q hq t) ≪≫
        (barFunctor k D ⋙ HomologicalComplex.eval _ c i).mapIso
          (eqToIso (leadingSummand_prefix k D X Z r r q le_rfl t) ≪≫
            innerSummandIso k D X Z r q t) ≪≫
          freeBarPatternIso k D X ((Z).X (inputDegree r t)) i (innerPattern r t) := by
  unfold leadingSummandIso
  change Eq.mpr (congrArg (fun W : ModuleCat D => W ≅
      ModuleCat.of D (D ⊗[k] patternTerm k D X ((Z).X (inputDegree r t))
        (List.replicate i false ++ innerPattern r t)))
      (leadingSummand_last k D X N r n i q hq t)) _ = _
  erw [iso_mpr_source]
  rfl

theorem supportedLeadingIso_eq (r n : ℕ) (t : Index (r+1) n) (h : inputDegree (r+1) t=0) :
    supportedLeadingIso k D X N r n t h = leadingSummandIso k D X Z r n t ≪≫
      eqToIso (congrArg (fun V : ModuleCat D => ModuleCat.of D
        (D ⊗[k] patternTerm k D X V (leadingPattern r n t)))
        (show (Z).X (inputDegree (r+1) t)=N by rw [h]; rfl)) := by
  rcases t with ⟨⟨⟨i,q⟩,hq⟩,t⟩
  let F := barFunctor k D ⋙ HomologicalComplex.eval _ c i
  let p := innerPattern r t
  let V := (Z).X (inputDegree r t)
  have hv : V=N := by change (Z).X (inputDegree r t)=N; rw [show inputDegree r t=0 from h]; rfl
  rw [leadingSummandIso_explicit]
  dsimp only [supportedLeadingIso]
  erw [Iso.trans_assoc]
  congr 1
  change F.mapIso (eqToIso _ ≪≫ supportedInnerIso k D X N r q t h) ≪≫
    freeBarPatternIso k D X N i p =
    F.mapIso (eqToIso _ ≪≫ innerSummandIso k D X Z r q t) ≪≫ (freeBarPatternIso k D X V i p ≪≫
      eqToIso (congrArg (fun W : ModuleCat D =>
        ModuleCat.of D (patternTerm k D X W (List.replicate (i+1) false ++ p))) hv))
  erw [supportedInnerIso_eq]
  exact mapIso_trans_congr F _ _ _ _ _ (freeBarPatternIso_eqToIso k D X V N hv i p)

theorem supportedLeading_length (r n : ℕ) (t : Index (r+1) n) (h : inputDegree (r+1) t=0) :
    (leadingPattern r n t).length=r+n := by
  have ht := length_leadingPattern r n t
  omega

private theorem innerTotalEmbedding_supported_comp (r q : ℕ) (t : Index r q)
    (h : inputDegree r t = 0) :
    let p := innerPattern r t
    let V := summand B Z r q t
    let W := ModuleCat.of D (patternTerm k D X N p)
    let e := canonicalLinear k D X N (patternTerm k D X N p) p.length (embed k D X N p)
    (innerTotalEmbedding k D X N r q).comp
      (canonicalRestrict k D V ((iter B Z r).X q) (inclusion B Z r q t)) =
      (termCast k D X N (supportedInner_length r q t h)).comp
        (e.comp (canonicalRestrict k D V W (supportedInnerIso k D X N r q t h).hom)) := by
  dsimp only
  ext w
  change innerTotalEmbedding k D X N r q ((inclusion B Z r q t).hom w) =
    termCast k D X N (supportedInner_length r q t h)
      (canonicalLinear k D X N (patternTerm k D X N (innerPattern r t))
        (innerPattern r t).length (embed k D X N (innerPattern r t))
        ((supportedInnerIso k D X N r q t h).hom.hom w))
  rw [canonicalLinear_apply, innerTotalEmbedding_inclusion]
  exact innerEmbedding_supported k D X N r q t h w

private theorem leadingTotalEmbedding_on_summand (r n i q : ℕ) (hq : i+q=n)
    (t : Index r q)
    (v : summand (leadingBarSequence k D X r) Z (r+1) n ⟨⟨⟨i,q⟩,hq⟩,t⟩) :
    let g := eqToHom (leadingSummand_prefix k D X Z r r q le_rfl t)
    let v' := (eqToHom (leadingSummand_last k D X N r n i q hq t)).hom v
    let u := ((barFunctor k D ⋙ HomologicalComplex.eval _ c i).map g).hom v'
    ((inclusion (leadingBarSequence k D X r) Z (r+1) n ⟨⟨⟨i,q⟩,hq⟩,t⟩ ≫
      eqToHom (congrArg (fun W => W.X n) (leadingIter_total k D X N r)) ≫
      leadingTotalEmbedding k D X N r n).hom v) =
    outerCast k D X N (show (r+q)+i=r+n by omega)
      (outerBarSuffix k D X N ((iter B Z r).X q) (r+q) i
        (innerTotalEmbedding k D X N r q)
        ((((barFunctor k D).map (inclusion B Z r q t)).f i).hom u)) := by
  dsimp only
  rw [← Category.assoc, leadingInclusion_total]
  erw [Category.assoc, Category.assoc, leadingTotalEmbedding_ι]
  simp only [Functor.map_comp, Category.assoc, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom]
  rfl

private theorem supportedLeadingIso_apply (r n i q : ℕ) (hq : i+q=n)
    (t : Index r q) (h : inputDegree r t = 0)
    (v : summand (leadingBarSequence k D X r) Z (r+1) n ⟨⟨⟨i,q⟩,hq⟩,t⟩) :
    let p := innerPattern r t
    let g := eqToHom (leadingSummand_prefix k D X Z r r q le_rfl t)
    let f := (supportedInnerIso k D X N r q t h).hom
    let v' := (eqToHom (leadingSummand_last k D X N r n i q hq t)).hom v
    let u := ((barFunctor k D ⋙ HomologicalComplex.eval _ c i).map g).hom v'
    (supportedLeadingIso k D X N r n ⟨⟨⟨i,q⟩,hq⟩,t⟩ h).hom.hom v =
      (freeBarPatternIso k D X N i p).hom.hom ((((barFunctor k D).map f).f i).hom u) := by
  dsimp only
  simp only [supportedLeadingIso, Iso.trans_hom,
    ModuleCat.hom_comp, LinearMap.comp_apply, eqToIso.hom]
  erw [Iso.trans_hom, Functor.mapIso_hom, Iso.trans_hom, Functor.map_comp]
  rfl

private theorem outerBarSuffix_of_pattern (V : ModuleCat.{u} D) (p : List Bool)
    (f : V ⟶ ModuleCat.of D (patternTerm k D X N p)) (i b m : ℕ)
    (hp : p.length=b) (h₁ : b+i=m) (h₂ : (List.replicate i false ++ p).length=m)
    (v : ((barFunctor k D).obj V).X i) :
    outerCast k D X N h₁
      (outerBarSuffix k D X N V b i
        ((termCast k D X N hp).comp
          ((canonicalLinear k D X N (patternTerm k D X N p) p.length (embed k D X N p)).comp
            (canonicalRestrict k D V (ModuleCat.of D (patternTerm k D X N p)) f))) v) =
    outerCast k D X N h₂
      (AlgebraTensorModule.lTensor D D (embed k D X N (List.replicate i false ++ p))
        ((freeBarPatternIso k D X N i p).hom.hom ((((barFunctor k D).map f).f i).hom v))) := by
  rw [outerBarSuffix_termCast]
  erw [← outerBarSuffix_map k D X N V (ModuleCat.of D (patternTerm k D X N p))
    p.length i (canonicalLinear k D X N (patternTerm k D X N p) p.length
      (embed k D X N p)) f v]
  erw [outerBarSuffix_canonicalLinear k D X N (patternTerm k D X N p) p.length i
    (embed k D X N p)]
  rw [outerEmbed_freeBarPatternIso, outerCast_trans, outerCast_trans]

private theorem outerBarSuffix_supported (r n i q : ℕ) (hq : i+q=n)
    (t : Index r q) (h : inputDegree r t=0)
    (u : ((barFunctor k D).obj (summand B Z r q t)).X i) :
    outerCast k D X N (show (r+q)+i=r+n by omega)
      (outerBarSuffix k D X N (summand B Z r q t) (r+q) i
        ((innerTotalEmbedding k D X N r q).comp
          (canonicalRestrict k D (summand B Z r q t) ((iter B Z r).X q)
            (inclusion B Z r q t))) u) =
    outerCast k D X N (supportedLeading_length r n ⟨⟨⟨i,q⟩,hq⟩,t⟩ h)
      (AlgebraTensorModule.lTensor D D (embed k D X N (List.replicate i false ++ innerPattern r t))
        ((freeBarPatternIso k D X N i (innerPattern r t)).hom.hom
          ((((barFunctor k D).map (supportedInnerIso k D X N r q t h).hom).f i).hom u))) := by
  let p := innerPattern r t
  let V := summand B Z r q t
  let W := ModuleCat.of D (patternTerm k D X N p)
  let f : V ⟶ W := (supportedInnerIso k D X N r q t h).hom
  let e := canonicalLinear k D X N (patternTerm k D X N p) p.length (embed k D X N p)
  have hp : p.length=r+q := supportedInner_length r q t h
  have he : (innerTotalEmbedding k D X N r q).comp
      (canonicalRestrict k D V ((iter B Z r).X q) (inclusion B Z r q t)) =
      (termCast k D X N hp).comp (e.comp (canonicalRestrict k D V W f)) :=
    innerTotalEmbedding_supported_comp k D X N r q t h
  rw [he]
  exact outerBarSuffix_of_pattern k D X N V p f i (r+q) (r+n) hp _ _ u

/-- The leading total embedding on every surviving recursive summand is the
original literal tensor inclusion under the previously constructed coordinates. -/
theorem leadingTotalEmbedding_supported (r n i q : ℕ) (hq : i+q=n) (t : Index r q)
    (h : inputDegree r t=0)
    (v : summand (leadingBarSequence k D X r) Z (r+1) n ⟨⟨⟨i,q⟩,hq⟩,t⟩) :
    ((inclusion (leadingBarSequence k D X r) Z (r+1) n ⟨⟨⟨i,q⟩,hq⟩,t⟩ ≫
      eqToHom (congrArg (fun W => W.X n) (leadingIter_total k D X N r)) ≫
      leadingTotalEmbedding k D X N r n).hom v) =
    outerCast k D X N (supportedLeading_length r n ⟨⟨⟨i,q⟩,hq⟩,t⟩ h)
      (AlgebraTensorModule.lTensor D D (embed k D X N (List.replicate i false ++ innerPattern r t))
        ((supportedLeadingIso k D X N r n ⟨⟨⟨i,q⟩,hq⟩,t⟩ h).hom.hom v)) := by
  let p := innerPattern r t
  let V := summand B Z r q t
  let g : summand (leadingBarSequence k D X r) Z r q t ⟶ V :=
    eqToHom (leadingSummand_prefix k D X Z r r q le_rfl t)
  let v' := (eqToHom (leadingSummand_last k D X N r n i q hq t)).hom v
  let u := (((barFunctor k D ⋙ HomologicalComplex.eval _ c i).map g).hom v')
  refine (leadingTotalEmbedding_on_summand k D X N r n i q hq t v).trans ?_
  change outerCast k D X N (show (r+q)+i=r+n by omega)
    (outerBarSuffix k D X N ((iter B Z r).X q) (r+q) i (innerTotalEmbedding k D X N r q)
      ((((barFunctor k D).map (inclusion B Z r q t)).f i).hom u)) = _
  rw [outerBarSuffix_map]
  change outerCast k D X N _ (outerBarSuffix k D X N V (r+q) i
    ((innerTotalEmbedding k D X N r q).comp
      (canonicalRestrict k D V ((iter B Z r).X q) (inclusion B Z r q t))) u) = _
  refine (outerBarSuffix_supported k D X N r n i q hq t h u).trans ?_
  exact (congrArg (fun w =>
    outerCast k D X N (supportedLeading_length r n ⟨⟨⟨i,q⟩,hq⟩,t⟩ h)
      (AlgebraTensorModule.lTensor D D (embed k D X N (List.replicate i false ++ p)) w))
    (supportedLeadingIso_apply k D X N r n i q hq t h v)).symm
end DerivedBar.ParityBridge

end

end OAI
