import OAI.Algebra.Finitistic.Bar.RecursiveSuffixInduction
import OAI.Algebra.Finitistic.Bar.BarPatternEmbedding

namespace OAI
open CategoryTheory CategoryTheory.Limits TensorProduct TrivSqZeroExt
open scoped TensorProduct DirectSum
noncomputable section
namespace DerivedBar.ParityBridge
open DerivedBar.Multibar DerivedBar.RecursiveTotal
universe u
variable (k D X : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
local instance supportedInnerCoordinatesScalarModule (V : ModuleCat.{u} D) : Module k V :=
  BimoduleTensor.scalarModule k D V
local instance supportedInnerCoordinatesScalarTower (V : ModuleCat.{u} D) : IsScalarTower k D V :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local instance supportedInnerCoordinatesIndexDecidableEq (r n : ℕ) :
    DecidableEq (Index r n) := Classical.decEq _
variable (N : ModuleCat.{u} D)
local notation "A" => TrivSqZeroExt D X
local notation "XB" => BimoduleTensor.twoSidedBarFunctor k D X
local notation "Z" => Functor.obj (ChainComplex.single₀ (ModuleCat D)) N
local notation "B" => (fun _ : ℕ => XB)
local notation "c" => ComplexShape.down ℕ
local instance supportedInnerCoordinatesInflatedModule : Module A N := inflatedModule D X N
local instance supportedInnerCoordinatesInflatedTower : IsScalarTower k A N :=
  IsScalarTower.of_algebraMap_smul
    (fun a v => IsScalarTower.algebraMap_smul D a v)

/-- Re-express a supplied k-linear map using the canonical scalars of ModuleCat D. -/
def canonicalLinear (V : Type u) [AddCommGroup V] [Module k V] [Module D V]
    [IsScalarTower k D V] (s : ℕ) (e : V →ₗ[k] term k A N s) :
    letI : Module k V := BimoduleTensor.scalarModule k D (ModuleCat.of D V)
    V →ₗ[k] term k A N s := by
  have h := BimoduleTensor.scalarModule_eq k D V
  cases h
  exact e

@[simp] theorem canonicalLinear_apply (V : Type u) [AddCommGroup V] [Module k V]
    [Module D V] [IsScalarTower k D V] (s : ℕ) (e : V →ₗ[k] term k A N s) (v : V) :
    canonicalLinear k D X N V s e v = e v := by
  have h := BimoduleTensor.scalarModule_eq k D V
  cases h
  rfl

/-- Prefixing a canonically re-expressed map recovers the supplied-scalars literal formula. -/
theorem barSuffix_canonicalLinear (V : Type u) [AddCommGroup V] [Module k V]
    [Module D V] [IsScalarTower k D V] (s i : ℕ) (e : V →ₗ[k] term k A N s)
    (v : ((XB).obj (ModuleCat.of D V)).X i) :
    barSuffix k D X N (ModuleCat.of D V) s i (canonicalLinear k D X N V s e) v =
      idealSuffixEmbed k D X N V s i e ((twoSidedBarObjIso k D X V i).hom.hom v) := by
  have h := BimoduleTensor.scalarModule_eq k D V
  cases h
  rfl

/-- The same literal inner coordinates, with the proved degree-zero input made explicit. -/
def supportedInnerIso : (r n : ℕ) → (t : Index r n) → (h : inputDegree r t=0) →
    summand B Z r n t ≅ ModuleCat.of D (patternTerm k D X N (innerPattern r t))
  | 0, n, t, h => by
      change n=0 at h
      subst n
      exact Iso.refl _
  | r+1, _, ⟨p,t⟩, h =>
      (XB ⋙ HomologicalComplex.eval _ c p.val.1).mapIso (supportedInnerIso r p.val.2 t h) ≪≫
        twoSidedBarPatternIso k D X N p.val.1 (innerPattern r t)

/-- Transport of the terminal input along an equality of D-modules commutes
with the genuine categorical bar pattern coordinates. -/
theorem twoSidedBarPatternIso_eqToIso (V W : ModuleCat.{u} D) (h : V=W)
    (i : ℕ) (p : List Bool) :
    (XB ⋙ HomologicalComplex.eval _ c i).mapIso
      (eqToIso (congrArg (fun V : ModuleCat D => ModuleCat.of D (patternTerm k D X V p)) h)) ≪≫
        twoSidedBarPatternIso k D X W i p =
    twoSidedBarPatternIso k D X V i p ≪≫
      eqToIso (congrArg (fun V : ModuleCat D =>
        ModuleCat.of D (patternTerm k D X V (true :: (List.replicate i false ++ p)))) h) := by
  subst W
  simp

/-- The supported recursion equals the already existing innerSummandIso,
followed only by the forced zero-degree input transport. -/
theorem supportedInnerIso_eq (r n : ℕ) (t : Index r n) (h : inputDegree r t=0) :
    supportedInnerIso k D X N r n t h =
      innerSummandIso k D X Z r n t ≪≫ eqToIso
        (congrArg (fun V : ModuleCat D => ModuleCat.of D (patternTerm k D X V (innerPattern r t)))
          (show (Z).X (inputDegree r t)=N by rw [h]; rfl)) := by
  induction r generalizing n with
  | zero =>
    change n=0 at h
    subst n
    rfl
  | succ r ih =>
    rcases t with ⟨⟨⟨i,q⟩,hq⟩,t⟩
    let F := XB ⋙ HomologicalComplex.eval _ c i
    let p := innerPattern r t
    let V := (Z).X (inputDegree r t)
    have hv : V=N := by change (Z).X (inputDegree r t)=N; rw [show inputDegree r t=0 from h]; rfl
    change F.mapIso (supportedInnerIso k D X N r q t h) ≪≫
      twoSidedBarPatternIso k D X N i p =
      (F.mapIso (innerSummandIso k D X Z r q t) ≪≫ twoSidedBarPatternIso k D X V i p) ≪≫
        eqToIso (congrArg (fun W : ModuleCat D =>
          ModuleCat.of D (patternTerm k D X W (true :: (List.replicate i false ++ p)))) hv)
    rw [ih q t h, Functor.mapIso_trans, Iso.trans_assoc, Iso.trans_assoc]
    congr 1
    exact twoSidedBarPatternIso_eqToIso k D X V N hv i p

/-- Every surviving summand has exactly r+n literal internal slots. -/
theorem supportedInner_length (r n : ℕ) (t : Index r n) (h : inputDegree r t=0) :
    (innerPattern r t).length = r+n := by
  have ht := length_innerPattern r n t
  omega

def canonicalRestrict (V W : ModuleCat.{u} D) (f : V ⟶ W) : V →ₗ[k] W :=
  f.hom.restrictScalars k

@[simp] theorem canonicalRestrict_apply (V W : ModuleCat.{u} D) (f : V ⟶ W) (v : V) :
    canonicalRestrict k D V W f v = f.hom v := rfl

/-- The canonical recursive embedding agrees with the original literal word
embedding on every supported summand, through the actual bar coordinate maps. -/
theorem innerEmbedding_supported (r n : ℕ) (t : Index r n) (h : inputDegree r t=0)
    (v : summand B Z r n t) :
    innerEmbedding k D X N r n ((lof B Z r n t).hom v) =
      termCast k D X N (supportedInner_length r n t h)
        (embed k D X N (innerPattern r t) ((supportedInnerIso k D X N r n t h).hom.hom v)) := by
  induction r generalizing n with
  | zero =>
    change n=0 at h
    subst n
    have he := congrArg (fun f => f v) (innerEmbedding_zero_lof k D X N t)
    exact he
  | succ r ih =>
    rcases t with ⟨⟨⟨i,q⟩,hq⟩,t⟩
    let p := innerPattern r t
    let V := summand B Z r q t
    let W := ModuleCat.of D (patternTerm k D X N p)
    let f : V ⟶ W := (supportedInnerIso k D X N r q t h).hom
    let e := canonicalLinear k D X N (patternTerm k D X N p) p.length (embed k D X N p)
    have hp : p.length=r+q := supportedInner_length r q t h
    have he : (innerEmbedding k D X N r q).comp ((lof B Z r q t).hom.restrictScalars k) =
        (termCast k D X N hp).comp (e.comp (canonicalRestrict k D V W f)) := by
      ext w
      change innerEmbedding k D X N r q ((lof B Z r q t).hom w) =
        termCast k D X N hp
          (canonicalLinear k D X N (patternTerm k D X N p) p.length (embed k D X N p)
            ((supportedInnerIso k D X N r q t h).hom.hom w))
      rw [canonicalLinear_apply]
      exact ih q t h w
    erw [innerEmbedding_lof_succ k D X N r n i q hq t v, he]
    erw [barSuffix_termCast k D X N V hp i (e.comp (canonicalRestrict k D V W f)) v]
    erw [← barSuffix_map k D X N V W p.length i e f v]
    change termCast k D X N (show ((r+q)+i)+1=(r+1)+n by omega)
      (termCast k D X N (show (p.length+i)+1=((r+q)+i)+1 by omega)
      (barSuffix k D X N W p.length i e ((((XB).map f).f i).hom v))) = _
    erw [barSuffix_canonicalLinear k D X N (patternTerm k D X N p) p.length i
      (embed k D X N p)]
    change _ = termCast k D X N
      (show (true :: (List.replicate i false ++ p)).length=(r+1)+n by
        simp only [List.length_cons, List.length_append, List.length_replicate]; omega)
      (embed k D X N (true :: (List.replicate i false ++ p))
        ((twoSidedBarPatternIso k D X N i p).hom.hom ((((XB).map f).f i).hom v)))
    erw [embed_twoSidedBarPatternIso k D X N i p]
    erw [termCast_trans k D X N
      (show (p.length+i)+1=((r+q)+i)+1 by omega)
      (show ((r+q)+i)+1=(r+1)+n by omega)]
    erw [termCast_trans k D X N
      (show (p.length+i)+1=(true :: (List.replicate i false ++ p)).length by simp; omega)
      (show (true :: (List.replicate i false ++ p)).length=(r+1)+n by
        simp only [List.length_cons, List.length_append, List.length_replicate]; omega)]
end DerivedBar.ParityBridge

end

end OAI
