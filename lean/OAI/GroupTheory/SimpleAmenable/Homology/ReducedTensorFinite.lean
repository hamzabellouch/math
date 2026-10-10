import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.ConstantSplit

namespace OAI

section
open CategoryTheory Limits MonoidalCategory HomologicalComplex HomologicalComplex₂
namespace TensorProductHomology

variable {R:Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
lemma finite_reduced (K L:ChainComplex (ModuleCat.{0} R) ℕ)
    [∀i,Module.Flat R (K.X i)] (n:ℕ)
    (hK0:IsZero (K.homology 0)) (hL0:IsZero (L.homology 0))
    (hK:∀i,i<n → Module.Finite R (K.homology i))
    (hL:∀i,i<n → Module.Finite R (L.homology i)) :
    Module.Finite R (((bicomplex K L).total c).homology n) := by
  apply TotalFiniteness.finite
  intro p q hpq
  let e : (TotalFiniteness.row (bicomplex K L) q).homology p ≅
      (TensorCoefficient.homologyFunctor K p).obj (L.homology q) :=
    (homologyFunctor _ c p).mapIso (rowIso K L q)
  have coefficientFinite : Module.Finite R ((TensorCoefficient.homologyFunctor K p).obj (L.homology q)) := by
    by_cases hq:q=0
    · subst q
      have hz := Functor.map_isZero (TensorCoefficient.homologyFunctor K p) hL0
      have zeroCoefficientSubsingleton := ModuleCat.isZero_iff_subsingleton.mp hz
      infer_instance
    · cases p with
      | zero =>
        have hz := TensorCoefficient.arbitrary_zero_zero K (L.homology q) hK0
        have zeroHomologySubsingleton := ModuleCat.isZero_iff_subsingleton.mp hz
        infer_instance
      | succ p =>
        have rightHomologyFinite := hL q (by omega)
        have leftHomologyFinite := hK p (by omega)
        have leftSuccessorFinite := hK (p+1) (by omega)
        exact TensorCoefficient.finite_coefficient_succ K (L.homology q) p
  exact Module.Finite.equiv e.symm.toLinearEquiv
end TensorProductHomology
namespace ConstantSplit
open FreeChains ProductChains

lemma red_finite (X:SSet) [X.IsConnected] (n:ℕ) [Module.Finite ℤ ((complex X).homology n)] :
    Module.Finite ℤ (((sc X).X₁).homology n) := by
  let s := splitting X (ConnectedProduct.point X)
  have originalHomologyFinite : Module.Finite ℤ (((sc X).X₂).homology n) :=
    ‹Module.Finite ℤ ((complex X).homology n)›
  let f := (homologyMap (sc X).f n).hom
  apply Module.Finite.of_injective f
  intro x y h
  have he := congrArg (fun t => homologyMap t n) s.f_r
  rw [homologyMap_comp,homologyMap_id] at he
  have he' : Function.LeftInverse (homologyMap s.r n) f := by
    intro z
    exact congrArg (fun t => t z) he
  exact he'.injective h
lemma red_homology_zero (X:SSet) [X.IsConnected] : IsZero (((sc X).X₁).homology 0) :=
  red_zero X 1 (by intro i hi hi'; omega) 0 (by omega)
end ConstantSplit
namespace ChainTensor
open FreeChains

variable (S T:ShortComplex (ChainComplex A ℕ)) (s:S.Splitting) (t:T.Splitting)
lemma homology_joint_kernel' (n:ℕ) (x:(S.X₂⊗T.X₂).homology n)
    (h0:homologyMap (s.r⊗ₘt.r) n x=0)
    (h1:homologyMap (𝟙 S.X₂⊗ₘT.g) n x=0)
    (h2:homologyMap (S.g⊗ₘ𝟙 T.X₂) n x=0) : x=0 := by
  have hid := congrArg (fun f => homologyMap f n) (splitting_tensor_identity S T s t)
  simp only [homologyMap_add,homologyMap_comp,homologyMap_id] at hid
  have hh := congrArg (fun f => f x) hid
  change homologyMap (S.f⊗ₘT.f) n (homologyMap (s.r⊗ₘt.r) n x) +
    homologyMap ((s.r≫S.f)⊗ₘt.s) n (homologyMap (𝟙 S.X₂⊗ₘT.g) n x) +
    homologyMap (s.s⊗ₘ𝟙 T.X₂) n (homologyMap (S.g⊗ₘ𝟙 T.X₂) n x) = x at hh
  simpa only [h0,h1,h2,map_zero,add_zero] using hh.symm
end ChainTensor

end

section
open CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite
namespace ConnectedProduct
open FreeChains ProductChains

attribute [local instance 1200] Submodule.module
variable (X Y:SSet) [X.IsConnected] [Y.IsConnected]
noncomputable def redProjection (n:ℕ) :
    ((X⊗Y).homology Z n : A) ⟶
      (((ConstantSplit.sc X).X₁)⊗((ConstantSplit.sc Y).X₁)).homology n :=
  (homologyIsoN X Y n).hom ≫ homologyMap
    ((ConstantSplit.splitting X (point X)).r⊗ₘ(ConstantSplit.splitting Y (point Y)).r) n
lemma projection_joint_zero (n:ℕ) (x:((X⊗Y).homology Z n : A))
    (hx:projection X Y n x=0) (hr:redProjection X Y n x=0) : x=0 := by
  have hf : SSet.homologyMap (CartesianMonoidalCategory.fst X Y) Z n x=0 := by
    have h := congrArg (fun z => (biprod.fst : X.homology Z n ⊞ Y.homology Z n ⟶ X.homology Z n) z) hx
    simp only [map_zero] at h
    change (projection X Y n ≫ biprod.fst) x=0 at h
    simpa only [projection,biprod.lift_fst] using h
  have hg : SSet.homologyMap (CartesianMonoidalCategory.snd X Y) Z n x=0 := by
    have h := congrArg (fun z => (biprod.snd : X.homology Z n ⊞ Y.homology Z n ⟶ Y.homology Z n) z) hx
    simp only [map_zero] at h
    change (projection X Y n ≫ biprod.snd) x=0 at h
    simpa only [projection,biprod.lift_snd] using h
  let e := homologyIsoN X Y n
  have h1 : homologyMap (𝟙 (complex X)⊗ₘConstantSplit.aug Y) n (e.hom x)=0 := by
    have hn := homology_natural (𝟙 X) (SSet.const (X:=Y) (Y:=one) PUnit.unit) n
    rw [chainMap_id] at hn
    have he : (𝟙 X)⊗ₘ(SSet.const (X:=Y) (Y:=one) PUnit.unit) =
        CartesianMonoidalCategory.fst X Y ≫ pairLeft X one PUnit.unit := by ext d z <;> rfl
    rw [he,SSet.homologyMap_comp] at hn
    have hh := congrArg (fun f => f x) hn
    change (homologyIsoN X one n).hom
      (SSet.homologyMap (pairLeft X one PUnit.unit) Z n
        (SSet.homologyMap (CartesianMonoidalCategory.fst X Y) Z n x)) = _ at hh
    simpa only [hf,map_zero,ConstantSplit.aug,ConstantSplit.one,e,ModuleCat.comp_apply] using hh.symm
  have h2 : homologyMap (ConstantSplit.aug X⊗ₘ𝟙 (complex Y)) n (e.hom x)=0 := by
    have hn := homology_natural (SSet.const (X:=X) (Y:=one) PUnit.unit) (𝟙 Y) n
    rw [chainMap_id] at hn
    have he : (SSet.const (X:=X) (Y:=one) PUnit.unit)⊗ₘ(𝟙 Y) =
        CartesianMonoidalCategory.snd X Y ≫ pairRight one Y PUnit.unit := by ext d z <;> rfl
    rw [he,SSet.homologyMap_comp] at hn
    have hh := congrArg (fun f => f x) hn
    change (homologyIsoN one Y n).hom
      (SSet.homologyMap (pairRight one Y PUnit.unit) Z n
        (SSet.homologyMap (CartesianMonoidalCategory.snd X Y) Z n x)) = _ at hh
    simpa only [hg,map_zero,ConstantSplit.aug,ConstantSplit.one,e,ModuleCat.comp_apply] using hh.symm
  have hh := ChainTensor.homology_joint_kernel' (ConstantSplit.sc X) (ConstantSplit.sc Y)
    (ConstantSplit.splitting X (point X)) (ConstantSplit.splitting Y (point Y)) n
    (e.hom x) hr h1 h2
  exact e.toLinearEquiv.injective (hh.trans (map_zero e.toLinearEquiv).symm)
lemma finite_projection_kernel (n:ℕ)
    (hX:∀ i,i<n → Module.Finite ℤ (X.homology Z i : A))
    (hY:∀ i,i<n → Module.Finite ℤ (Y.homology Z i : A)) :
    Module.Finite ℤ (LinearMap.ker (projection X Y n).hom) := by
  have hXF : ∀ i,i<n → Module.Finite ℤ (((ConstantSplit.sc X).X₁).homology i) := by
    intro i hi
    have simplicialHomologyFinite := hX i hi
    let e : (X.homology Z i : A) ≅ (complex X).homology i :=
      (homologyFunctor A c i).mapIso (complexIso X)
    have chainHomologyFinite : Module.Finite ℤ ((complex X).homology i) := Module.Finite.equiv e.toLinearEquiv
    exact ConstantSplit.red_finite X i
  have hYF : ∀ i,i<n → Module.Finite ℤ (((ConstantSplit.sc Y).X₁).homology i) := by
    intro i hi
    have simplicialHomologyFinite := hY i hi
    let e : (Y.homology Z i : A) ≅ (complex Y).homology i :=
      (homologyFunctor A c i).mapIso (complexIso Y)
    have chainHomologyFinite : Module.Finite ℤ ((complex Y).homology i) := Module.Finite.equiv e.toLinearEquiv
    exact ConstantSplit.red_finite Y i
  have reducedTensorFinite : Module.Finite ℤ ((((ConstantSplit.sc X).X₁)⊗((ConstantSplit.sc Y).X₁)).homology n) :=
    TensorProductHomology.finite_reduced _ _ n
      (ConstantSplit.red_homology_zero X) (ConstantSplit.red_homology_zero Y) hXF hYF
  let f := (redProjection X Y n).hom.comp (LinearMap.ker (projection X Y n).hom).subtype
  apply Module.Finite.of_injective f
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  apply Subtype.ext
  exact projection_joint_zero X Y n x.val x.property hx
end ConnectedProduct

end

end OAI
