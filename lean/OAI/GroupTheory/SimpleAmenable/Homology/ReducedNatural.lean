import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.GroupNerveCoordinates
import OAI.GroupTheory.SimpleAmenable.Homology.ReducedTensorFinite
import OAI.GroupTheory.SimpleAmenable.Homology.ReducedTensorTwo

namespace OAI

section
open CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite
namespace ConstantSplit
open FreeChains ProductChains

variable {X Y:SSet}
@[reassoc] lemma aug_natural (f:X⟶Y) : chainMap f ≫ aug Y=aug X := by
  rw [aug,←chainMap_comp]
  congr 1
noncomputable def redMap (f:X⟶Y) : (sc X).X₁ ⟶ (sc Y).X₁ :=
  kernel.map (aug X) (aug Y) (chainMap f) (𝟙 _) (by simp [aug_natural])
@[reassoc (attr:=simp)] lemma redMap_inclusion (f:X⟶Y) : redMap f ≫ (sc Y).f=(sc X).f ≫ chainMap f :=
  kernel.lift_ι _ _ _
lemma one_positive (n:ℕ) (hn:n≠0) : IsZero ((complex one).homology n) := by
  exact IsZero.of_iso (ConnectedProduct.one_homology_zero n hn)
    ((homologyFunctor A c n).mapIso (complexIso one)).symm
noncomputable def inclusionIso (X:SSet) (x:X.obj (op ⦋0⦌)) (n:ℕ) (hn:n≠0) :
    ((sc X).X₁).homology n ≅ (complex X).homology n where
  hom := homologyMap (sc X).f n
  inv := homologyMap (splitting X x).r n
  hom_inv_id := by erw [←homologyMap_comp,(splitting X x).f_r,homologyMap_id]
  inv_hom_id := by
    have h:=congrArg (fun f=>homologyMap f n) (splitting X x).id
    rw [homologyMap_add,homologyMap_comp,homologyMap_comp,homologyMap_id] at h
    have hz : homologyMap (sc X).g n=0 := (one_positive n hn).eq_of_tgt _ _
    rw [hz,zero_comp,add_zero] at h
    exact h
lemma redMap_epi (f:X⟶Y) (x:X.obj (op ⦋0⦌)) (y:Y.obj (op ⦋0⦌)) (n:ℕ) (hn:n≠0)
    [chainMapEpi : Epi (homologyMap (chainMap f) n)] : Epi (homologyMap (redMap f) n) := by
  have h:=congrArg (fun f=>homologyMap f n) (redMap_inclusion f)
  erw [homologyMap_comp (redMap f) (sc Y).f,
    homologyMap_comp (sc X).f (chainMap f)] at h
  have : IsIso (homologyMap (sc X).f n):=(inclusionIso X x n hn).isIso_hom
  have : IsIso (homologyMap (sc Y).f n):=(inclusionIso Y y n hn).isIso_hom
  have : Epi (homologyMap (redMap f) n ≫ homologyMap (sc Y).f n):=by
    erw [h]
    exact epi_comp' (inferInstanceAs (Epi (homologyMap (sc X).f n))) chainMapEpi
  exact (epi_comp_iff_of_isIso _ (homologyMap (sc Y).f n)).mp inferInstance
lemma red_X_zero (X:SSet) [Subsingleton (X.obj (op ⦋0⦌))] (x:X.obj (op ⦋0⦌)) :
    IsZero (((sc X).X₁).X 0) := by
  have he : (aug X).f 0 ≫ (sec X x).f 0=𝟙 ((complex X).X 0) := by
    change (ModuleCat.free ℤ).map ((SSet.const (Y:=one) PUnit.unit).app (op ⦋0⦌)) ≫
      (ModuleCat.free ℤ).map ((SSet.const (X:=one) x).app (op ⦋0⦌))=𝟙 _
    rw [←Functor.map_comp,←(ModuleCat.free ℤ).map_id (X.obj (op ⦋0⦌))]
    congr 1
    ext z
    exact Subsingleton.elim _ _
  apply (IsZero.iff_id_eq_zero _).mpr
  have : Mono ((sc X).f.f 0) := by change Mono ((kernel.ι (aug X)).f 0); infer_instance
  apply (cancel_mono ((sc X).f.f 0)).mp
  simp only [Category.id_comp,zero_comp]
  have h:=congrArg (fun f=>f.f 0) (sc X).zero
  simp only [HomologicalComplex.comp_f,HomologicalComplex.zero_f] at h
  have hh:=congrArg (fun f=>f≫(sec X x).f 0) h
  change ((sc X).f.f 0 ≫ (aug X).f 0) ≫ (sec X x).f 0 = _ at hh
  erw [Category.assoc,he,zero_comp] at hh
  change (kernel.ι (aug X)).f 0 ≫ 𝟙 ((complex X).X 0)=0 at hh
  rw [Category.comp_id] at hh
  exact hh
end ConstantSplit

end

section
open CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite
namespace ConnectedProduct
open FreeChains ProductChains ConstantSplit

variable (X Y:SSet) [X.IsConnected] [Y.IsConnected]
noncomputable def redInclusion (n:ℕ) :
    (((sc X).X₁)⊗((sc Y).X₁)).homology n ⟶ ((X⊗Y).homology Z n : A) :=
  homologyMap ((sc X).f⊗ₘ(sc Y).f) n ≫ (homologyIsoN X Y n).inv
@[reassoc (attr:=simp)] lemma redInclusion_redProjection (n:ℕ) :
    redInclusion X Y n ≫ redProjection X Y n=𝟙 _ := by
  simp only [redInclusion,redProjection,ConstantSplit.sc,Category.assoc,Iso.inv_hom_id_assoc]
  erw [←homologyMap_comp,tensorHom_comp_tensorHom,(splitting X (point X)).f_r,
    (splitting Y (point Y)).f_r,id_tensorHom_id,homologyMap_id]
omit [X.IsConnected] [Y.IsConnected] in
@[reassoc] lemma redInclusion_fst (n:ℕ) :
    redInclusion X Y n ≫ SSet.homologyMap (CartesianMonoidalCategory.fst X Y) Z n=0 := by
  let f:=SSet.const (X:=Y) (Y:=one) PUnit.unit
  have h:=(homology_natural (𝟙 X) f n)
  have he : (𝟙 X)⊗ₘf=CartesianMonoidalCategory.fst X Y ≫ pairLeft X one PUnit.unit := by ext d z <;> rfl
  rw [he,SSet.homologyMap_comp,chainMap_id] at h
  have ht : ((sc X).f⊗ₘ(sc Y).f) ≫ (𝟙 (complex X)⊗ₘchainMap f)=0 := by
    change ((sc X).f⊗ₘ(sc Y).f) ≫ (𝟙 (sc X).X₂⊗ₘ(sc Y).g)=0
    rw [tensorHom_comp_tensorHom,Category.comp_id]
    rw [(sc Y).zero]; simp
  have hh:=congrArg (fun k=>redInclusion X Y n≫k) h
  simp only [redInclusion,ConstantSplit.sc,Category.assoc,Iso.inv_hom_id_assoc] at hh
  erw [←homologyMap_comp,ht,homologyMap_zero] at hh
  have : Mono (SSet.homologyMap (pairLeft X one PUnit.unit) Z n) := by
    have he : pairLeft X one PUnit.unit ≫ CartesianMonoidalCategory.fst X one=𝟙 X := by ext d z; rfl
    exact (SplitMono.mk _ (by rw [←SSet.homologyMap_comp,he,SSet.homologyMap_id])).mono
  have : Mono (SSet.homologyMap (pairLeft X one PUnit.unit) Z n ≫ (homologyIsoN X one n).hom) := inferInstance
  apply (cancel_mono (SSet.homologyMap (pairLeft X one PUnit.unit) Z n ≫ (homologyIsoN X one n).hom)).mp
  erw [zero_comp]
  simp only [redInclusion,ConstantSplit.sc,Category.assoc]
  exact hh
omit [X.IsConnected] [Y.IsConnected] in
@[reassoc] lemma redInclusion_snd (n:ℕ) :
    redInclusion X Y n ≫ SSet.homologyMap (CartesianMonoidalCategory.snd X Y) Z n=0 := by
  let f:=SSet.const (X:=X) (Y:=one) PUnit.unit
  have h:=(homology_natural f (𝟙 Y) n)
  have he : f⊗ₘ(𝟙 Y)=CartesianMonoidalCategory.snd X Y ≫ pairRight one Y PUnit.unit := by ext d z <;> rfl
  rw [he,SSet.homologyMap_comp,chainMap_id] at h
  have ht : ((sc X).f⊗ₘ(sc Y).f) ≫ (chainMap f⊗ₘ𝟙 (complex Y))=0 := by
    change ((sc X).f⊗ₘ(sc Y).f) ≫ ((sc X).g⊗ₘ𝟙 (sc Y).X₂)=0
    rw [tensorHom_comp_tensorHom,Category.comp_id]
    rw [(sc X).zero]; simp
  have hh:=congrArg (fun k=>redInclusion X Y n≫k) h
  simp only [redInclusion,ConstantSplit.sc,Category.assoc,Iso.inv_hom_id_assoc] at hh
  erw [←homologyMap_comp,ht,homologyMap_zero] at hh
  have : Mono (SSet.homologyMap (pairRight one Y PUnit.unit) Z n) := by
    have he : pairRight one Y PUnit.unit ≫ CartesianMonoidalCategory.snd one Y=𝟙 Y := by ext d z; rfl
    exact (SplitMono.mk _ (by rw [←SSet.homologyMap_comp,he,SSet.homologyMap_id])).mono
  have : Mono (SSet.homologyMap (pairRight one Y PUnit.unit) Z n ≫ (homologyIsoN one Y n).hom) := inferInstance
  apply (cancel_mono (SSet.homologyMap (pairRight one Y PUnit.unit) Z n ≫ (homologyIsoN one Y n).hom)).mp
  erw [zero_comp]
  simp only [redInclusion,ConstantSplit.sc,Category.assoc]
  exact hh
omit [X.IsConnected] [Y.IsConnected] in
@[reassoc (attr:=simp)] lemma redInclusion_projection (n:ℕ) :
    redInclusion X Y n ≫ projection X Y n=0 := by
  apply biprod.hom_ext <;> simp [projection,redInclusion_fst,redInclusion_snd]
lemma red_projection_recover (n:ℕ) (x:((X⊗Y).homology Z n : A))
    (hx:projection X Y n x=0) : redInclusion X Y n (redProjection X Y n x)=x := by
  apply sub_eq_zero.mp
  apply projection_joint_zero X Y n
  · rw [map_sub,hx,sub_zero]
    change (redInclusion X Y n≫projection X Y n) _=0
    rw [redInclusion_projection]; rfl
  · rw [map_sub]
    change (redInclusion X Y n≫redProjection X Y n) _ - _=0
    rw [redInclusion_redProjection]
    exact sub_self _
variable {X Y} {X' Y':SSet} [X'.IsConnected] [Y'.IsConnected]
omit [X.IsConnected] [Y.IsConnected] [X'.IsConnected] [Y'.IsConnected] in
@[reassoc] lemma redInclusion_natural (f:X⟶X') (g:Y⟶Y') (n:ℕ) :
    redInclusion X Y n ≫ SSet.homologyMap (f⊗ₘg) Z n =
      homologyMap (redMap f⊗ₘredMap g) n ≫ redInclusion X' Y' n := by
  apply (cancel_mono (homologyIsoN X' Y' n).hom).mp
  simp only [redInclusion,ConstantSplit.sc,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  erw [homology_natural, Iso.inv_hom_id_assoc,←homologyMap_comp,←homologyMap_comp,
    tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,redMap_inclusion,redMap_inclusion]
  rfl
lemma kernel_map_surjective (f:X⟶X') (g:Y⟶Y')
    [Subsingleton (X.obj (op ⦋0⦌))] [Subsingleton (Y.obj (op ⦋0⦌))]
    [Subsingleton (X'.obj (op ⦋0⦌))] [Subsingleton (Y'.obj (op ⦋0⦌))]
    [Epi (SSet.homologyMap f Z 1)] [Epi (SSet.homologyMap g Z 1)]
    (x:((X'⊗Y').homology Z 2 : A)) (hx:projection X' Y' 2 x=0) :
    ∃y:((X⊗Y).homology Z 2 : A), projection X Y 2 y=0 ∧ SSet.homologyMap (f⊗ₘg) Z 2 y=x := by
  have hf:=FreeChains.complexIso_natural f
  have : Epi (homologyMap (chainMap f) 1) := by
    have hh:=congrArg (fun k=>homologyMap k 1) hf
    simp only [homologyMap_comp] at hh
    have : Epi (homologyMap (FreeChains.complexIso X).hom 1 ≫ homologyMap (chainMap f) 1):=by rw [←hh]; infer_instance
    exact epi_of_epi (homologyMap (FreeChains.complexIso X).hom 1) _
  have : Epi (homologyMap (chainMap g) 1) := by
    have hh:=congrArg (fun k=>homologyMap k 1) (FreeChains.complexIso_natural g)
    simp only [homologyMap_comp] at hh
    have : Epi (homologyMap (FreeChains.complexIso Y).hom 1 ≫ homologyMap (chainMap g) 1):=by rw [←hh]; infer_instance
    exact epi_of_epi (homologyMap (FreeChains.complexIso Y).hom 1) _
  have :=redMap_epi f (point X) (point X') 1 (by decide)
  have :=redMap_epi g (point Y) (point Y') 1 (by decide)
  have :=ReducedTensorTwo.homology_epi (redMap f) (redMap g)
    (red_X_zero X (point X)) (red_X_zero Y (point Y))
    (red_X_zero X' (point X')) (red_X_zero Y' (point Y'))
  obtain ⟨y,hy⟩:=((ModuleCat.epi_iff_surjective (homologyMap (redMap f⊗ₘredMap g) 2)).mp inferInstance) (redProjection X' Y' 2 x)
  refine ⟨redInclusion X Y 2 y,?_,?_⟩
  · change (redInclusion X Y 2≫projection X Y 2) y=0
    rw [redInclusion_projection]; rfl
  · change (redInclusion X Y 2≫SSet.homologyMap (f⊗ₘg) Z 2) y=x
    rw [redInclusion_natural]
    change redInclusion X' Y' 2 (homologyMap (redMap f⊗ₘredMap g) 2 y)=x
    rw [hy,red_projection_recover X' Y' 2 x hx]
end ConnectedProduct

end

end OAI
