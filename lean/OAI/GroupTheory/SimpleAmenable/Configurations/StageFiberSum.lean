import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.UniformMonoidal
import OAI.GroupTheory.SimpleAmenable.Simplicial.FiniteSetMonoidal

namespace OAI

section

section
open CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage.UniformObject

variable {a n s : ℕ} {P : BooleanPartition a} {L : Fin s → Fin n → CutRing × CutRing}
variable (U V : UniformObject P L) (b : Fin P.size × Fin s)
noncomputable def fiberSumFun : Fiber U b ⊕ Fiber V b → Fiber (sum U V) b
  | .inl x => ⟨sumPointEquiv U.obj.polygon V.obj.polygon (.inl x.val),by
      simpa only [sumPointEquiv_inl] using x.property.1,by
      simpa only [sum,Labelled.sum,sumPointEquiv_inl,Fin.addCases_left] using x.property.2⟩
  | .inr y => ⟨sumPointEquiv U.obj.polygon V.obj.polygon (.inr y.val),by
      simpa only [sumPointEquiv_inr] using y.property.1,by
      simpa only [sum,Labelled.sum,sumPointEquiv_inr,Fin.addCases_right] using y.property.2⟩
noncomputable def fiberSum : Fiber U b ⊕ Fiber V b ≃ Fiber (sum U V) b :=
  Equiv.ofBijective (fiberSumFun U V b) ⟨by
    intro x y h
    have h' := congrArg Subtype.val h
    cases x <;> cases y
    · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj ((sumPointEquiv _ _).injective h')))
    · cases ((sumPointEquiv _ _).injective h')
    · cases ((sumPointEquiv _ _).injective h')
    · exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj ((sumPointEquiv _ _).injective h'))),by
    intro z
    obtain ⟨x,hx⟩ := (sumPointEquiv U.obj.polygon V.obj.polygon).surjective z.val
    cases x with
    | inl x =>
      have hp : x.val.2=P.point b.1 ∧ U.obj.label x.val.1=L b.2 := by
        simpa only [←hx,sumPointEquiv_inl,sum,Labelled.sum,Fin.addCases_left] using z.property
      exact ⟨.inl ⟨x,hp⟩,Subtype.ext hx⟩
    | inr x =>
      have hp : x.val.2=P.point b.1 ∧ V.obj.label x.val.1=L b.2 := by
        simpa only [←hx,sumPointEquiv_inr,sum,Labelled.sum,Fin.addCases_right] using z.property
      exact ⟨.inr ⟨x,hp⟩,Subtype.ext hx⟩⟩
@[simp] lemma fiberSum_inl (x : Fiber U b) :
    (fiberSum U V b (.inl x)).val=sumPointEquiv U.obj.polygon V.obj.polygon (.inl x.val) := rfl
@[simp] lemma fiberSum_inr (x : Fiber V b) :
    (fiberSum U V b (.inr x)).val=sumPointEquiv U.obj.polygon V.obj.polygon (.inr x.val) := rfl

noncomputable abbrev E := evaluation (P:=P) (L:=L)
noncomputable def enumerate (U : UniformObject P L) (b : Fin P.size × Fin s) : Fiber U b ≃ Fin (E.obj U b).size := Fintype.equivFin (Fiber U b)
@[simp] lemma E_map_enum {U V : UniformObject P L} (f : U ⟶ V) (b : Fin P.size × Fin s) (x : Fiber U b) :
    E.map f b (enumerate U b x)=enumerate V b (fiberMap f b x) := by
  change enumerate V b (fiberMap f b ((enumerate U b).symm (enumerate U b x)))=_
  rw [Equiv.symm_apply_apply]
noncomputable def mu (U V : UniformObject P L) : E.obj U ⊗ E.obj V ⟶ E.obj (U⊗V) := fun b =>
  (FiniteSetGroupoid.sumEquiv _ _).symm.trans
    ((Equiv.sumCongr (enumerate U b).symm (enumerate V b).symm).trans
      ((fiberSum U V b).trans (enumerate (sum U V) b)))
@[simp] lemma mu_inl (x : Fiber U b) :
    mu U V b (FiniteSetGroupoid.sumEquiv _ _ (.inl (enumerate U b x)))=
      enumerate (sum U V) b (fiberSum U V b (.inl x)) := by
  change (enumerate (sum U V) b) ((fiberSum U V b) ((Equiv.sumCongr (enumerate U b).symm (enumerate V b).symm)
    ((FiniteSetGroupoid.sumEquiv (E.obj U b) (E.obj V b)).symm
    ((FiniteSetGroupoid.sumEquiv (E.obj U b) (E.obj V b)) _)))) = _
  rw [Equiv.symm_apply_apply]
  simp only [Equiv.sumCongr_apply,Sum.map_inl,Equiv.symm_apply_apply]
@[simp] lemma mu_inr (x : Fiber V b) :
    mu U V b (FiniteSetGroupoid.sumEquiv _ _ (.inr (enumerate V b x)))=
      enumerate (sum U V) b (fiberSum U V b (.inr x)) := by
  change (enumerate (sum U V) b) ((fiberSum U V b) ((Equiv.sumCongr (enumerate U b).symm (enumerate V b).symm)
    ((FiniteSetGroupoid.sumEquiv (E.obj U b) (E.obj V b)).symm
    ((FiniteSetGroupoid.sumEquiv (E.obj U b) (E.obj V b)) _)))) = _
  rw [Equiv.symm_apply_apply]
  simp only [Equiv.sumCongr_apply,Sum.map_inr,Equiv.symm_apply_apply]
lemma fiberMap_sum_inl {U V W Z : UniformObject P L} (f : U ⟶ W) (g : V ⟶ Z)
    (b : Fin P.size × Fin s) (x : Fiber U b) :
    fiberMap (sumHom f g) b (fiberSum U V b (.inl x))=
      fiberSum W Z b (.inl (fiberMap f b x)) := by
  apply Subtype.ext
  exact sumArrow_inl f.arrow.arrow g.arrow.arrow x.val
lemma fiberMap_sum_inr {U V W Z : UniformObject P L} (f : U ⟶ W) (g : V ⟶ Z)
    (b : Fin P.size × Fin s) (x : Fiber V b) :
    fiberMap (sumHom f g) b (fiberSum U V b (.inr x))=
      fiberSum W Z b (.inr (fiberMap g b x)) := by
  apply Subtype.ext
  exact sumArrow_inr f.arrow.arrow g.arrow.arrow x.val
end SimpleAmenable.PolygonObject.LabelledStage.UniformObject

end

section
open CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage.UniformObject

variable {a n s : ℕ} {P : BooleanPartition a} {L : Fin s → Fin n → CutRing × CutRing}
instance fiberEmpty (b : Fin P.size × Fin s) : IsEmpty (Fiber (empty (P:=P) (L:=L)) b) :=
  ⟨fun x => isEmptyElim x.val⟩
noncomputable def eps : 𝟙_ (Obj P (s:=s)) ⟶ E.obj (𝟙_ (UniformObject P L)) := fun b =>
  (Equiv.equivOfIsEmpty (Fin 0) (Fiber empty b)).trans (enumerate empty b)
@[simp] lemma fiberMap_id (U : UniformObject P L) (b : Fin P.size × Fin s) (x : Fiber U b) :
    fiberMap (𝟙 U) b x=x := rfl
lemma mu_natural {U V W Z : UniformObject P L} (f : U ⟶ W) (g : V ⟶ Z) :
    (E.map f ⊗ₘ E.map g) ≫ mu W Z = mu U V ≫ E.map (f⊗ₘg) := by
  funext b
  apply Equiv.ext
  intro x
  obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv (E.obj U b) (E.obj V b)).surjective x
  cases x with
  | inl x =>
    obtain ⟨x,rfl⟩ := (enumerate U b).surjective x
    change mu W Z b (FiniteSetGroupoid.sumHom (E.map f b) (E.map g b) _) = E.map (sumHom f g) b _
    rw [FiniteSetGroupoid.sumHom_inl,E_map_enum,mu_inl,mu_inl,E_map_enum,fiberMap_sum_inl]
  | inr x =>
    obtain ⟨x,rfl⟩ := (enumerate V b).surjective x
    change mu W Z b (FiniteSetGroupoid.sumHom (E.map f b) (E.map g b) _) = E.map (sumHom f g) b _
    rw [FiniteSetGroupoid.sumHom_inr,E_map_enum,mu_inr,mu_inr,E_map_enum,fiberMap_sum_inr]

variable (U V W : UniformObject P L) (b : Fin P.size × Fin s)
@[simp] lemma fiber_assoc_left (x : Fiber U b) :
    fiberMap (assocHom U V W) b (fiberSum (sum U V) W b (.inl (fiberSum U V b (.inl x))))=
      fiberSum U (sum V W) b (.inl x) := by
  apply Subtype.ext
  change sumAssocEquiv U.obj.polygon V.obj.polygon W.obj.polygon _ = _
  exact sumAssocEquiv_left _ _ _ x.val
@[simp] lemma fiber_assoc_mid (x : Fiber V b) :
    fiberMap (assocHom U V W) b (fiberSum (sum U V) W b (.inl (fiberSum U V b (.inr x))))=
      fiberSum U (sum V W) b (.inr (fiberSum V W b (.inl x))) := by
  apply Subtype.ext
  change sumAssocEquiv U.obj.polygon V.obj.polygon W.obj.polygon _ = _
  exact sumAssocEquiv_mid _ _ _ x.val
@[simp] lemma fiber_assoc_right (x : Fiber W b) :
    fiberMap (assocHom U V W) b (fiberSum (sum U V) W b (.inr x))=
      fiberSum U (sum V W) b (.inr (fiberSum V W b (.inr x))) := by
  apply Subtype.ext
  change sumAssocEquiv U.obj.polygon V.obj.polygon W.obj.polygon _ = _
  exact sumAssocEquiv_right _ _ _ x.val
@[simp] lemma fiber_left (x : Fiber U b) :
    fiberMap (leftHom U) b (fiberSum empty U b (.inr x))=x := by
  apply Subtype.ext
  exact leftUnitEquiv_apply _ x.val
@[simp] lemma fiber_right (x : Fiber U b) :
    fiberMap (rightHom U) b (fiberSum U empty b (.inl x))=x := by
  apply Subtype.ext
  exact rightUnitEquiv_apply _ x.val
@[simp] lemma fiber_swap_left (x : Fiber U b) :
    fiberMap (swapHom U V) b (fiberSum U V b (.inl x))=fiberSum V U b (.inr x) := by
  apply Subtype.ext
  exact sumSwapEquiv_inl _ _ x.val
@[simp] lemma fiber_swap_right (x : Fiber V b) :
    fiberMap (swapHom U V) b (fiberSum U V b (.inr x))=fiberSum V U b (.inl x) := by
  apply Subtype.ext
  exact sumSwapEquiv_inr _ _ x.val
end SimpleAmenable.PolygonObject.LabelledStage.UniformObject

end

end

end OAI
