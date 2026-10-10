import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.TrajectoryStages
import OAI.GroupTheory.SimpleAmenable.Simplicial.TripleBarMaps

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.Labelled

variable {a n : ℕ}
noncomputable def initialCore : (toStrings (a:=a) (n:=n) ⋙ stringEval).CoreMonoidal :=
  Functor.Monoidal.coreMonoidalTransport initialIso
lemma initialCore_unit : (initialCore (a:=a) (n:=n)).εIso.hom=initial (𝟙_ _) := by
  change 𝟙 _ ≫ initial (𝟙_ _) = _
  exact Category.id_comp _
lemma initialCore_tensor (U V : Labelled a n) :
    (initialCore.μIso U V).hom=tensorInitial U V := by
  change (inv (initial U) ⊗ₘ inv (initial V)) ≫ 𝟙 _ ≫ initial (U⊗V) =
    inv (sumArrow (initial U) (initial V)) ≫ initial (U⊗V)
  simp only [Category.id_comp]
  congr 1
  apply (cancel_epi (sumArrow (initial U) (initial V))).mp
  change (initial U ⊗ₘ initial V) ≫ (inv (initial U) ⊗ₘ inv (initial V)) = _
  rw [tensorHom_comp_tensorHom]
  simp
  rfl
noncomputable def stringsCore : (toStrings (a:=a) (n:=n)).CoreMonoidal where
  εIso := @asIso (StringGroupoid a n) _ _ _ unitLadder
    (IsIso.of_groupoid (C := StringGroupoid a n) _)
  μIso U V := @asIso (StringGroupoid a n) _ _ _ (tensorLadder U V)
    (IsIso.of_groupoid (C := StringGroupoid a n) _)
  μIso_hom_natural_left := by
    intro U V f W
    apply (stringEval (a:=a) (n:=n)).map_injective
    change sumArrow ((ladder f).hom.app 0) (𝟙 _) ≫ (tensorLadder V W).hom.app 0 =
      (tensorLadder U W).hom.app 0 ≫ (ladder (f ▷ W)).hom.app 0
    rw [tensorLadder_zero,tensorLadder_zero,←initialCore_tensor,←initialCore_tensor]
    exact initialCore.μIso_hom_natural_left f W
  μIso_hom_natural_right := by
    intro U V W f
    apply (stringEval (a:=a) (n:=n)).map_injective
    change sumArrow (𝟙 _) ((ladder f).hom.app 0) ≫ (tensorLadder W V).hom.app 0 =
      (tensorLadder W U).hom.app 0 ≫ (ladder (W ◁ f)).hom.app 0
    rw [tensorLadder_zero,tensorLadder_zero,←initialCore_tensor,←initialCore_tensor]
    exact initialCore.μIso_hom_natural_right W f
  associativity := by
    intro U V W
    apply (stringEval (a:=a) (n:=n)).map_injective
    change sumArrow ((tensorLadder U V).hom.app 0) (𝟙 _) ≫
      (tensorLadder (U⊗V) W).hom.app 0 ≫ (ladder (α_ U V W).hom).hom.app 0 =
      sumAssoc _ _ _ ≫ sumArrow (𝟙 _) ((tensorLadder V W).hom.app 0) ≫
        (tensorLadder U (V⊗W)).hom.app 0
    simp only [tensorLadder_zero,←initialCore_tensor]
    exact initialCore.associativity U V W
  left_unitality := by
    intro U
    apply (stringEval (a:=a) (n:=n)).map_injective
    change leftUnit _ = sumArrow (unitLadder.hom.app 0) (𝟙 _) ≫
      (tensorLadder (𝟙_ _) U).hom.app 0 ≫ (ladder (λ_ U).hom).hom.app 0
    rw [unitLadder_zero,tensorLadder_zero,←initialCore_unit,←initialCore_tensor]
    exact initialCore.left_unitality U
  right_unitality := by
    intro U
    apply (stringEval (a:=a) (n:=n)).map_injective
    change rightUnit _ = sumArrow (𝟙 _) (unitLadder.hom.app 0) ≫
      (tensorLadder U (𝟙_ _)).hom.app 0 ≫ (ladder (ρ_ U).hom).hom.app 0
    rw [unitLadder_zero,tensorLadder_zero,←initialCore_unit,←initialCore_tensor]
    exact initialCore.right_unitality U
noncomputable instance : (toStrings (a:=a) (n:=n)).Monoidal := stringsCore.toMonoidal
noncomputable instance : (toStrings (a:=a) (n:=n)).Braided where
  braided U V := by
    apply (stringEval (a:=a) (n:=n)).map_injective
    change (tensorLadder U V).hom.app 0 ≫ (ladder (β_ U V).hom).hom.app 0 =
      sumSwap _ _ ≫ (tensorLadder V U).hom.app 0
    rw [tensorLadder_zero,tensorLadder_zero,ladder_zero]
    change (inv (sumArrow (initial U) (initial V)) ≫ initial (U⊗V)) ≫
        (inv (initial (U⊗V)) ≫ sumSwap _ _ ≫ initial (V⊗U)) =
      sumSwap _ _ ≫ inv (sumArrow (initial V) (initial U)) ≫ initial (V⊗U)
    simp only [Category.assoc,IsIso.hom_inv_id_assoc]
    apply (cancel_epi (sumArrow (initial U) (initial V))).mp
    simp only [IsIso.hom_inv_id_assoc]
    have h := BraidedCategory.braiding_naturality (initial U) (initial V)
    change sumArrow (initial U) (initial V) ≫ sumSwap _ _ =
      sumSwap _ _ ≫ sumArrow (initial V) (initial U) at h
    rw [←Category.assoc (sumArrow (initial U) (initial V)),h]
    simp

lemma tripleBar_homology_isIso (j : ℕ) :
    IsIso (SSet.homologyMap (IntervalBar.Diagram.bar₃Map (toStrings (a:=a) (n:=n)))
      DiagonalResolution.Z j) :=
  IntervalBar.Diagram.bar₃Map_homology_isIso toStrings j
end SimpleAmenable.PolygonObject.Labelled

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Classical
namespace SimpleAmenable.PolygonObject.LabelledStage

variable {a n : ℕ}
variable {I : Type} [Category.{0} I] [Finite I] [∀i j:I,Finite (i ⟶ j)]

theorem exists_common_stage (F : I ⥤ Labelled a n) :
    ∃ (P : BooleanPartition a) (s : ℕ) (L : Fin s → Fin n → CutRing × CutRing),
      (∀j i,orbitRepresentative (L j i)=L j i) ∧ Function.Injective L ∧
      ∃G : I ⥤ UniformObject P L, G ⋙ UniformObject.forget=F := by
  let : Fintype I := Fintype.ofFinite I
  let (i j : I) : Fintype (i ⟶ j) := Fintype.ofFinite (i ⟶ j)
  let Ar := Σi:I,Σj:I,i ⟶ j
  let u : Ar → I := fun t => t.1
  let v : Ar → I := fun t => t.2.1
  let f : ∀t:Ar,F.obj (u t) ⟶ F.obj (v t) := fun t => F.map t.2.2
  obtain ⟨P,hP,hf⟩ := Labelled.exists_uniform_partition F.obj u v f
  let label : (Σi:I,Fin (F.obj i).polygon.tracks) → Fin n → CutRing × CutRing :=
    fun t => (F.obj t.1).label t.2
  let S := Set.range label
  have : Fintype S := (Set.finite_range label).fintype
  let L : Fin (Fintype.card S) → Fin n → CutRing × CutRing :=
    fun j => ((Fintype.equivFin S).symm j).val
  have hL : ∀j i,orbitRepresentative (L j i)=L j i := by
    intro j i
    obtain ⟨⟨k,t⟩,hk⟩ := ((Fintype.equivFin S).symm j).property
    change orbitRepresentative (((Fintype.equivFin S).symm j).val i)=(((Fintype.equivFin S).symm j).val i)
    rw [←hk]
    exact (F.obj k).reduced t i
  have hLi : Function.Injective L := by
    intro i j h
    exact (Fintype.equivFin S).symm.injective (Subtype.ext h)
  let obj (i : I) : UniformObject P L := {
    obj := F.obj i
    uniform := hP i
    supported := fun j => ⟨Fintype.equivFin S ⟨label ⟨i,j⟩,⟨⟨i,j⟩,rfl⟩⟩,by
      simp only [L,Equiv.symm_apply_apply]; rfl⟩ }
  let G : I ⥤ UniformObject P L := {
    obj := obj
    map {i j} g := ⟨F.map g,hf ⟨i,j,g⟩⟩
    map_id i := UniformObject.Hom.ext _ _ (F.map_id i)
    map_comp g h := UniformObject.Hom.ext _ _ (F.map_comp g h) }
  refine ⟨P,Fintype.card S,L,hL,hLi,G,?_⟩
  rfl
end SimpleAmenable.PolygonObject.LabelledStage

end

end

end OAI
