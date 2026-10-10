import OAI.NumberTheory.PiExponent.Approximation.CoherentTwistPresentation
import OAI.NumberTheory.PiExponent.Approximation.LinePullback
import OAI.NumberTheory.PiExponent.Approximation.SectionOpens
import OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange

namespace OAI

namespace PiExponent.ProjectionFormula
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure
variable {X Y : Scheme.{0}} (f : X ⟶ Y)

def hom (M : X.Modules) (L : Y.Modules) :
    moduleTensor Y ((Scheme.Modules.pushforward f).obj M) L ⟶
      (Scheme.Modules.pushforward f).obj
        (moduleTensor X M ((Scheme.Modules.pullback f).obj L)) :=
  moduleTensorMap (𝟙 _) ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L) ≫
    PiExponentSeshadri.PushforwardTensor.hom f _ _

lemma hom_pure (M : X.Modules) (L : Y.Modules) (U : Y.Opens)
    (m : M.val.obj (op (f ⁻¹ᵁ U))) (s : L.val.obj (op U)) :
    (hom f M L).app U (pure ((Scheme.Modules.pushforward f).obj M) L U m s) =
      pure M ((Scheme.Modules.pullback f).obj L) (f ⁻¹ᵁ U) m
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).app U s) := by
  have ht := map_pure (𝟙 ((Scheme.Modules.pushforward f).obj M))
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L) U m s
  have hp := PiExponentSeshadri.PushforwardTensor.hom_pure f M
    ((Scheme.Modules.pullback f).obj L) U m
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).app U s)
  exact (congrArg (fun z => (PiExponentSeshadri.PushforwardTensor.hom f M
    ((Scheme.Modules.pullback f).obj L)).app U z) ht).trans hp

@[reassoc] lemma naturality {M N : X.Modules} {L K : Y.Modules}
    (a : M ⟶ N) (b : L ⟶ K) :
    moduleTensorMap ((Scheme.Modules.pushforward f).map a) b ≫ hom f N K =
      hom f M L ≫ (Scheme.Modules.pushforward f).map
        (moduleTensorMap a ((Scheme.Modules.pullback f).map b)) := by
  unfold hom
  rw [← Category.assoc, ← moduleTensorMap_comp]
  rw [Category.comp_id, ← (Scheme.Modules.pullbackPushforwardAdjunction f).unit_naturality]
  have ht := moduleTensorMap_comp (𝟙 _) ((Scheme.Modules.pushforward f).map a)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L)
    ((Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map b))
  simp only [Category.id_comp] at ht
  rw [ht, Category.assoc, PiExponentSeshadri.PushforwardTensor.naturality]
  simp only [Category.assoc]

lemma pullback_unit_apply (U : Y.Opens) (a : Γ(Y,U)) :
    (pullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (structureSheaf Y)).app U a) =
    (f.app U) a := by
  have hu := congrArg (fun q => q.app U a) (pullbackUnit_adjunction f)
  exact hu

lemma unit_compatibility (M : X.Modules) :
    hom f M (structureSheaf Y) ≫
      (Scheme.Modules.pushforward f).map
        (moduleTensorMap (𝟙 M) (pullbackUnitIso f).hom ≫ (moduleTensorRightUnit M).hom) =
      (moduleTensorRightUnit ((Scheme.Modules.pushforward f).obj M)).hom := by
  apply PiExponentSeshadri.TensorPure.hom_ext
  intro U m a
  change Γ(M, f ⁻¹ᵁ U) at m
  change Γ(Y,U) at a
  let b : ((Scheme.Modules.pullback f).obj (structureSheaf Y)).val.obj (op (f ⁻¹ᵁ U)) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (structureSheaf Y)).app U a
  have hp := hom_pure f M (structureSheaf Y) U m a
  have ht := map_pure (𝟙 M) (pullbackUnitIso f).hom (f ⁻¹ᵁ U) m b
  have hu := right_unit_pure M (f ⁻¹ᵁ U) m ((pullbackUnitIso f).hom.app (f ⁻¹ᵁ U) b)
  have hv := right_unit_pure ((Scheme.Modules.pushforward f).obj M) U m a
  have hs := congrArg (fun r : Γ(X, f ⁻¹ᵁ U) => r • m) (pullback_unit_apply f U a)
  exact (congrArg (fun z => (moduleTensorRightUnit M).hom.app (f ⁻¹ᵁ U)
    ((moduleTensorMap (𝟙 M) (pullbackUnitIso f).hom).app (f ⁻¹ᵁ U) z)) hp).trans
    ((congrArg (fun z => (moduleTensorRightUnit M).hom.app (f ⁻¹ᵁ U) z) ht).trans
      (hu.trans (hs.trans hv.symm)))

instance unit_isIso (M : X.Modules) : IsIso (hom f M (structureSheaf Y)) := by
  let e : moduleTensor X M ((Scheme.Modules.pullback f).obj (structureSheaf Y)) ≅ M :=
    moduleTensorIso (Iso.refl M) (pullbackUnitIso f) ≪≫ moduleTensorRightUnit M
  have hi : IsIso (hom f M (structureSheaf Y) ≫
      (Scheme.Modules.pushforward f).map
        (moduleTensorMap (𝟙 M) (pullbackUnitIso f).hom ≫ (moduleTensorRightUnit M).hom)) := by
    rw [unit_compatibility]
    infer_instance
  exact (isIso_comp_right_iff (C := Y.Modules) (hom f M (structureSheaf Y))
    ((Scheme.Modules.pushforward f).mapIso e).hom).mp hi

lemma framed_isIso (M : X.Modules) (L : Y.Modules) (e : L ≅ structureSheaf Y) :
    IsIso (hom f M L) := by
  have hn := naturality f (𝟙 M) e.hom
  have hi : IsIso (moduleTensorMap ((Scheme.Modules.pushforward f).map (𝟙 M)) e.hom ≫
      hom f M (structureSheaf Y)) := by
    infer_instance
  have hj : IsIso (hom f M L ≫ (Scheme.Modules.pushforward f).map
      (moduleTensorMap (𝟙 M) ((Scheme.Modules.pullback f).map e.hom))) := by
    rw [← hn]
    exact hi
  exact (isIso_comp_right_iff _ _).mp hj

lemma restrict_compatibility (U : Y.Opens) (M : X.Modules) (L : Y.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).map (hom f M L) ≫
      (PiExponentSeshadri.OpenBaseChange.iso f U
        (moduleTensor X M ((Scheme.Modules.pullback f).obj L))).hom ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        (moduleTensorRestrict (f ⁻¹ᵁ U) M ((Scheme.Modules.pullback f).obj L)).hom =
    (moduleTensorRestrict U ((Scheme.Modules.pushforward f).obj M) L).hom ≫
      moduleTensorMap (PiExponentSeshadri.OpenBaseChange.iso f U M).hom (𝟙 _) ≫
      hom (f ∣_ U) (M.restrict (f ⁻¹ᵁ U).ι) (L.restrict U.ι) ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        (moduleTensorMap (𝟙 _) ((PiExponentSeshadri.OpenBaseChange.leftSquare f U).hom.app L)) := by
  unfold hom
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [PiExponentSeshadri.OpenBaseChange.tensor_square]
  rw [← Category.assoc, ← Category.assoc]
  erw [PiExponentSeshadri.TensorPure.restrict_map U (𝟙 ((Scheme.Modules.pushforward f).obj M))
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L)]
  simp only [Category.assoc]
  rw [← moduleTensorMap_comp_assoc]
  erw [(Scheme.Modules.restrictFunctor U.ι).map_id]
  rw [Category.id_comp, PiExponentSeshadri.OpenBaseChange.unit_compatibility]
  have ht := moduleTensorMap_comp
    (PiExponentSeshadri.OpenBaseChange.iso f U M).hom (𝟙 _)
    ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (L.restrict U.ι))
    ((Scheme.Modules.pushforward (f ∣_ U)).map
      ((PiExponentSeshadri.OpenBaseChange.leftSquare f U).hom.app L))
  simp only [Category.comp_id] at ht
  rw [ht]
  simp only [Category.assoc]
  have hn := PiExponentSeshadri.PushforwardTensor.naturality (f ∣_ U)
    (𝟙 (M.restrict (f ⁻¹ᵁ U).ι))
    ((PiExponentSeshadri.OpenBaseChange.leftSquare f U).hom.app L)
  erw [(Scheme.Modules.pushforward (f ∣_ U)).map_id] at hn
  erw [hn]
  rw [← moduleTensorMap_comp_assoc, Category.comp_id, Category.id_comp]
  rfl

instance line_isIso (M : X.Modules) (L : LineBundle Y) : IsIso (hom f M L.sheaf) := by
  apply PiExponentSeshadri.SectionOpens.isIso_of_locally_isIso
  intro y
  obtain ⟨U, hy, ⟨e⟩⟩ := L.locallyRankOne y
  refine ⟨U, hy, ?_⟩
  let : IsIso (hom (f ∣_ U) (M.restrict (f ⁻¹ᵁ U).ι) (L.sheaf.restrict U.ι)) :=
    framed_isIso (f ∣_ U) _ _ e
  have hi : IsIso ((Scheme.Modules.restrictFunctor U.ι).map (hom f M L.sheaf) ≫
      (PiExponentSeshadri.OpenBaseChange.iso f U
        (moduleTensor X M ((Scheme.Modules.pullback f).obj L.sheaf))).hom ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        (moduleTensorRestrict (f ⁻¹ᵁ U) M ((Scheme.Modules.pullback f).obj L.sheaf)).hom) := by
    rw [restrict_compatibility]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hi

def iso (M : X.Modules) (L : LineBundle Y) :
    moduleTensor Y ((Scheme.Modules.pushforward f).obj M) L.sheaf ≅
      (Scheme.Modules.pushforward f).obj (moduleTensor X M (L.pullback f).sheaf) :=
  @asIso Y.Modules _ _ _ (hom f M L.sheaf) (line_isIso f M L)

def twistIso (M : X.Modules) (L : LineBundle Y) : ∀ n : ℕ,
    (Scheme.Modules.pushforward f).obj ((moduleTwistFunctor (L.pullback f) n).obj M) ≅
      (moduleTwistFunctor L n).obj ((Scheme.Modules.pushforward f).obj M)
  | 0 => Iso.refl _
  | n+1 => (iso f ((moduleTwistFunctor (L.pullback f) n).obj M) L).symm ≪≫
      moduleTensorIso (twistIso M L n) (Iso.refl _)

end
end PiExponent.ProjectionFormula

end OAI
