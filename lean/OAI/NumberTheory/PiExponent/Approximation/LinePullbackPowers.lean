import OAI.NumberTheory.PiExponent.Approximation.SectionOpens
import OAI.NumberTheory.PiExponent.Approximation.TensorOpenBaseChange

namespace OAI

noncomputable section

namespace PiExponentSeshadri.PullbackTensor
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MonoidalCategory
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

def hom (M N : Y.Modules) : (Scheme.Modules.pullback f).obj (moduleTensor Y M N) ⟶
    moduleTensor X ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (moduleTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
      PushforwardTensor.hom f _ _)

lemma unit_hom (M N : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (moduleTensor Y M N) ≫
      (Scheme.Modules.pushforward f).map (hom f M N) =
    moduleTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
      PushforwardTensor.hom f _ _ :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).apply_symm_apply _

@[reassoc] lemma naturality {M N P Q : Y.Modules} (a : M ⟶ P) (b : N ⟶ Q) :
    (Scheme.Modules.pullback f).map (moduleTensorMap a b) ≫ hom f P Q =
      hom f M N ≫ moduleTensorMap ((Scheme.Modules.pullback f).map a)
        ((Scheme.Modules.pullback f).map b) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left,Adjunction.homEquiv_naturality_right]
  simp only [hom,Equiv.apply_symm_apply]
  rw [← Category.assoc,← moduleTensorMap_comp]
  rw [Category.assoc,← PushforwardTensor.naturality,← Category.assoc,← moduleTensorMap_comp]
  rw [← (Scheme.Modules.pullbackPushforwardAdjunction f).unit_naturality,
    ← (Scheme.Modules.pullbackPushforwardAdjunction f).unit_naturality]

lemma unit_pure_structure (Z : Scheme.{0}) (U : Z.Opens)
    (a b : (O Z).val.obj (op U)) :
    (moduleTensorUnit (O Z)).hom.app U (pure (O Z) (O Z) U a b) =
      (show Γ(Z,U) from a) * (show Γ(Z,U) from b) :=
  TensorPure.unit_pure (O Z) U a b

lemma unit_compatibility :
    hom f (O Y) (O Y) ≫
      (moduleTensorIso (pullbackUnitIso f) (pullbackUnitIso f)).hom ≫
      (moduleTensorUnit (O X)).hom =
    (Scheme.Modules.pullback f).map (moduleTensorUnit (O Y)).hom ≫
      (pullbackUnitIso f).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have hl := adj.homEquiv_naturality_left (moduleTensorUnit (O Y)).hom
    (pullbackUnitIso f).hom
  have hr := adj.homEquiv_naturality_right (hom f (O Y) (O Y))
    ((moduleTensorIso (pullbackUnitIso f) (pullbackUnitIso f)).hom ≫
      (moduleTensorUnit (O X)).hom)
  have hu := congrArg (fun q => (moduleTensorUnit (O Y)).hom ≫ q)
    (pullbackUnit_adjunction f)
  refine hr.trans (Eq.trans ?_ (hu.symm.trans hl.symm))
  simp only [adj, hom, Equiv.apply_symm_apply]
  apply TensorPure.hom_ext
  intro U a b
  change (moduleTensorUnit (O X)).hom.app (f ⁻¹ᵁ U)
    ((moduleTensorMap (pullbackUnitIso f).hom (pullbackUnitIso f).hom).app (f ⁻¹ᵁ U)
      ((PushforwardTensor.hom f _ _).app U ((moduleTensorMap _ _).app U
        (pure (O Y) (O Y) U a b)))) =
    (f.app U) ((moduleTensorUnit (O Y)).hom.app U (pure (O Y) (O Y) U a b))
  let η := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y)
  let m := η.app U a
  let n := η.app U b
  have h₁ := congrArg (fun z => (moduleTensorUnit (O X)).hom.app (f ⁻¹ᵁ U)
    ((moduleTensorMap (pullbackUnitIso f).hom (pullbackUnitIso f).hom).app (f ⁻¹ᵁ U)
      ((PushforwardTensor.hom f _ _).app U z)))
    (TensorPure.map_pure η η U a b)
  have h₂ := congrArg (fun z => (moduleTensorUnit (O X)).hom.app (f ⁻¹ᵁ U)
    ((moduleTensorMap (pullbackUnitIso f).hom (pullbackUnitIso f).hom).app (f ⁻¹ᵁ U) z))
    (PushforwardTensor.hom_pure f ((Scheme.Modules.pullback f).obj (O Y))
      ((Scheme.Modules.pullback f).obj (O Y)) U m n)
  have h₃ := congrArg (fun z => (moduleTensorUnit (O X)).hom.app (f ⁻¹ᵁ U) z)
    (TensorPure.map_pure (pullbackUnitIso f).hom (pullbackUnitIso f).hom (f ⁻¹ᵁ U) m n)
  refine h₁.trans (h₂.trans (h₃.trans ((unit_pure_structure X (f ⁻¹ᵁ U) _ _).trans ?_)))
  have hy := congrArg (fun z => (f.app U) z) (unit_pure_structure Y U a b)
  refine Eq.trans ?_ hy.symm
  have hu := congrArg (fun q => q.app U) (pullbackUnit_adjunction f)
  have ha := congrArg (fun q => q a) hu
  have hb := congrArg (fun q => q b) hu
  change (pullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y)).app U a) =
    (f.app U) a at ha
  change (pullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y)).app U b) =
    (f.app U) b at hb
  exact (congrArg₂ (fun a b : Γ(X,f ⁻¹ᵁ U) => a * b) ha hb).trans
    (map_mul (f.app U).hom (show Γ(Y,U) from a) (show Γ(Y,U) from b)).symm

instance unit_isIso : IsIso (hom f (O Y) (O Y)) := by
  let e := (Scheme.Modules.pullback f).mapIso (moduleTensorUnit (O Y)) ≪≫
    pullbackUnitIso f
  let d := moduleTensorIso (pullbackUnitIso f) (pullbackUnitIso f) ≪≫
    moduleTensorUnit (O X)
  have hi : IsIso (hom f (O Y) (O Y) ≫ d.hom) := by
    change IsIso (hom f (O Y) (O Y) ≫
      (moduleTensorIso (pullbackUnitIso f) (pullbackUnitIso f)).hom ≫
      (moduleTensorUnit (O X)).hom)
    rw [unit_compatibility]
    exact e.isIso_hom
  let hd : IsIso (C := X.Modules) d.hom := d.isIso_hom
  exact (@isIso_comp_right_iff X.Modules _ _ _ _ _ _ hd).mp hi

lemma open_transpose (M : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _
      ((OpenBaseChange.leftSquare f U).hom.app M) =
    (Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
        (OpenBaseChange.iso f U ((Scheme.Modules.pullback f).obj M)).hom :=
  (OpenBaseChange.unit_compatibility f U M).symm

lemma restrict_compatibility (M N : Y.Modules) :
    (OpenBaseChange.leftSquare f U).hom.app (moduleTensor Y M N) ≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map (hom f M N) ≫
      (moduleTensorRestrict (f ⁻¹ᵁ U) ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N)).hom =
    (Scheme.Modules.pullback (f ∣_ U)).map (moduleTensorRestrict U M N).hom ≫
      hom (f ∣_ U) (M.restrict U.ι) (N.restrict U.ι) ≫
      moduleTensorMap ((OpenBaseChange.leftSquare f U).hom.app M)
        ((OpenBaseChange.leftSquare f U).hom.app N) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _).injective
  conv_rhs => rw [Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  conv_lhs => rw [Adjunction.homEquiv_naturality_right]
  rw [open_transpose]
  have ht : (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _
      (hom (f ∣_ U) (M.restrict U.ι) (N.restrict U.ι)) =
      moduleTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (M.restrict U.ι))
        ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (N.restrict U.ι)) ≫
        PushforwardTensor.hom (f ∣_ U) _ _ := Equiv.apply_symm_apply _ _
  rw [ht]
  simp only [Functor.map_comp, Category.assoc]
  rw [← OpenBaseChange.naturality_assoc]
  rw [← Functor.map_comp_assoc, unit_hom, Functor.map_comp]
  simp only [Category.assoc]
  rw [OpenBaseChange.tensor_square]
  rw [← Category.assoc]
  refine (congrArg (fun q => q ≫
    moduleTensorMap (OpenBaseChange.iso f U ((Scheme.Modules.pullback f).obj M)).hom
      (OpenBaseChange.iso f U ((Scheme.Modules.pullback f).obj N)).hom ≫
    PushforwardTensor.hom (f ∣_ U)
      (((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι)
      (((Scheme.Modules.pullback f).obj N).restrict (f ⁻¹ᵁ U).ι))
    (TensorPure.restrict_map U
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N))).trans ?_
  simp only [Category.assoc]
  rw [← moduleTensorMap_comp_assoc]
  rw [OpenBaseChange.unit_compatibility,OpenBaseChange.unit_compatibility]
  rw [moduleTensorMap_comp]
  simp only [Category.assoc]
  exact congrArg (fun q => (moduleTensorRestrict U M N).hom ≫
    moduleTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (M.restrict U.ι))
      ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (N.restrict U.ι)) ≫ q)
    (PushforwardTensor.naturality (f ∣_ U)
      ((OpenBaseChange.leftSquare f U).hom.app M) ((OpenBaseChange.leftSquare f U).hom.app N))

lemma framed_isIso (M N : Y.Modules) (e : M ≅ O Y) (d : N ≅ O Y) :
    IsIso (hom f M N) := by
  have h := naturality f e.hom d.hom
  have : IsIso ((Scheme.Modules.pullback f).map (moduleTensorMap e.hom d.hom) ≫
      hom f (O Y) (O Y)) := by
    change IsIso ((Scheme.Modules.pullback f).map (moduleTensorIso e d).hom ≫ _)
    infer_instance
  have : IsIso (moduleTensorMap ((Scheme.Modules.pullback f).map e.hom)
      ((Scheme.Modules.pullback f).map d.hom)) := by
    change IsIso (moduleTensorIso ((Scheme.Modules.pullback f).mapIso e)
      ((Scheme.Modules.pullback f).mapIso d)).hom
    infer_instance
  have hi : IsIso (hom f M N ≫ moduleTensorMap ((Scheme.Modules.pullback f).map e.hom)
      ((Scheme.Modules.pullback f).map d.hom)) := h ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp hi

instance power_step_isIso (L : LineBundle Y) (n : ℕ) :
    IsIso (hom f L.sheaf (L.pow n).sheaf) := by
  apply PiExponentSeshadri.SectionOpens.isIso_of_locally_isIso
  intro x
  obtain ⟨U,hx,⟨e⟩⟩ := L.locallyRankOne (f x)
  let d := modulePowFrame U e n
  refine ⟨f ⁻¹ᵁ U,hx,?_⟩
  let : IsIso (hom (f ∣_ U) (L.sheaf.restrict U.ι) ((L.pow n).sheaf.restrict U.ι)) :=
    framed_isIso (f ∣_ U) _ _ e d
  have : IsIso (moduleTensorMap ((OpenBaseChange.leftSquare f U).hom.app L.sheaf)
      ((OpenBaseChange.leftSquare f U).hom.app (L.pow n).sheaf)) := by
    change IsIso (moduleTensorIso ((OpenBaseChange.leftSquare f U).app L.sheaf)
      ((OpenBaseChange.leftSquare f U).app (L.pow n).sheaf)).hom
    infer_instance
  have h := restrict_compatibility f U L.sheaf (L.pow n).sheaf
  have : IsIso ((OpenBaseChange.leftSquare f U).hom.app (moduleTensor Y L.sheaf (L.pow n).sheaf) ≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map (hom f L.sheaf (L.pow n).sheaf) ≫
      (moduleTensorRestrict (f ⁻¹ᵁ U) ((Scheme.Modules.pullback f).obj L.sheaf)
        ((Scheme.Modules.pullback f).obj (L.pow n).sheaf)).hom) := by rw [h]; infer_instance
  have hi : IsIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map
      (hom f L.sheaf (L.pow n).sheaf) ≫
      (moduleTensorRestrict (f ⁻¹ᵁ U) ((Scheme.Modules.pullback f).obj L.sheaf)
        ((Scheme.Modules.pullback f).obj (L.pow n).sheaf)).hom) :=
    (isIso_comp_left_iff ((OpenBaseChange.leftSquare f U).hom.app
      (moduleTensor Y L.sheaf (L.pow n).sheaf)) _).mp inferInstance
  exact (isIso_comp_right_iff _ _).mp hi

def powIso (L : LineBundle Y) : ∀ n : ℕ,
    (Scheme.Modules.pullback f).obj (L.pow n).sheaf ≅ ((L.pullback f).pow n).sheaf
  | 0 => pullbackUnitIso f
  | n+1 => @asIso _ _ _ _ (hom f L.sheaf (L.pow n).sheaf) (power_step_isIso f L n) ≪≫
      moduleTensorIso (Iso.refl _) (powIso L n)

end PiExponentSeshadri.PullbackTensor

end

end OAI
