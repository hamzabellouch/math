import OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction
import OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula
import OAI.NumberTheory.PiExponent.Approximation.TwistPowerSection
import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule

namespace OAI

namespace PiExponent.ClosedRestrictionTensor
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure

lemma tensor_map_pure_val {Z : Scheme.{0}} {M N P Q : Z.Modules}
    (a : M ⟶ P) (b : N ⟶ Q) (U : Z.Opens)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensorMap a b).val.app (op U) (pure M N U m n) =
      pure P Q U (a.val.app (op U) m) (b.val.app (op U) n) :=
  map_pure a b U m n

lemma tensor_comm_pure_val {Z : Scheme.{0}} (M N : Z.Modules) (U : Z.Opens)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensorComm M N).hom.val.app (op U) (pure M N U m n) =
      pure N M U n m := moduleTensorComm_pure M N U m n

lemma projection_hom_pure_val {X Y : Scheme.{0}} (f : X ⟶ Y)
    (M : X.Modules) (L : Y.Modules) (U : Y.Opens)
    (m : M.val.obj (op (f ⁻¹ᵁ U))) (s : L.val.obj (op U)) :
    (ProjectionFormula.hom f M L).val.app (op U)
      (pure ((Scheme.Modules.pushforward f).obj M) L U m s) =
      pure M ((Scheme.Modules.pullback f).obj L) (f ⁻¹ᵁ U) m
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).val.app (op U) s) :=
  ProjectionFormula.hom_pure f M L U m s

lemma pushforward_hom_pure_val {X Y : Scheme.{0}} (f : X ⟶ Y)
    (M N : X.Modules) (U : Y.Opens)
    (m : M.val.obj (op (f ⁻¹ᵁ U))) (n : N.val.obj (op (f ⁻¹ᵁ U))) :
    (PiExponentSeshadri.PushforwardTensor.hom f M N).val.app (op U)
      (pure ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N) U m n) =
      pure M N (f ⁻¹ᵁ U) m n :=
  PiExponentSeshadri.PushforwardTensor.hom_pure f M N U m n

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LineBundle Y)

def powerProjectionIso (n : ℕ) :
    (moduleTwistFunctor L n).obj ((Scheme.Modules.pushforward f).obj (O X)) ≅
      (Scheme.Modules.pushforward f).obj ((L.pullback f).pow n).sheaf :=
  (ProjectionFormula.twistIso f (O X) L n).symm ≪≫
    (Scheme.Modules.pushforward f).mapIso (moduleTwistUnitIso (L.pullback f) n)

def powerUnit (n : ℕ) : (L.pow n).sheaf ⟶
    (Scheme.Modules.pushforward f).obj ((L.pullback f).pow n).sheaf :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (L.pow n).sheaf ≫
    (Scheme.Modules.pushforward f).map (PiExponentSeshadri.PullbackTensor.powIso f L n).hom

lemma powerProjectionIso_succ_pure (n : ℕ) (U : Y.Opens)
    (m : ((moduleTwistFunctor L n).obj ((Scheme.Modules.pushforward f).obj (O X))).val.obj (op U))
    (s : L.sheaf.val.obj (op U)) :
    (powerProjectionIso f L (n+1)).hom.val.app (op U)
      (pure _ L.sheaf U m s) =
      pure (L.pullback f).sheaf ((L.pullback f).pow n).sheaf (f ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf).val.app (op U) s)
        ((powerProjectionIso f L n).hom.val.app (op U) m) := by
  change (moduleTwistUnitIso (L.pullback f) (n+1)).hom.val.app (op (f ⁻¹ᵁ U))
    ((ProjectionFormula.hom f ((moduleTwistFunctor (L.pullback f) n).obj (O X)) L.sheaf).val.app (op U)
      ((moduleTensorMap (ProjectionFormula.twistIso f (O X) L n).inv (𝟙 L.sheaf)).val.app (op U)
        (pure _ L.sheaf U m s))) = _
  rw [tensor_map_pure_val]
  change (moduleTensorComm ((L.pullback f).pow n).sheaf (L.pullback f).sheaf).hom.val.app (op (f ⁻¹ᵁ U))
    ((moduleTensorMap (moduleTwistUnitIso (L.pullback f) n).hom (𝟙 (L.pullback f).sheaf)).val.app (op (f ⁻¹ᵁ U))
      ((ProjectionFormula.hom f ((moduleTwistFunctor (L.pullback f) n).obj (O X)) L.sheaf).val.app (op U)
        (pure _ L.sheaf U ((ProjectionFormula.twistIso f (O X) L n).inv.val.app (op U) m) s))) = _
  erw [projection_hom_pure_val f ((moduleTwistFunctor (L.pullback f) n).obj (O X))
    L.sheaf U ((ProjectionFormula.twistIso f (O X) L n).inv.val.app (op U) m) s]
  have ht := tensor_map_pure_val (Z := X) (moduleTwistUnitIso (L.pullback f) n).hom
    (𝟙 (L.pullback f).sheaf) (f ⁻¹ᵁ U)
    ((ProjectionFormula.twistIso f (O X) L n).inv.val.app (op U) m)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf).val.app (op U) s)
  exact (congrArg (fun r => (moduleTensorComm ((L.pullback f).pow n).sheaf
    (L.pullback f).sheaf).hom.val.app (op (f ⁻¹ᵁ U)) r) ht).trans
      (tensor_comm_pure_val _ _ _ _ _)

lemma powerUnit_succ_pure (n : ℕ) (U : Y.Opens)
    (s : L.sheaf.val.obj (op U)) (m : (L.pow n).sheaf.val.obj (op U)) :
    (powerUnit f L (n+1)).val.app (op U) (pure L.sheaf (L.pow n).sheaf U s m) =
      pure (L.pullback f).sheaf ((L.pullback f).pow n).sheaf (f ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf).val.app (op U) s)
        ((powerUnit f L n).val.app (op U) m) := by
  have h := PiExponentSeshadri.PullbackTensor.unit_hom f L.sheaf (L.pow n).sheaf
  have hp := congrArg (fun q => q.val.app (op U) (pure L.sheaf (L.pow n).sheaf U s m)) h
  change (PiExponentSeshadri.PullbackTensor.hom f L.sheaf (L.pow n).sheaf).val.app (op (f ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (moduleTensor Y L.sheaf (L.pow n).sheaf)).val.app (op U) (pure L.sheaf (L.pow n).sheaf U s m)) =
    (PiExponentSeshadri.PushforwardTensor.hom f _ _).val.app (op U)
      ((moduleTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf)
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (L.pow n).sheaf)).val.app (op U)
        (pure L.sheaf (L.pow n).sheaf U s m)) at hp
  have hm := tensor_map_pure_val (Z := Y)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (L.pow n).sheaf) U s m
  have hv := pushforward_hom_pure_val f ((Scheme.Modules.pullback f).obj L.sheaf)
    ((Scheme.Modules.pullback f).obj (L.pow n).sheaf) U
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf).val.app (op U) s)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (L.pow n).sheaf).val.app (op U) m)
  have hp' := hp.trans ((congrArg (fun r => (PiExponentSeshadri.PushforwardTensor.hom f
    ((Scheme.Modules.pullback f).obj L.sheaf) ((Scheme.Modules.pullback f).obj (L.pow n).sheaf)).val.app
      (op U) r) hm).trans hv)
  change (moduleTensorMap (𝟙 (L.pullback f).sheaf) (PiExponentSeshadri.PullbackTensor.powIso f L n).hom).app
    (f ⁻¹ᵁ U)
    ((PiExponentSeshadri.PullbackTensor.hom f L.sheaf (L.pow n).sheaf).val.app (op (f ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (moduleTensor Y L.sheaf (L.pow n).sheaf)).val.app (op U) (pure L.sheaf (L.pow n).sheaf U s m))) = _
  exact (congrArg (fun r => (moduleTensorMap (𝟙 (L.pullback f).sheaf)
    (PiExponentSeshadri.PullbackTensor.powIso f L n).hom).val.app (op (f ⁻¹ᵁ U)) r) hp').trans
      (tensor_map_pure_val (Z := X) (𝟙 (L.pullback f).sheaf)
        (PiExponentSeshadri.PullbackTensor.powIso f L n).hom _ _ _)

theorem twist_structureMap_power (n : ℕ) :
    (moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f) ≫
        (powerProjectionIso f L n).hom =
      (moduleTwistUnitIso L n).hom ≫ powerUnit f L n := by
  induction n with
  | zero =>
    change PiExponentSeshadri.IdealModule.structureMap f =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y) ≫
        (Scheme.Modules.pushforward f).map (pullbackUnitIso f).hom
    exact (pullbackUnit_adjunction f).symm
  | succ n ih =>
    apply PiExponentSeshadri.TensorPure.hom_ext
    intro U m s
    change (powerProjectionIso f L (n+1)).hom.val.app (op U)
      ((moduleTensorMap ((moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f))
        (𝟙 L.sheaf)).val.app (op U) (pure _ L.sheaf U m s)) =
      (powerUnit f L (n+1)).val.app (op U)
        ((moduleTensorComm (L.pow n).sheaf L.sheaf).hom.val.app (op U)
          ((moduleTensorMap (moduleTwistUnitIso L n).hom (𝟙 L.sheaf)).val.app (op U)
            (pure _ L.sheaf U m s)))
    have h1 := tensor_map_pure_val (Z := Y)
      ((moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f)) (𝟙 L.sheaf) U m s
    have h2 := powerProjectionIso_succ_pure f L n U
      (((moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f)).val.app (op U) m) s
    have h3 := tensor_map_pure_val (Z := Y) (moduleTwistUnitIso L n).hom (𝟙 L.sheaf) U m s
    have h4 := tensor_comm_pure_val (L.pow n).sheaf L.sheaf U
      ((moduleTwistUnitIso L n).hom.val.app (op U) m) s
    have h5 := powerUnit_succ_pure f L n U s ((moduleTwistUnitIso L n).hom.val.app (op U) m)
    have hleft := (congrArg (fun r => (powerProjectionIso f L (n+1)).hom.val.app (op U) r) h1).trans h2
    have hright := (congrArg (fun r => (powerUnit f L (n+1)).val.app (op U) r)
      ((congrArg (fun r => (moduleTensorComm (L.pow n).sheaf L.sheaf).hom.val.app (op U) r) h3).trans h4)).trans h5
    exact hleft.trans ((congrArg (fun r => pure (L.pullback f).sheaf ((L.pullback f).pow n).sheaf
      (f ⁻¹ᵁ U) (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf).val.app (op U) s) r)
      (congrArg (fun q => q.val.app (op U) m) ih)).trans hright.symm)

theorem power_restriction_eq (n : ℕ) :
    (moduleTwistUnitIso L n).inv ≫
      (moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f) ≫
      (ProjectionFormula.twistIso f (O X) L n).inv ≫
      (Scheme.Modules.pushforward f).map (moduleTwistUnitIso (L.pullback f) n).hom =
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (L.pow n).sheaf ≫
      (Scheme.Modules.pushforward f).map (PiExponentSeshadri.PullbackTensor.powIso f L n).hom := by
  change (moduleTwistUnitIso L n).inv ≫
    ((moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f) ≫
      (powerProjectionIso f L n).hom) = powerUnit f L n
  erw [twist_structureMap_power, Iso.inv_hom_id_assoc]

theorem push_pullbackSection {M : Y.Modules} (s : O Y ⟶ M) :
    PiExponentSeshadri.IdealModule.structureMap f ≫
      (Scheme.Modules.pushforward f).map (pullbackSection f s) =
      s ≫ (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M := by
  have hu : PiExponentSeshadri.IdealModule.structureMap f =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y) ≫
        (Scheme.Modules.pushforward f).map (pullbackUnitIso f).hom :=
    (pullbackUnit_adjunction f).symm
  let F := Scheme.Modules.pushforward f
  let P := Scheme.Modules.pullback f
  let e := pullbackUnitIso f
  have h := (F.map_comp e.hom (e.inv ≫ P.map s)).symm.trans
    (congrArg F.map (e.hom_inv_id_assoc (P.map s)))
  calc
    _ = ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y) ≫
        F.map e.hom) ≫ F.map (e.inv ≫ P.map s) :=
      congrArg (fun q : O Y ⟶ F.obj (O X) => q ≫ F.map (pullbackSection f s)) hu
    _ = (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y) ≫ F.map (P.map s) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun q => (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y) ≫ q) h)
    _ = _ := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality s).symm

theorem section_restriction_eq (n : ℕ) (s : O Y ⟶ (L.pow n).sheaf) :
    s ≫ (moduleTwistUnitIso L n).inv ≫
      (moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f) ≫
      (ProjectionFormula.twistIso f (O X) L n).inv ≫
      (Scheme.Modules.pushforward f).map (moduleTwistUnitIso (L.pullback f) n).hom =
    PiExponentSeshadri.IdealModule.structureMap f ≫
      (Scheme.Modules.pushforward f).map (pullbackPowerSection L f n s) := by
  erw [power_restriction_eq]
  symm
  simp only [pullbackPowerSection]
  erw [(Scheme.Modules.pushforward f).map_comp (pullbackSection f s)
    (PiExponentSeshadri.PullbackTensor.powIso f L n).hom, ← Category.assoc,
    push_pullbackSection f s, Category.assoc]

end
end PiExponent.ClosedRestrictionTensor

end OAI
