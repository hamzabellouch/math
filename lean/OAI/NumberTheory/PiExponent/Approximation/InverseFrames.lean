import OAI.NumberTheory.PiExponent.Approximation.FrameSubopens
import OAI.NumberTheory.PiExponent.Approximation.TensorPure

namespace OAI

namespace PiExponent.InverseFrames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure
variable {X : Scheme.{0}} {M N : X.Modules}

def regularValue {P : X.Modules} (f : P ⟶ O X) (U : X.Opens)
    (x : P.val.obj (op U)) : Γ(X,U) := f.app U x

def pairingFrame (E : moduleTensor X M N ≅ O X) (e : M ≅ O X) : N ≅ O X :=
  (moduleTensorUnit N).symm ≪≫ moduleTensorIso e.symm (Iso.refl N) ≪≫ E

lemma unit_inv_pure (N : X.Modules) (U : X.Opens) (x : N.val.obj (op U)) :
    (moduleTensorUnit N).inv.app U x = PiExponentSeshadri.TensorPure.pure (O X) N U (1 : Γ(X,U)) x := by
  have h : (moduleTensorUnit N).hom.app U (PiExponentSeshadri.TensorPure.pure (O X) N U (1 : Γ(X,U)) x) = x := by
    change (moduleTensorUnit N).hom.app U
      (PiExponentSeshadri.TensorPure.pure (structureSheaf X) N U (1 : Γ(X,U)) x) = x
    exact (unit_pure N U (1 : Γ(X,U)) x).trans (one_smul Γ(X,U) (show Γ(N,U) from x))
  calc
    (moduleTensorUnit N).inv.app U x =
        (moduleTensorUnit N).inv.app U
          ((moduleTensorUnit N).hom.app U (PiExponentSeshadri.TensorPure.pure (O X) N U (1 : Γ(X,U)) x)) :=
      congrArg (fun z => (moduleTensorUnit N).inv.app U z) h.symm
    _ = _ := congrArg (fun f => f.app U (PiExponentSeshadri.TensorPure.pure (O X) N U (1 : Γ(X,U)) x))
      (moduleTensorUnit N).hom_inv_id

lemma pairingFrame_apply (E : moduleTensor X M N ≅ O X) (e : M ≅ O X)
    (U : X.Opens) (x : N.val.obj (op U)) :
    (pairingFrame E e).hom.app U x =
      E.hom.app U (PiExponentSeshadri.TensorPure.pure M N U (e.inv.app U (1 : Γ(X,U))) x) := by
  change E.hom.app U ((moduleTensorMap e.inv (𝟙 N)).app U
    ((moduleTensorUnit N).inv.app U x)) = _
  rw [unit_inv_pure]
  exact congrArg (fun z => E.hom.app U z)
    (PiExponentSeshadri.TensorPure.map_pure e.inv (𝟙 N) U (1 : Γ(X,U)) x)

lemma frame_generator_change (e f : M ≅ O X) :
    f.inv.app ⊤ (1 : Γ(X,⊤)) = (frameChange f e : Γ(X,⊤)) • e.inv.app ⊤ (1 : Γ(X,⊤)) := by
  have h := e.inv.app_smul (r := (frameChange f e : Γ(X,⊤)))
    (x := (1 : Γ(X,⊤)))
  change e.inv.app ⊤ ((frameChange f e : Γ(X,⊤)) * (1 : Γ(X,⊤)) : Γ(X,⊤)) = _ at h
  rw [mul_one] at h
  rw [← h]
  change f.inv.app ⊤ (1 : Γ(X,⊤)) = e.inv.app ⊤ (e.hom.app ⊤ (f.inv.app ⊤ (1 : Γ(X,⊤))))
  exact (congrArg (fun t => t.app ⊤ (f.inv.app ⊤ (1 : Γ(X,⊤)))) e.hom_inv_id).symm

lemma pairingFrame_change_apply (E : moduleTensor X M N ≅ O X)
    (e f : M ≅ O X) (x : N.val.obj (op (⊤ : X.Opens))) :
    regularValue (pairingFrame E f).hom ⊤ x =
      (frameChange f e : Γ(X,⊤)) * regularValue (pairingFrame E e).hom ⊤ x := by
  dsimp only [regularValue]
  have hf := pairingFrame_apply E f ⊤ x
  have he := pairingFrame_apply E e ⊤ x
  have hg := congrArg (fun m => E.hom.app ⊤ (PiExponentSeshadri.TensorPure.pure M N ⊤ m x))
    (frame_generator_change e f)
  have hs := congrArg (fun z => E.hom.app ⊤ z)
    (pure_smul_left M N ⊤ (frameChange f e : Γ(X,⊤)) (e.inv.app ⊤ (1 : Γ(X,⊤))) x)
  have hm := E.hom.app_smul (r := (frameChange f e : Γ(X,⊤)))
    (x := PiExponentSeshadri.TensorPure.pure M N ⊤ (e.inv.app ⊤ (1 : Γ(X,⊤))) x)
  exact hf.trans (hg.trans (hs.trans (hm.trans
    (congrArg (fun a : Γ(X,⊤) => (frameChange f e : Γ(X,⊤)) * a) he.symm))))

lemma pairingFrame_frameChange (E : moduleTensor X M N ≅ O X)
    (e f : M ≅ O X) :
    frameChange (pairingFrame E e) (pairingFrame E f) = frameChange f e := by
  apply Units.ext
  change (pairingFrame E f).hom.app ⊤ ((pairingFrame E e).inv.app ⊤ (1 : Γ(X,⊤))) = _
  change regularValue (pairingFrame E f).hom ⊤ ((pairingFrame E e).inv.app ⊤ (1 : Γ(X,⊤))) = _
  erw [pairingFrame_change_apply]
  have h := congrArg (fun t => t.app ⊤ (1 : Γ(X,⊤))) (pairingFrame E e).inv_hom_id
  change (pairingFrame E e).hom.app ⊤ ((pairingFrame E e).inv.app ⊤ (1 : Γ(X,⊤))) = (1 : Γ(X,⊤)) at h
  have hv : regularValue (pairingFrame E e).hom ⊤
      ((pairingFrame E e).inv.app ⊤ (1 : Γ(X,⊤))) = 1 := h
  rw [hv, mul_one]

lemma pairing_apply (E : moduleTensor X M N ≅ O X) (e : M ≅ O X)
    (U : X.Opens) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    regularValue E.hom U (PiExponentSeshadri.TensorPure.pure M N U m n) =
      regularValue e.hom U m * regularValue (pairingFrame E e).hom U n := by
  have hm : m = (regularValue e.hom U m) • e.inv.app U (1 : Γ(X,U)) := by
    have h := e.inv.app_smul (r := (regularValue e.hom U m))
      (x := (1 : Γ(X,U)))
    change e.inv.app U (regularValue e.hom U m * (1 : Γ(X,U)) : Γ(X,U)) = _ at h
    rw [mul_one] at h
    rw [← h]
    exact (congrArg (fun t => t.app U m) e.hom_inv_id).symm
  calc
    regularValue E.hom U (PiExponentSeshadri.TensorPure.pure M N U m n) =
        regularValue E.hom U (PiExponentSeshadri.TensorPure.pure M N U ((regularValue e.hom U m) • e.inv.app U (1 : Γ(X,U))) n) :=
      congrArg (fun z => regularValue E.hom U (PiExponentSeshadri.TensorPure.pure M N U z n)) hm
    _ = (regularValue e.hom U m) * regularValue E.hom U (PiExponentSeshadri.TensorPure.pure M N U (e.inv.app U (1 : Γ(X,U))) n) := by
      erw [pure_smul_left]
      exact E.hom.app_smul _ _
    _ = _ := by
      dsimp only [regularValue]
      rw [pairingFrame_apply]

lemma pairing_inverse_generator (E : moduleTensor X M N ≅ O X) (e : M ≅ O X)
    (U : X.Opens) (m : M.val.obj (op U)) :
    E.hom.app U (PiExponentSeshadri.TensorPure.pure M N U m ((pairingFrame E e).inv.app U (1 : Γ(X,U)))) = e.hom.app U m := by
  change regularValue E.hom U _ = regularValue e.hom U m
  erw [pairing_apply]
  have h := congrArg (fun t => t.app U (1 : Γ(X,U))) (pairingFrame E e).inv_hom_id
  change (pairingFrame E e).hom.app U ((pairingFrame E e).inv.app U (1 : Γ(X,U))) = (1 : Γ(X,U)) at h
  have hv : regularValue (pairingFrame E e).hom U
      ((pairingFrame E e).inv.app U (1 : Γ(X,U))) = 1 := h
  rw [hv, mul_one]

def dualMap (E : moduleTensor X M N ≅ O X) (s : O X ⟶ M) : N ⟶ O X :=
  (moduleTensorUnit N).inv ≫ moduleTensorMap s (𝟙 N) ≫ E.hom

lemma dualMap_apply (E : moduleTensor X M N ≅ O X) (s : O X ⟶ M)
    (U : X.Opens) (n : N.val.obj (op U)) :
    (dualMap E s).app U n = E.hom.app U (PiExponentSeshadri.TensorPure.pure M N U (s.app U (1 : Γ(X,U))) n) := by
  change E.hom.app U ((moduleTensorMap s (𝟙 N)).app U
    ((moduleTensorUnit N).inv.app U n)) = _
  rw [unit_inv_pure]
  exact congrArg (fun z => E.hom.app U z)
    (PiExponentSeshadri.TensorPure.map_pure s (𝟙 N) U (1 : Γ(X,U)) n)

lemma dualMap_coefficient (E : moduleTensor X M N ≅ O X) (e : M ≅ O X)
    (s : O X ⟶ M) :
    endValue ((pairingFrame E e).inv ≫ dualMap E s) = coefficient e s := by
  change (dualMap E s).app ⊤ ((pairingFrame E e).inv.app ⊤ (1 : Γ(X,⊤))) = e.hom.app ⊤ (s.app ⊤ (1 : Γ(X,⊤)))
  exact (dualMap_apply E s ⊤ ((pairingFrame E e).inv.app ⊤ (1 : Γ(X,⊤)))).trans
    (pairing_inverse_generator E e ⊤ (s.app ⊤ (1 : Γ(X,⊤))))

def restrictPairing (E : moduleTensor X M N ≅ O X) (U : X.Opens) :
    moduleTensor U.toScheme (M.restrict U.ι) (N.restrict U.ι) ≅ O U.toScheme :=
  (moduleTensorRestrict U M N).symm ≪≫
    (Scheme.Modules.restrictFunctor U.ι).mapIso E ≪≫ Scheme.Modules.restrictUnitIso U.ι

def inverseOpenFrame (E : moduleTensor X M N ≅ O X) (U : X.Opens)
    (e : M.restrict U.ι ≅ O U.toScheme) : N.restrict U.ι ≅ O U.toScheme :=
  pairingFrame (restrictPairing E U) e

lemma inverseOpenFrame_frameChange (E : moduleTensor X M N ≅ O X) (U : X.Opens)
    (e f : M.restrict U.ι ≅ O U.toScheme) :
    frameChange (inverseOpenFrame E U e) (inverseOpenFrame E U f) = frameChange f e :=
  pairingFrame_frameChange (restrictPairing E U) e f

end
end PiExponent.InverseFrames

end OAI
