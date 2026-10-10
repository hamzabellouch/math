import OAI.NumberTheory.PiExponent.Approximation.FrameSubopensCoherence
import OAI.NumberTheory.PiExponent.Approximation.InverseFrames

namespace OAI

namespace PiExponent.InverseFrames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure
variable {X : Scheme.{0}} {M N : X.Modules}

lemma restrictPairing_pure (E : moduleTensor X M N ≅ O X) (U : X.Opens)
    (A : U.toScheme.Opens) (m : Γ(M.restrict U.ι,A)) (n : Γ(N.restrict U.ι,A)) :
    (restrictPairing E U).hom.app A (PiExponentSeshadri.TensorPure.pure (M.restrict U.ι) (N.restrict U.ι) A m n) =
      E.hom.app (U.ι ''ᵁ A) (PiExponentSeshadri.TensorPure.pure M N (U.ι ''ᵁ A) m n) := by
  change (Scheme.Modules.restrictUnitIso U.ι).hom.app A
    (((Scheme.Modules.restrictFunctor U.ι).map E.hom).app A
      ((moduleTensorRestrict U M N).inv.app A
        (PiExponentSeshadri.TensorPure.pure (M.restrict U.ι) (N.restrict U.ι) A m n))) = _
  refine (congrArg (fun z => (Scheme.Modules.restrictUnitIso U.ι).hom.app A
    (((Scheme.Modules.restrictFunctor U.ι).map E.hom).app A z))
    (restrict_pure_inv U M N A m n)).trans ?_
  change (U.ι.appIso A).hom (E.hom.app (U.ι ''ᵁ A) (PiExponentSeshadri.TensorPure.pure M N (U.ι ''ᵁ A) m n)) = _
  rw [Scheme.Opens.ι_appIso]
  rfl

lemma inverseOpenFrame_pairing (E : moduleTensor X M N ≅ O X) (U : X.Opens)
    (e : M.restrict U.ι ≅ O U.toScheme)
    (A : U.toScheme.Opens) (m : Γ(M.restrict U.ι,A)) (n : Γ(N.restrict U.ι,A)) :
    E.hom.app (U.ι ''ᵁ A) (PiExponentSeshadri.TensorPure.pure M N (U.ι ''ᵁ A) m n) =
      regularValue e.hom A m * regularValue (inverseOpenFrame E U e).hom A n := by
  rw [← restrictPairing_pure]
  exact pairing_apply (restrictPairing E U) e A m n

lemma pairing_restrict (E : moduleTensor X M N ≅ O X) {U V : X.Opens}
    (h : V ≤ U) (m : Γ(M,U)) (n : Γ(N,U)) :
    X.presheaf.map (homOfLE h).op (E.hom.app U (PiExponentSeshadri.TensorPure.pure M N U m n)) =
      E.hom.app V (PiExponentSeshadri.TensorPure.pure M N V (M.presheaf.map (homOfLE h).op m)
        (N.presheaf.map (homOfLE h).op n)) := by
  have hn := CategoryTheory.congr_fun (E.hom.mapPresheaf.naturality (homOfLE h).op)
    (PiExponentSeshadri.TensorPure.pure M N U m n)
  change E.hom.app V ((moduleTensor X M N).presheaf.map (homOfLE h).op
    (PiExponentSeshadri.TensorPure.pure M N U m n)) =
    X.presheaf.map (homOfLE h).op (E.hom.app U (PiExponentSeshadri.TensorPure.pure M N U m n)) at hn
  exact hn.symm.trans (congrArg (fun z => E.hom.app V z)
    (pure_restrict M N (homOfLE h) m n))

private lemma restrictionMap_cycle {C : Type*} [Category C]
    (F : X.Opensᵒᵖ ⥤ C) {U V : X.Opens} (h : V ≤ U) (k : U ≤ V) :
    F.map (homOfLE h).op ≫ F.map (homOfLE k).op = 𝟙 (F.obj (op U)) := by
  rw [← Functor.map_comp]
  rw [show (homOfLE h).op ≫ (homOfLE k).op = 𝟙 (op U) from Subsingleton.elim _ _]
  exact F.map_id _

lemma inverseOpenFrame_restrict_pairing (E : moduleTensor X M N ≅ O X)
    {U V : X.Opens} (h : V ≤ U) (e : M.restrict U.ι ≅ O U.toScheme)
    (A : V.toScheme.Opens) (m : Γ(M.restrict V.ι,A)) (n : Γ(N.restrict V.ι,A)) :
    E.hom.app (V.ι ''ᵁ A) (PiExponentSeshadri.TensorPure.pure M N (V.ι ''ᵁ A) m n) =
      regularValue (restrictOpenFrame h e).hom A m *
        regularValue (restrictOpenFrame h (inverseOpenFrame E U e)).hom A n := by
  let B := X.homOfLE h ''ᵁ A
  have h₁ : V.ι ''ᵁ A ≤ U.ι ''ᵁ B := by simp [B, ← Scheme.Hom.comp_image]
  have h₂ : U.ι ''ᵁ B ≤ V.ι ''ᵁ A := by simp [B, ← Scheme.Hom.comp_image]
  let m' := M.presheaf.map (homOfLE h₂).op m
  let n' := N.presheaf.map (homOfLE h₂).op n
  have hp := inverseOpenFrame_pairing E U e B m' n'
  have hs := congrArg (fun x : Γ(U.toScheme,B) => X.presheaf.map (homOfLE h₁).op x) hp
  have hs := hs.trans ((X.presheaf.map (homOfLE h₁).op).hom.map_mul _ _)
  have hr := pairing_restrict E h₁ m' n'
  have hm : M.presheaf.map (homOfLE h₁).op m' = m := by
    change (M.presheaf.map _ ≫ M.presheaf.map _) m = m
    exact CategoryTheory.congr_fun (restrictionMap_cycle M.presheaf h₂ h₁) m
  have hn : N.presheaf.map (homOfLE h₁).op n' = n := by
    change (N.presheaf.map _ ≫ N.presheaf.map _) n = n
    exact CategoryTheory.congr_fun (restrictionMap_cycle N.presheaf h₂ h₁) n
  rw [hm, hn] at hr
  dsimp only [regularValue]
  rw [restrictOpenFrame_app, restrictOpenFrame_app]
  exact hr.symm.trans hs

lemma inverseOpenFrame_restrict (E : moduleTensor X M N ≅ O X)
    {U V : X.Opens} (h : V ≤ U) (e : M.restrict U.ι ≅ O U.toScheme) :
    restrictOpenFrame h (inverseOpenFrame E U e) =
      inverseOpenFrame E V (restrictOpenFrame h e) := by
  apply Iso.ext
  ext A n
  let eV := restrictOpenFrame h e
  have h1 := inverseOpenFrame_restrict_pairing E h e A (eV.inv.app A (1 : Γ(V.toScheme,A))) n
  have h2 := inverseOpenFrame_pairing E V eV A (eV.inv.app A (1 : Γ(V.toScheme,A))) n
  have he : regularValue eV.hom A (eV.inv.app A (1 : Γ(V.toScheme,A))) = (1 : Γ(V.toScheme,A)) :=
    congrArg (fun g => g.app A (1 : Γ(V.toScheme,A))) eV.inv_hom_id
  change _ = regularValue eV.hom A (eV.inv.app A (1 : Γ(V.toScheme,A))) * _ at h1
  rw [he, one_mul] at h1 h2
  exact h1.symm.trans h2

end
end PiExponent.InverseFrames

end OAI
