import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.SurfaceCech

namespace OAI


                                    
section

namespace MaximalSeshadri.ModuleMayerVietoris
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open ModuleFlasque
universe u
variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

lemma freeOpen_hom_ext {A B Q : Opens X} (hA : A ≤ Q) (hB : B ≤ Q) (h : A ⊔ B = Q)
    {N : SheafOfModules R} {f g : freeOpen R Q ⟶ N}
    (ha : freeOpenMap R (homOfLE hA) ≫ f = freeOpenMap R (homOfLE hA) ≫ g)
    (hb : freeOpenMap R (homOfLE hB) ≫ f = freeOpenMap R (homOfLE hB) ≫ g) : f = g := by
  subst Q
  apply CategoryTheory.IsPushout.hom_ext (freeOpen_isPushout R A B) ha hb

lemma freeOpen_glue3 {U V W : Opens X} {N : SheafOfModules R}
    (f : freeOpen R U ⟶ N) (g : freeOpen R V ⟶ N) (h : freeOpen R W ⟶ N)
    (hfg : freeOpenMap R (homOfLE (show U ⊓ V ≤ U from inf_le_left)) ≫ f =
      freeOpenMap R (homOfLE (show U ⊓ V ≤ V from inf_le_right)) ≫ g)
    (hfh : freeOpenMap R (homOfLE (show U ⊓ W ≤ U from inf_le_left)) ≫ f =
      freeOpenMap R (homOfLE (show U ⊓ W ≤ W from inf_le_right)) ≫ h)
    (hgh : freeOpenMap R (homOfLE (show V ⊓ W ≤ V from inf_le_left)) ≫ g =
      freeOpenMap R (homOfLE (show V ⊓ W ≤ W from inf_le_right)) ≫ h) :
    ∃ l : freeOpen R ((U ⊔ V) ⊔ W) ⟶ N,
      freeOpenMap R (homOfLE (le_sup_left.trans le_sup_left)) ≫ l = f ∧
      freeOpenMap R (homOfLE (le_sup_right.trans le_sup_left)) ≫ l = g ∧
      freeOpenMap R (homOfLE le_sup_right) ≫ l = h := by
  let p : freeOpen R (U ⊔ V) ⟶ N := CategoryTheory.IsPushout.desc (freeOpen_isPushout R U V) f g hfg
  have hpU : freeOpenMap R (homOfLE (show U ≤ U ⊔ V from le_sup_left)) ≫ p = f :=
    CategoryTheory.IsPushout.inl_desc (freeOpen_isPushout R U V) f g hfg
  have hpV : freeOpenMap R (homOfLE (show V ≤ U ⊔ V from le_sup_right)) ≫ p = g :=
    CategoryTheory.IsPushout.inr_desc (freeOpen_isPushout R U V) f g hfg
  have hp : freeOpenMap R (homOfLE (show (U ⊔ V) ⊓ W ≤ U ⊔ V from inf_le_left)) ≫ p =
      freeOpenMap R (homOfLE (show (U ⊔ V) ⊓ W ≤ W from inf_le_right)) ≫ h := by
    apply freeOpen_hom_ext R (A := U ⊓ W) (B := V ⊓ W)
      (inf_le_inf le_sup_left le_rfl) (inf_le_inf le_sup_right le_rfl) (inf_sup_right U V W).symm
    · simp only [← Category.assoc,freeOpenMap_comp]
      change freeOpenMap R (homOfLE (inf_le_left.trans le_sup_left)) ≫ p = freeOpenMap R (homOfLE inf_le_right) ≫ h
      rw [show freeOpenMap R (homOfLE (show U ⊓ W ≤ U ⊔ V from inf_le_left.trans le_sup_left)) =
        freeOpenMap R (homOfLE (show U ⊓ W ≤ U from inf_le_left)) ≫
          freeOpenMap R (homOfLE (show U ≤ U ⊔ V from le_sup_left)) from
        (freeOpenMap_comp R _ _).symm,Category.assoc,hpU]
      exact hfh
    · simp only [← Category.assoc,freeOpenMap_comp]
      change freeOpenMap R (homOfLE (inf_le_left.trans le_sup_right)) ≫ p = freeOpenMap R (homOfLE inf_le_right) ≫ h
      rw [show freeOpenMap R (homOfLE (show V ⊓ W ≤ U ⊔ V from inf_le_left.trans le_sup_right)) =
        freeOpenMap R (homOfLE (show V ⊓ W ≤ V from inf_le_left)) ≫
          freeOpenMap R (homOfLE (show V ≤ U ⊔ V from le_sup_right)) from
        (freeOpenMap_comp R _ _).symm,Category.assoc,hpV]
      exact hgh
  let l : freeOpen R ((U ⊔ V) ⊔ W) ⟶ N := CategoryTheory.IsPushout.desc (freeOpen_isPushout R (U ⊔ V) W) p h hp
  have hl : freeOpenMap R (homOfLE (show U ⊔ V ≤ (U ⊔ V) ⊔ W from le_sup_left)) ≫ l = p :=
    CategoryTheory.IsPushout.inl_desc (freeOpen_isPushout R (U ⊔ V) W) p h hp
  refine ⟨l,?_,?_,CategoryTheory.IsPushout.inr_desc (freeOpen_isPushout R (U ⊔ V) W) p h hp⟩
  · rw [show freeOpenMap R (homOfLE (show U ≤ (U ⊔ V) ⊔ W from le_sup_left.trans le_sup_left)) =
      freeOpenMap R (homOfLE (show U ≤ U ⊔ V from le_sup_left)) ≫
        freeOpenMap R (homOfLE (show U ⊔ V ≤ (U ⊔ V) ⊔ W from le_sup_left)) from
      (freeOpenMap_comp R _ _).symm,Category.assoc,hl,hpU]
  · rw [show freeOpenMap R (homOfLE (show V ≤ (U ⊔ V) ⊔ W from le_sup_right.trans le_sup_left)) =
      freeOpenMap R (homOfLE (show V ≤ U ⊔ V from le_sup_right)) ≫
        freeOpenMap R (homOfLE (show U ⊔ V ≤ (U ⊔ V) ⊔ W from le_sup_left)) from
      (freeOpenMap_comp R _ _).symm,Category.assoc,hl,hpV]

end
end MaximalSeshadri.ModuleMayerVietoris

end


end OAI
