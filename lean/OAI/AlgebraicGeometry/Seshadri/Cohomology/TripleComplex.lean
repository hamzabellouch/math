import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.TripleFree

namespace OAI


                                       
section

namespace MaximalSeshadri.ModuleMayerVietoris
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open ModuleFlasque
universe u
variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

abbrev tripleVertices (U V W : Opens X) := freeOpen R U ⊞ (freeOpen R V ⊞ freeOpen R W)
abbrev triplePairs (U V W : Opens X) := freeOpen R (U ⊓ V) ⊞ (freeOpen R (U ⊓ W) ⊞ freeOpen R (V ⊓ W))
def tripleD (U V W : Opens X) : triplePairs R U V W ⟶ tripleVertices R U V W :=
  biprod.desc
    (freeOpenMap R (homOfLE inf_le_left) ≫ biprod.inl -
      freeOpenMap R (homOfLE inf_le_right) ≫ biprod.inl ≫ biprod.inr)
    (biprod.desc
      (-freeOpenMap R (homOfLE inf_le_left) ≫ biprod.inl +
        freeOpenMap R (homOfLE inf_le_right) ≫ biprod.inr ≫ biprod.inr)
      (freeOpenMap R (homOfLE inf_le_left) ≫ biprod.inl ≫ biprod.inr -
        freeOpenMap R (homOfLE inf_le_right) ≫ biprod.inr ≫ biprod.inr))
def tripleG (U V W : Opens X) : tripleVertices R U V W ⟶ freeOpen R ((U ⊔ V) ⊔ W) :=
  biprod.desc (freeOpenMap R (homOfLE (le_sup_left.trans le_sup_left)))
    (biprod.desc (freeOpenMap R (homOfLE (le_sup_right.trans le_sup_left)))
      (freeOpenMap R (homOfLE le_sup_right)))

lemma tripleDG (U V W : Opens X) : tripleD R U V W ≫ tripleG R U V W = 0 := by
  apply biprod.hom_ext'
  · simp [tripleD,tripleG,Preadditive.sub_comp,Category.assoc,freeOpenMap_comp]
  · apply biprod.hom_ext' <;>
      simp [tripleD,tripleG,Preadditive.sub_comp,Preadditive.add_comp,Preadditive.neg_comp,
        Category.assoc,freeOpenMap_comp]

instance tripleG_epi (U V W : Opens X) : Epi (tripleG R U V W) := by
  constructor
  intro N f g h
  apply freeOpen_hom_ext R (A := U ⊔ V) (B := W) le_sup_left le_sup_right rfl
  · apply freeOpen_hom_ext R (A := U) (B := V) le_sup_left le_sup_right rfl
    · have hh := congrArg (fun z => biprod.inl ≫ z) h
      simp only [← Category.assoc,freeOpenMap_comp]
      simpa [tripleG,Category.assoc] using hh
    · have hh := congrArg (fun z => biprod.inl ≫ biprod.inr ≫ z) h
      simp only [← Category.assoc,freeOpenMap_comp]
      simpa [tripleG,Category.assoc] using hh
  · have hh := congrArg (fun z => biprod.inr ≫ biprod.inr ≫ z) h
    simpa [tripleG,Category.assoc] using hh

def tripleG_isCokernel (U V W : Opens X) :
    IsColimit (CokernelCofork.ofπ (tripleG R U V W) (tripleDG R U V W)) := by
  apply CokernelCofork.IsColimit.ofπ'
  intro N k hk
  have hab := congrArg (fun z => biprod.inl ≫ z) hk
  have hac := congrArg (fun z => biprod.inl ≫ biprod.inr ≫ z) hk
  have hbc := congrArg (fun z => biprod.inr ≫ biprod.inr ≫ z) hk
  simp only [tripleD,Category.assoc,biprod.inl_desc_assoc,biprod.inr_desc_assoc,
    Preadditive.sub_comp,Preadditive.add_comp,Preadditive.neg_comp,Limits.comp_zero] at hab hac hbc
  apply Classical.indefiniteDescription
  obtain ⟨l,hl0,hl1,hl2⟩ := freeOpen_glue3 R (biprod.inl ≫ k)
    (biprod.inl ≫ biprod.inr ≫ k) (biprod.inr ≫ biprod.inr ≫ k)
    (sub_eq_zero.mp hab) (by simpa only [Preadditive.neg_comp,neg_add_eq_sub] using (sub_eq_zero.mp (by simpa only [Preadditive.neg_comp,neg_add_eq_sub] using hac)).symm)
    (sub_eq_zero.mp hbc)
  refine ⟨l,?_⟩
  apply biprod.hom_ext'
  · simpa [tripleG,Category.assoc] using hl0
  · apply biprod.hom_ext'
    · simpa [tripleG,Category.assoc] using hl1
    · simpa [tripleG,Category.assoc] using hl2

abbrev tripleRelations (U V W : Opens X) := kernel (tripleG R U V W)
def tripleToRelations (U V W : Opens X) : triplePairs R U V W ⟶ tripleRelations R U V W :=
  kernel.lift (tripleG R U V W) (tripleD R U V W) (tripleDG R U V W)
instance tripleToRelations_epi (U V W : Opens X) : Epi (tripleToRelations R U V W) := by
  let S := ShortComplex.mk (tripleD R U V W) (tripleG R U V W) (tripleDG R U V W)
  exact S.exact_iff_epi_kernel_lift.mp (S.exact_of_g_is_cokernel (tripleG_isCokernel R U V W))

lemma tripleToRelations_cycle {U V W T : Opens X} (hU : T ≤ U) (hV : T ≤ V) (hW : T ≤ W) :
    freeOpenMap R (homOfLE (le_inf hU hV)) ≫ biprod.inl ≫ tripleToRelations R U V W +
    freeOpenMap R (homOfLE (le_inf hU hW)) ≫ biprod.inl ≫ biprod.inr ≫ tripleToRelations R U V W +
    freeOpenMap R (homOfLE (le_inf hV hW)) ≫ biprod.inr ≫ biprod.inr ≫ tripleToRelations R U V W = 0 := by
  apply (cancel_mono (kernel.ι (tripleG R U V W))).mp
  simp only [Preadditive.add_comp,Category.assoc,tripleToRelations,kernel.lift_ι,Limits.zero_comp]
  apply biprod.hom_ext
  · simp [tripleD,Category.assoc,Preadditive.comp_sub,Preadditive.comp_add,
      Preadditive.comp_neg,freeOpenMap_comp]
  · apply biprod.hom_ext <;> simp [tripleD,Category.assoc,Preadditive.comp_sub,
      Preadditive.comp_add,Preadditive.comp_neg,freeOpenMap_comp]

abbrev tripleKernelComplex (U V W : Opens X) :=
  ShortComplex.mk (kernel.ι (tripleG R U V W)) (tripleG R U V W) (kernel.condition _)
lemma tripleKernelComplex_shortExact (U V W : Opens X) :
    (tripleKernelComplex R U V W).ShortExact := by
  exact ⟨(tripleKernelComplex R U V W).exact_of_f_is_kernel (kernelIsKernel _)⟩

end
end MaximalSeshadri.ModuleMayerVietoris

end


end OAI
