import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.LaurentSupport
import OAI.AlgebraicGeometry.Seshadri.Cohomology.CechPresentation

namespace OAI


                                          
section

namespace MaximalSeshadri.PlaneCech
noncomputable section
open LaurentPlane
variable {K M P : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup P] [Module K P]

lemma cycleMap_fullBoundaries_le
    (f : P →ₗ[K] M) (A B C : Submodule K P) (D E F : Submodule K M)
    (hA : ∀ x ∈ A, f x ∈ D) (hB : ∀ x ∈ B, f x ∈ E)
    (hC : ∀ x ∈ C, f x ∈ F) (Q : Submodule K (cycles D E F))
    (hAB : ∀ x : ↥(A ⊓ B), edgeAB D E F ⟨f x,⟨hA _ x.2.1,hB _ x.2.2⟩⟩ ∈ Q)
    (hAC : ∀ x : ↥(A ⊓ C), edgeAC D E F ⟨f x,⟨hA _ x.2.1,hC _ x.2.2⟩⟩ ∈ Q)
    (hBC : ∀ x : ↥(B ⊓ C), edgeBC D E F ⟨f x,⟨hB _ x.2.1,hC _ x.2.2⟩⟩ ∈ Q) :
    (fullBoundaries A B C).map (cycleMap f A B C D E F hA hB hC) ≤ Q := by
  rw [fullBoundaries,Submodule.map_sup,Submodule.map_sup]
  apply sup_le
  · apply sup_le
    · rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
      convert hAB x using 1
      ext <;> simp [cycleMap,edgeAB]
    · rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
      convert hAC x using 1
      ext <;> simp [cycleMap,edgeAC]
  · rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
    convert hBC x using 1
    ext <;> simp [cycleMap,edgeBC]

theorem finite_H1_of_free_presentation {ι : Type*} [Fintype ι]
    [Module (LaurentPlane.Ring K) M] [IsScalarTower K (LaurentPlane.Ring K) M]
    (f : (ι → LaurentPlane.Ring K) →ₗ[LaurentPlane.Ring K] M) (d : ℤ)
    (D E F : Submodule K M)
    (hA : ∀ x ∈ freeA ι, f x ∈ D) (hB : ∀ x ∈ freeB ι, f x ∈ E)
    (hC : ∀ x ∈ freeC ι d, f x ∈ F)
    (surA : ∀ x ∈ D, ∃ y ∈ freeA ι, f y = x)
    (surB : ∀ x ∈ E, ∃ y ∈ freeB ι, f y = x)
    (surC : ∀ x ∈ F, ∃ y ∈ freeC ι d, f y = x)
    (Q : Submodule K (cycles D E F))
    (hQ : (fullBoundaries (freeA ι) (freeB ι) (freeC ι d)).map
      (cycleMap (f.restrictScalars K) (freeA ι) (freeB ι) (freeC ι d) D E F hA hB hC) ≤ Q) :
    Module.Finite K ((cycles D E F) ⧸ Q) := by
  let sA : freeA (K := K) ι →ₗ[K] D :=
    ((f.restrictScalars K).domRestrict (freeA ι)).codRestrict D (fun x => hA x x.2)
  let sB : freeB (K := K) ι →ₗ[K] E :=
    ((f.restrictScalars K).domRestrict (freeB ι)).codRestrict E (fun x => hB x x.2)
  let sC : freeC (K := K) ι d →ₗ[K] F :=
    ((f.restrictScalars K).domRestrict (freeC ι d)).codRestrict F (fun x => hC x x.2)
  apply finite_H1_of_presentation (f.restrictScalars K) (freeA ι) (freeB ι) (freeC ι d)
    D E F hA hB hC sA sB sC (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) _ _ _ Q hQ
    (free_H1_zero ι d)
  · exact submodule_top_finite (LinearMap.ker f) d
  · rintro ⟨x,hx⟩
    obtain ⟨y,hy,he⟩ := surA x hx
    exact ⟨⟨y,hy⟩,Subtype.ext he⟩
  · rintro ⟨x,hx⟩
    obtain ⟨y,hy,he⟩ := surB x hx
    exact ⟨⟨y,hy⟩,Subtype.ext he⟩
  · rintro ⟨x,hx⟩
    obtain ⟨y,hy,he⟩ := surC x hx
    exact ⟨⟨y,hy⟩,Subtype.ext he⟩

end
end MaximalSeshadri.PlaneCech

end

end OAI
