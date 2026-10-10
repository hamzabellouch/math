import OAI.Combinatorics.TriangleFace.Model

namespace OAI

namespace CanonicalFace198

variable {A B : Type*} [AddCommGroup A] [Module ℝ A]
  [AddCommGroup B] [Module ℝ B]

theorem self_mem (P : Set A) (x : A) : x ∈ minFace P x := by
  apply Set.mem_sInter.mpr
  intro F hF
  exact hF.2.2

theorem least {P F : Set A} {x : A} (hF : Convex ℝ F)
    (hPF : IsExtreme ℝ P F) (hxF : x ∈ F) : minFace P x ⊆ F := by
  intro y hy
  exact Set.mem_sInter.mp hy F ⟨hF, hPF, hxF⟩

theorem convex (P : Set A) (x : A) : Convex ℝ (minFace P x) := by
  exact convex_sInter (fun _ hF => hF.1)

theorem extreme {P : Set A} (hP : Convex ℝ P) {x : A} (hx : x ∈ P) :
    IsExtreme ℝ P (minFace P x) := by
  apply isExtreme_sInter
  · exact ⟨P, hP, IsExtreme.refl ℝ P, hx⟩
  · intro F hF
    exact hF.2.1

theorem subset {P : Set A} (hP : Convex ℝ P) {x : A} (hx : x ∈ P) :
    minFace P x ⊆ P := (extreme hP hx).subset

theorem extreme_affine_image (f : A →ᵃ[ℝ] B) (hf : Function.Injective f)
    {P Q : Set A} (h : IsExtreme ℝ P Q) : IsExtreme ℝ (f '' P) (f '' Q) := by
  refine ⟨Set.image_mono h.subset, ?_⟩
  rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩ _ ⟨w,hw,rfl⟩ hseg
  rw [← image_openSegment ℝ f] at hseg
  obtain ⟨w',hw',he⟩ := hseg
  have hww : w' = w := hf he
  exact ⟨u, h.left_mem_of_mem_openSegment hu hv hw (hww ▸ hw'), rfl⟩

theorem extreme_affine_preimage (f : A →ᵃ[ℝ] B) {P : Set A} {Q R : Set B}
    (hPQ : f '' P ⊆ Q) (hQR : IsExtreme ℝ Q R) :
    IsExtreme ℝ P (P ∩ f ⁻¹' R) := by
  refine ⟨Set.inter_subset_left, ?_⟩
  intro u hu v hv w hw hseg
  refine ⟨hu, hQR.left_mem_of_mem_openSegment (hPQ ⟨u,hu,rfl⟩)
    (hPQ ⟨v,hv,rfl⟩) hw.2 ?_⟩
  rw [← image_openSegment ℝ f]
  exact ⟨w,hseg,rfl⟩

theorem image_minFace (f : A →ᵃ[ℝ] B) (hf : Function.Injective f)
    {P : Set A} {K : Set B} (hP : Convex ℝ P) (hK : Convex ℝ K)
    (hface : IsExtreme ℝ K (f '' P)) {x : A} (hx : x ∈ P) :
    f '' minFace P x = minFace K (f x) := by
  have hfx : f x ∈ K := hface.subset ⟨x, hx, rfl⟩
  apply Set.Subset.antisymm
  · have hpreConvex : Convex ℝ (P ∩ f ⁻¹' minFace K (f x)) :=
      hP.inter ((convex K (f x)).affine_preimage f)
    have hpreExtreme := extreme_affine_preimage f hface.subset (extreme hK hfx)
    have hleast := least hpreConvex hpreExtreme ⟨hx, self_mem K (f x)⟩
    rintro _ ⟨y, hy, rfl⟩
    exact (hleast hy).2
  · apply least ((convex P x).affine_image f)
    · exact hface.trans (extreme_affine_image f hf (extreme hP hx))
    · exact ⟨x, self_mem P x, rfl⟩

end CanonicalFace198

end OAI
