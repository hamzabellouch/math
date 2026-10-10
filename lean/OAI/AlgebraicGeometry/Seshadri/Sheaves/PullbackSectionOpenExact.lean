import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.AmpleCurveDegree

namespace OAI

section
noncomputable section
                                                  
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.SectionOpens

variable {X Y : Scheme.{0}}

theorem pullback_isoOpen_eq (L : LineBundle X) (s : O X ⟶ L.sheaf) (f : Y ⟶ X) :
    isoOpen (pullbackSection f s) = f ⁻¹ᵁ isoOpen s := by
  ext y
  obtain ⟨U,hy,⟨e⟩⟩ := L.locallyRankOne (f y)
  obtain ⟨eF,he⟩ := exists_restricted_pullback_frame_all f U e
  calc
    y ∈ isoOpen (pullbackSection f s) ↔
        (⟨y,hy⟩ : (f ⁻¹ᵁ U).toScheme) ∈ (f ⁻¹ᵁ U).toScheme.basicOpen
          (coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s))) :=
      (congrArg (fun V => (⟨y,hy⟩ : (f ⁻¹ᵁ U).toScheme) ∈ V)
        (preimage_isoOpen (pullbackSection f s) (f ⁻¹ᵁ U).ι eF)).to_iff
    _ ↔ (⟨f y,hy⟩ : U.toScheme) ∈ U.toScheme.basicOpen
          (coefficient e (restrictSection U.ι s)) := by
      rw [he,← Scheme.preimage_basicOpen_top]
      change (f ∣_ U) ⟨y,hy⟩ ∈ U.toScheme.basicOpen
        (coefficient e (restrictSection U.ι s)) ↔ _
      rw [morphismRestrict_base]
      rfl
    _ ↔ f y ∈ isoOpen s :=
      (congrArg (fun V => (⟨f y,hy⟩ : U.toScheme) ∈ V)
        (preimage_isoOpen s U.ι e)).to_iff.symm

theorem IntegralCurve.exists_positive_ambient_power (S : Surface) (C : IntegralCurve S)
    (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ m : ℕ, 0 < m ∧ 0 < curveDegree S (L.pow m) C := by
  obtain ⟨U,x,hx,hU⟩ := exists_proper_nonempty_open C.dimension
  have hUC : IsOpen (U : Set C.scheme) := U.isOpen
  obtain ⟨V,hV,hVU⟩ := C.embedding.isClosedEmbedding.isInducing.isOpen_iff.mp hUC
  let W : S.scheme.Opens := ⟨V,hV⟩
  have hxW : C.embedding x ∈ W := by
    change x ∈ C.embedding ⁻¹' V
    rw [hVU]
    exact hx
  obtain ⟨m,hm,s,hxs,hsW,_⟩ := hL (C.embedding x) W hxW
  let t : O C.scheme ⟶ ((L.pow m).pullback C.embedding).sheaf :=
    pullbackSection C.embedding s
  have htopen : isoOpen t = C.embedding ⁻¹ᵁ isoOpen s :=
    pullback_isoOpen_eq (L.pow m) s C.embedding
  have hxt : x ∈ isoOpen t := by
    rw [htopen]
    exact hxs
  have ht : t ≠ 0 := section_ne_zero_of_mem_isoOpen
    ((L.pow m).pullback C.embedding) t x hxt
  have hproper : isoOpen t ≠ ⊤ := by
    intro he
    apply hU
    apply top_unique
    intro y _hy
    have hyt : y ∈ isoOpen t := by rw [he]; trivial
    rw [htopen] at hyt
    have hyW := hsW hyt
    change y ∈ (U : Set C.scheme)
    rw [← hVU]
    exact hyW
  obtain ⟨σ,hσ,B,a,ha,hc⟩ := C.exists_projective_sections S L hL
  let := hσ
  let := hc
  refine ⟨m,hm,?_⟩
  exact projective_section_positive_degree (C.embedding ≫ S.structureMap)
    C.dimension a ha ((L.pow m).pullback C.embedding) t ht hproper

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
