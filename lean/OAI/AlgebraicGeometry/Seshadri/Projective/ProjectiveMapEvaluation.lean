import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.SectionMaps

namespace OAI

section
noncomputable section
                                                 
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal
universe u
variable {A B R σ τ : Type u} [CommRing A] [CommRing B] [CommRing R]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {ℬ : ℕ → τ} [GradedRing ℬ]

lemma evalAway_map (F : 𝒜 →+*ᵍ ℬ) (f : B →+* R) {s : A} {d : ℕ}
    (hs : s ∈ 𝒜 d) (hu : IsUnit (f (F s))) :
    (evalAway f (F s) hu).comp (Away.map F s) =
      evalAway (f.comp F.toRingHom) s hu := by
  apply RingHom.ext
  intro x
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hs x
  apply (hu.pow n).mul_right_cancel
  simp only [RingHom.comp_apply, Away.map_mk]
  rw [evalAway_mk_clear]
  exact (evalAway_mk_clear (f.comp F.toRingHom) hs hu n a ha).symm

lemma fromUnitCoordinate_comp_Proj_map (F : 𝒜 →+*ᵍ ℬ)
    (hF : ℬ₊ ≤ 𝒜₊.map F) (f : B →+* R) {s : A} {d : ℕ}
    (hd : 0 < d) (hs : s ∈ 𝒜 d) (hu : IsUnit (f (F s))) :
    fromUnitCoordinate f hd (F.map_mem hs) hu ≫ Proj.map F hF =
      fromUnitCoordinate (f.comp F.toRingHom) hd hs hu := by
  rw [fromUnitCoordinate, Category.assoc]
  erw [Proj.awayι_comp_map F hF hd s hs,
    ← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
      ((evalAway f (F s) hu).comp (Away.map F s))) ≫ _ = _
  rw [evalAway_map F f hs]
  rfl

lemma fromUnitCoordinate_comp_Proj_map_eq (F : 𝒜 →+*ᵍ ℬ)
    (hF : ℬ₊ ≤ 𝒜₊.map F) (f : B →+* R) {s : A} {d : ℕ}
    (hd : 0 < d) (hs : s ∈ 𝒜 d) (t : B) (ht : F s = t)
    (htmem : t ∈ ℬ d) (hu : IsUnit (f t)) (g : A →+* R)
    (hg : f.comp F.toRingHom = g) (hv : IsUnit (g s)) :
    fromUnitCoordinate f hd htmem hu ≫ Proj.map F hF =
      fromUnitCoordinate g hd hs hv := by
  subst t
  subst g
  exact fromUnitCoordinate_comp_Proj_map F hF f hd hs hu

end
end MaximalSeshadri.Projective

end


end
end

end OAI
