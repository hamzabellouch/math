import Mathlib

namespace OAI

section
noncomputable section
                                     
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

variable {X Y : Scheme}

lemma closedImmersion_stalk_kernel (f : Y ⟶ X) [IsClosedImmersion f]
    (U : X.affineOpens) (y : Y) (hy : f y ∈ U.1) :
    RingHom.ker (f.stalkMap y).hom =
      (f.ker.ideal U).map (X.presheaf.germ U.1 (f y) hy).hom := by
  let V := f ⁻¹ᵁ U.1
  have hV : IsAffineOpen V := U.2.preimage f
  let p := U.2.primeIdealOf ⟨f y,hy⟩
  let q := hV.primeIdealOf ⟨y,hy⟩
  let φ := (f.app U.1).hom
  have hφ : Function.Surjective φ := f.app_surjective U.1 U.2
  have hpq : q.asIdeal.comap φ = p.asIdeal := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE U.1 U.2 V hV le_rfl hy
    simpa [Scheme.Hom.appLE, p, q, φ, V] using congrArg PrimeSpectrum.asIdeal h
  have hmon : p.asIdeal.primeCompl.map φ = q.asIdeal.primeCompl := by
    have hc : p.asIdeal.primeCompl = (q.asIdeal.comap φ).primeCompl := by
      ext a
      simp only [Ideal.mem_primeCompl_iff, hpq]
    rw [hc]
    exact q.asIdeal.map_primeCompl_comap_of_surjective φ hφ
  let : Algebra Γ(X,U.1) (X.presheaf.stalk (f y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨f y,hy⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk (f y)) p.asIdeal :=
    U.2.isLocalization_stalk ⟨f y,hy⟩
  let : Algebra Γ(Y,V) (Y.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y,hy⟩
  let : IsLocalization.AtPrime (Y.presheaf.stalk y) q.asIdeal :=
    hV.isLocalization_stalk ⟨y,hy⟩
  have he : (f.stalkMap y).hom =
      IsLocalization.map (Y.presheaf.stalk y) φ (hmon.symm ▸ p.asIdeal.primeCompl.le_comap_map) := by
    apply IsLocalization.ringHom_ext p.asIdeal.primeCompl
    ext a
    change (f.stalkMap y) (X.presheaf.germ U.1 (f y) hy a) = _
    rw [Scheme.Hom.germ_stalkMap_apply]
    exact (IsLocalization.map_eq (S := X.presheaf.stalk (f y))
      (Q := Y.presheaf.stalk y) (g := φ)
      (hmon.symm ▸ p.asIdeal.primeCompl.le_comap_map) a).symm
  rw [he, IsLocalization.ker_map (Y.presheaf.stalk y) φ hmon, Scheme.Hom.ker_apply]
  rfl

lemma subscheme_stalk_kernel (I : X.IdealSheafData)
    (U : X.affineOpens) (y : I.subscheme) (hy : I.subschemeι y ∈ U.1) :
    RingHom.ker (I.subschemeι.stalkMap y).hom =
      (I.ideal U).map (X.presheaf.germ U.1 (I.subschemeι y) hy).hom := by
  simpa using closedImmersion_stalk_kernel I.subschemeι U y hy

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
