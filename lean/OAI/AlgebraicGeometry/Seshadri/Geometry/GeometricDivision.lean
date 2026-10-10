import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.OpenChartDegree

namespace OAI

section
noncomputable section
                                           
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X : Scheme.{0}}

lemma section_value_naturality {M : X.Modules} (s : O X ⟶ M)
    {U V : X.Opens} (h : V ≤ U) :
    M.presheaf.map (homOfLE h).op (s.app U (1 : Γ(X,U))) =
      s.app V (1 : Γ(X,V)) := by
  have ht := CategoryTheory.congr_fun (s.mapPresheaf.naturality (homOfLE h).op)
    (1 : Γ(X,U))
  change s.app V (X.presheaf.map (homOfLE h).op (1 : Γ(X,U))) =
    M.presheaf.map (homOfLE h).op (s.app U (1 : Γ(X,U))) at ht
  simpa only [map_one] using ht.symm

lemma section_eq_zero_of_top_value {M : X.Modules} (s : O X ⟶ M)
    (hs : s.app ⊤ (1 : Γ(X,⊤)) = 0) : s = 0 := by
  ext U a
  change Γ(X,U) at a
  change s.app U a = 0
  have h := s.app_smul (r := a) (x := (1 : Γ(X,U)))
  change s.app U (a*1 : Γ(X,U)) = a • s.app U (1 : Γ(X,U)) at h
  rw [mul_one] at h
  rw [h, ← section_value_naturality s (show U ≤ ⊤ from le_top), hs,map_zero,smul_zero]

lemma section_eq_zero_of_local_restrictions {M : X.Modules} (s : O X ⟶ M)
    (hs : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ restrictSection U.ι s = 0) : s = 0 := by
  apply section_eq_zero_of_top_value
  let F : (X : TopCat).Sheaf AddCommGrpCat := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
  apply TopCat.Presheaf.section_ext F ⊤ (s.app ⊤ (1 : Γ(X,⊤))) 0
  intro x hx
  obtain ⟨U,hxU,hU⟩ := hs x
  have hv : s.app U (1 : Γ(X,U)) = 0 := by
    have ht := congrArg (fun q : O U.toScheme ⟶ M.restrict U.ι =>
      q.app ⊤ (1 : Γ(U.toScheme,⊤))) hU
    change s.app (U.ι ''ᵁ ⊤) ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme,⊤))) = 0 at ht
    rw [map_one] at ht
    have htop : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := by
      rw [Scheme.Hom.image_top_eq_opensRange,Scheme.Opens.opensRange_ι]
    suffices h : ∀ V : X.Opens, V = U → s.app V (1 : Γ(X,V)) = 0 →
        s.app U (1 : Γ(X,U)) = 0 from h _ htop ht
    intro V he ht
    subst V
    exact ht
  change M.presheaf.germ ⊤ x hx (s.app ⊤ (1 : Γ(X,⊤))) =
    M.presheaf.germ ⊤ x hx 0
  rw [← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE (show U ≤ ⊤ from le_top)) x hxU]
  rw [section_value_naturality s, hv, map_zero, map_zero]

theorem global_division_of_local_lifts {M N : X.Modules} (f : M ⟶ N) [Mono f]
    (s : O X ⟶ N)
    (hs : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ t : O U.toScheme ⟶ M.restrict U.ι,
        t ≫ (Scheme.Modules.restrictFunctor U.ι).map f = restrictSection U.ι s) :
    ∃! t : O X ⟶ M, t ≫ f = s := by
  have hz : s ≫ cokernel.π f = 0 := by
    apply section_eq_zero_of_local_restrictions
    intro x
    obtain ⟨U,hx,t,ht⟩ := hs x
    refine ⟨U,hx,?_⟩
    have hc : restrictSection U.ι (s ≫ cokernel.π f) =
        restrictSection U.ι s ≫ (Scheme.Modules.restrictFunctor U.ι).map (cokernel.π f) := by
      exact (congrArg (fun morphism :
          (Scheme.Modules.restrictFunctor U.ι).obj (O X) ⟶
            (Scheme.Modules.restrictFunctor U.ι).obj (cokernel f) =>
          (Scheme.Modules.restrictUnitIso U.ι).inv ≫ morphism)
        ((Scheme.Modules.restrictFunctor U.ι).map_comp s (cokernel.π f))).trans
          (Category.assoc _ _ _).symm
    rw [hc, ← ht, Category.assoc, ← Functor.map_comp,cokernel.condition,Functor.map_zero,comp_zero]
  refine ⟨Abelian.monoLift _ s hz,Abelian.monoLift_comp _ s hz,?_⟩
  intro t ht
  apply (cancel_mono f).mp
  rw [ht,Abelian.monoLift_comp]

lemma pullback_zero_coefficient_mem (p : X ⟶ Spec (CommRingCat.of ℂ))
    (I : X.IdealSheafData) (L : LineBundle X) (s : O X ⟶ L.sheaf)
    (hs : pullbackSection I.subschemeι s = 0) (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)) ∈ I.ideal U := by
  let : Algebra ℂ Γ(X,U.1) := (openScalars p U.1).toAlgebra
  let : Algebra ℂ Γ((I.subschemeι ⁻¹ᵁ U.1).toScheme,⊤) :=
    (baseScalars ((I.subschemeι ⁻¹ᵁ U.1).ι ≫ (I.subschemeι ≫ p))).toAlgebra
  rw [← structuralOpenChartMap_ker p I U]
  change structuralOpenChartMap p I.subschemeι U.1
    (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))) = 0
  obtain ⟨eF,he⟩ := exists_restricted_pullback_frame I.subschemeι U.1 e s
  have hzero : coefficient eF
      (restrictSection (I.subschemeι ⁻¹ᵁ U.1).ι (pullbackSection I.subschemeι s)) = 0 := by
    rw [hs,restrictSection_zero,coefficient_zero]
  rw [he] at hzero
  change (I.subschemeι ∣_ U.1).appTop
    (U.1.topIso.inv (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)))) = 0
  rw [U.1.topIso.hom_inv_id_apply]
  exact hzero

lemma framed_local_division {M N : X.Modules} (e : M ≅ O X) (d : N ≅ O X)
    (f : M ⟶ N) (s : O X ⟶ N)
    (hs : coefficient d s ∈ Ideal.span {endValue (e.inv ≫ f ≫ d.hom)}) :
    ∃ t : O X ⟶ M, t ≫ f = s := by
  obtain ⟨r,hr⟩ := Ideal.mem_span_singleton.mp hs
  refine ⟨scalarEnd r ≫ e.inv,?_⟩
  apply (cancel_mono d.hom).mp
  apply endValue_injective
  rw [Category.assoc,Category.assoc,endValue_comp,endValue_scalarEnd]
  change r * endValue (e.inv ≫ f ≫ d.hom) = coefficient d s
  rw [mul_comm,← hr]

theorem geometric_global_division (p : X ⟶ Spec (CommRingCat.of ℂ))
    (M N : LineBundle X) (f : M.sheaf ⟶ N.sheaf) [Mono f]
    (I : X.IdealSheafData)
    (heq : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span {U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map f ≫ d.hom))})
    (s : O X ⟶ N.sheaf) (hs : pullbackSection I.subschemeι s = 0) :
    ∃! t : O X ⟶ M.sheaf, t ≫ f = s := by
  apply global_division_of_local_lifts
  intro x
  obtain ⟨U,hx,e,d,hI⟩ := heq x
  refine ⟨U.1,hx,?_⟩
  apply framed_local_division e d
  have hb := pullback_zero_coefficient_mem p I N s hs U d
  rw [hI,Ideal.mem_span_singleton] at hb
  obtain ⟨r,hr⟩ := hb
  rw [Ideal.mem_span_singleton]
  refine ⟨U.1.topIso.inv r,?_⟩
  have h := congrArg U.1.topIso.inv hr
  simpa only [map_mul,U.1.topIso.hom_inv_id_apply] using h

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
