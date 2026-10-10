import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Blowup.FiniteCenters
import OAI.AlgebraicGeometry.Seshadri.Sheaves.AffineOrderRestriction

namespace OAI


                                              
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini

variable {X Y Z : Scheme.{0}}

lemma ker_comap_open_comp (q : Z ⟶ Y) (j : Y ⟶ X) [IsOpenImmersion j]
    [IsClosedImmersion (q ≫ j)] : (q ≫ j).ker.comap j = q.ker := by
  have hr : Set.range (q ≫ j) ⊆ Set.range j := by
    rintro _ ⟨z,rfl⟩; exact ⟨q z,rfl⟩
  have he : IsOpenImmersion.lift j (q ≫ j) hr = q := by
    symm; exact IsOpenImmersion.lift_uniq j (q ≫ j) hr q rfl
  have hp := IsOpenImmersion.isPullback_lift_id (q ≫ j) j hr
  rw [he] at hp
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso hp.isoPullback.hom, hp.isoPullback_hom_fst]

lemma affineComplexPoint_ideal (g : X ⟶ complexBase) (U : X.affineOpens)
    (ρ : letI := (openScalars g U.1).toAlgebra; Γ(X,U.1) →ₐ[ℂ] ℂ) :
    (affineComplexPoint g U ρ).left.ker.ideal U = RingHom.ker ρ := by
  let := (openScalars g U.1).toAlgebra
  have : IsClosedImmersion (affineComplexPoint g U ρ).left :=
    isClosedImmersion_of_comp_eq_id g _ (affineComplexPoint g U ρ).w
  apply IdealPullback.specIdeal_injective
  rw [← IdealPullback.comap_fromSpec]
  change (Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ U.2.fromSpec).ker.comap U.2.fromSpec = _
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ U.2.fromSpec) :=
    inferInstanceAs (IsClosedImmersion (affineComplexPoint g U ρ).left)
  let : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
  rw [ker_comap_open_comp,IdealPullback.specMap_ker]
  rfl

lemma ideal_eq_on_smaller {I J : X.IdealSheafData} (W : X.Opens)
    (hIJ : I.comap W.ι = J.comap W.ι) (V : X.affineOpens) (hVW : V.1 ≤ W) :
    I.ideal V = J.ideal V := by
  have hr : Set.range V.2.fromSpec ⊆ Set.range W.ι := by
    rw [V.2.range_fromSpec,Scheme.Opens.range_ι]
    exact hVW
  let f := IsOpenImmersion.lift W.ι V.2.fromSpec hr
  have hf : f ≫ W.ι = V.2.fromSpec := IsOpenImmersion.lift_fac _ _ _
  apply IdealPullback.specIdeal_injective
  rw [← IdealPullback.comap_fromSpec,← IdealPullback.comap_fromSpec,← hf,
    Scheme.IdealSheafData.comap_comp,Scheme.IdealSheafData.comap_comp,hIJ]

lemma centre_local_power_membership (S : Surface) {r : ℕ} (p : Configuration S r)
    (M : LineBundle S.scheme) (n : ℕ) (s : O S.scheme ⟶ M.sheaf)
    (U : Fin r → S.scheme.affineOpens)
    (e : ∀ i, M.sheaf.restrict (U i).1.ι ≅ O (U i).1.toScheme)
    (ρ : ∀ i, letI := (openScalars S.structureMap (U i).1).toAlgebra;
      Γ(S.scheme,(U i).1) →ₐ[ℂ] ℂ)
    (hρ : ∀ i, affineComplexPoint S.structureMap (U i) (ρ i) = p.val i)
    (hs : ∀ i, affineCoefficient (U i) (e i) s ∈ (RingHom.ker (ρ i))^n) :
    ∀ x : S.scheme, ∃ V : S.scheme.affineOpens, x ∈ V.1 ∧
      ∃ eV : M.sheaf.restrict V.1.ι ≅ O V.1.toScheme,
        affineCoefficient V eV s ∈ (centreIdeal S r p).ideal V ^ n := by
  classical
  let (i : Fin r) : Algebra ℂ Γ(S.scheme,(U i).1) := (openScalars S.structureMap (U i).1).toAlgebra
  let q : Fin r → (Spec (.of ℂ) ⟶ S.scheme) := fun i => (p.val i).left
  have hq (i : Fin r) : q i ≫ S.structureMap = 𝟙 _ := (p.val i).w
  have hd : Function.Injective (fun i => q i (fieldPoint ℂ)) := p.property
  intro x
  by_cases hx : x ∈ (FinitePointBlowup.pointCentre q).support
  · obtain ⟨i,hi⟩ := (FinitePointBlowup.mem_centre_support q x).mp hx
    have hxi : x = q i (fieldPoint ℂ) := by
      change x ∈ ((q i).ker.support : Set S.scheme) at hi
      rw [FinitePointBlowup.point_support q S.structureMap hq i] at hi
      exact hi
    have hxU : x ∈ (U i).1 := by
      rw [hxi]
      change (p.val i).left (fieldPoint ℂ) ∈ (U i).1
      rw [← hρ i]
      apply (U i).2.range_fromSpec.subset
      exact ⟨Spec.map (CommRingCat.ofHom (ρ i).toRingHom) (fieldPoint ℂ), rfl⟩
    have hxW : x ∈ FinitePointBlowup.pointOpen q i := by
      rw [hxi]; exact FinitePointBlowup.point_mem_own_open q S.structureMap hq hd i _
    obtain ⟨_,⟨V₀,hV₀,rfl⟩,hxV,hV⟩ :=
      S.scheme.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ (U i).1 ⊓ FinitePointBlowup.pointOpen q i from ⟨hxU,hxW⟩)
        ((U i).1 ⊓ FinitePointBlowup.pointOpen q i).isOpen
    let V : S.scheme.affineOpens := ⟨V₀,hV₀⟩
    let eV := frameOnSmaller (e i) V.1 (fun z hz => (hV hz).1)
    obtain ⟨σ,hσ⟩ := affineComplexPoint_factor S.structureMap V (p.val i) (by change q i (fieldPoint ℂ) ∈ V.1; rwa [← hxi])
    refine ⟨V,hxV,eV,?_⟩
    have hI : (centreIdeal S r p).ideal V = (q i).ker.ideal V :=
      ideal_eq_on_smaller (FinitePointBlowup.pointOpen q i)
        (FinitePointBlowup.pointOpen_comap_centre q i) V (fun z hz => (hV hz).2)
    rw [hI,show (q i).ker.ideal V = RingHom.ker σ by
      rw [show q i = (affineComplexPoint S.structureMap V σ).left from
        congrArg Over.Hom.left hσ.symm]; exact affineComplexPoint_ideal _ _ _]
    exact (affineCoefficient_order_restrict_iff S.structureMap (U i) V
      (fun z hz => (hV hz).1) (e i) eV (ρ i) σ ((hρ i).trans hσ.symm) s n).mp (hs i)
  · let W := FinitePointBlowup.outsideOpen q
    obtain ⟨A,hxA,⟨eA⟩⟩ := M.locallyRankOne x
    obtain ⟨_,⟨V₀,hV₀,rfl⟩,hxV,hV⟩ := S.scheme.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ A ⊓ W from ⟨hxA,hx⟩) (A ⊓ W).isOpen
    let V : S.scheme.affineOpens := ⟨V₀,hV₀⟩
    refine ⟨V,hxV,frameOnSmaller eA V.1 (fun z hz => (hV hz).1),?_⟩
    have hI : (centreIdeal S r p).ideal V = (⊤ : S.scheme.IdealSheafData).ideal V := by
      apply ideal_eq_on_smaller W _ V (fun z hz => (hV hz).2)
      rw [Scheme.IdealSheafData.comap_top]
      exact FinitePointBlowup.outside_comap_centre q
    rw [hI]
    change _ ∈ (⊤ : Ideal Γ(S.scheme,V.1))^n
    rw [Ideal.top_pow]
    trivial

end
end MaximalSeshadri.Geometry

end

end OAI
