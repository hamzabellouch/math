import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.SmoothAffineRefinement
import OAI.AlgebraicGeometry.Seshadri.Projective.ProjectiveCoordinates

namespace OAI

section
noncomputable section
                                             

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace KaehlerDifferential
open MaximalSeshadri.Projective MaximalSeshadri.AlgebraicJets
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme} {σ : Type}

structure EtaleProjectiveChart (g : X ⟶ Spec (CommRingCat.of K))
    (h : X ⟶ Proj (PolyGrade K σ)) where
  U : X.affineOpens
  coord : σ
  nonempty : Nonempty U.1
  φ : PolyChart (R := K) coord →+* Γ(X, U.1)
  factor : Spec.map (CommRingCat.ofHom φ) ≫
    Proj.awayι (PolyGrade K σ) (MvPolynomial.X coord) (poly_X_mem coord) (by decide) =
      U.2.fromSpec ≫ h
  κ : Type
  finite : Finite κ
  a : κ → ChartVariables coord
  card : Nat.card κ = 2
  etale : (MvPolynomial.eval₂Hom (openScalars g U.1)
    (fun k => -φ (chartCoordinate coord (a k).1))).Etale

lemma restrict_projective_factor (h : X ⟶ Proj (PolyGrade K σ))
    (U V : X.affineOpens) (e : U.1 ≤ V.1) (i : σ)
    (φ : PolyChart (R := K) i →+* Γ(X, V.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
        V.2.fromSpec ≫ h) :
    Spec.map (CommRingCat.ofHom ((X.presheaf.map (homOfLE e).op).hom.comp φ)) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
        U.2.fromSpec ≫ h := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hφ, ← Category.assoc,
    CommRingCat.ofHom_hom, V.2.map_fromSpec U.2]

lemma etale_aeval_equiv {A B ι : Type} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (e : A ≃ₐ[K] B) (v : ι → A)
    (hv : (MvPolynomial.aeval (R := K) v).toRingHom.Etale) :
    (MvPolynomial.aeval (R := K) (fun i => e (v i))).toRingHom.Etale := by
  have hh := RingHom.Etale.respectsIso.1 _ e.toRingEquiv hv
  change (e.toAlgHom.comp (MvPolynomial.aeval (R := K) v)).toRingHom.Etale at hh
  rw [MvPolynomial.comp_aeval] at hh
  exact hh

theorem exists_etale_projective_chart [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (h : X ⟶ Proj (PolyGrade K σ)) [IsClosedImmersion h]
    (hbase : h ≫ projectiveToSpec = g)
    (i : σ) (W : X.Opens) (x : X) (hxW : x ∈ W)
    (hxi : h x ∈ Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i)) :
    ∃ C : EtaleProjectiveChart g h, x ∈ C.U.1 ∧ C.U.1 ≤ W ∧ C.coord = i := by
  classical
  obtain ⟨V, φ, hV, hsurj, hφ⟩ := closed_projective_affine_surjective h i
  have hxV : x ∈ V.1 := by rwa [hV]
  obtain ⟨U, hxU, hUW, hstd⟩ := exists_standard_smooth_affine_inside g 2
    (W ⊓ V.1) x ⟨hxW, hxV⟩
  have e : U.1 ≤ V.1 := hUW.trans inf_le_right
  let : Nonempty V.1 := ⟨⟨x, hxV⟩⟩
  let : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  let : Algebra K Γ(X, V.1) := (openScalars g V.1).toAlgebra
  let : Algebra K Γ(X, U.1) := (openScalars g U.1).toAlgebra
  let r : Γ(X, V.1) →+* Γ(X, U.1) := (X.presheaf.map (homOfLE e).op).hom
  let : Algebra Γ(X, V.1) Γ(X, U.1) := r.toAlgebra
  let : IsScalarTower K Γ(X, V.1) Γ(X, U.1) :=
    IsScalarTower.of_algebraMap_eq' (openScalars_restrict g e).symm
  let : Algebra.Etale Γ(X, V.1) Γ(X, U.1) := affine_restriction_etale U V e
  have hconst := projective_affine_constants h g hbase V (spec_openScalars g V) i φ hφ
  have hspan := differentials_span_projective_chart i φ hsurj hconst
  have hs := differentials_span_of_formallyEtale (T := Γ(X, U.1))
    (fun j : ChartVariables i => -φ (chartCoordinate i j.1)) hspan
  let φU := r.comp φ
  let : Algebra.IsStandardSmoothOfRelativeDimension 2 K Γ(X, U.1) := hstd
  let p : PrimeSpectrum Γ(X, U.1) := U.2.isoSpec.hom ⟨x, hxU⟩
  obtain ⟨f, hfp, κ, hκ, a, hcard, het⟩ := exists_local_etale_from_spanning 2
    (fun j : ChartVariables i => -φU (chartCoordinate i j.1))
    (by simpa only [φU, RingHom.comp_apply, map_neg, RingHom.algebraMap_toAlgebra] using hs) p.asIdeal
  let T : X.affineOpens := ⟨X.basicOpen f, U.2.basicOpen f⟩
  have hxf : x ∈ T.1 := by
    have hp : U.2.fromSpec p = x := by
      change (U.2.isoSpec.hom ≫ U.2.fromSpec) ⟨x, hxU⟩ = x
      rw [U.2.isoSpec_hom_fromSpec]
      rfl
    have hm : p ∈ PrimeSpectrum.basicOpen f := hfp
    rw [← U.2.fromSpec_preimage_basicOpen f] at hm
    change U.2.fromSpec p ∈ X.basicOpen f at hm
    rwa [hp] at hm
  let r' : Γ(X, U.1) →+* Γ(X, T.1) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  let : Algebra K Γ(X, T.1) := (openScalars g T.1).toAlgebra
  let : IsScalarTower K Γ(X, U.1) Γ(X, T.1) :=
    IsScalarTower.of_algebraMap_eq' (openScalars_restrict g (X.basicOpen_le f)).symm
  let : IsLocalization.Away f Γ(X, T.1) := U.2.isLocalization_basicOpen f
  let ρ := (IsLocalization.algEquiv (Submonoid.powers f)
    (Localization.Away f) Γ(X, T.1)).restrictScalars K
  have het' := etale_aeval_equiv ρ _ het
  let φT := r'.comp φU
  have hφU := restrict_projective_factor h U V e i φ hφ
  refine ⟨{ U := T
            coord := i
            nonempty := ⟨⟨x, hxf⟩⟩
            φ := φT
            factor := restrict_projective_factor h T U (X.basicOpen_le f) i φU hφU
            κ := κ
            finite := hκ
            a := a
            card := hcard
            etale := ?_ }, hxf,
      (X.basicOpen_le f).trans (hUW.trans inf_le_left), rfl⟩
  convert het' using 1
  apply MvPolynomial.ringHom_ext
  · intro c
    change MvPolynomial.eval₂Hom _ _ (MvPolynomial.C c) =
      MvPolynomial.aeval _ (MvPolynomial.C c)
    rw [MvPolynomial.eval₂Hom_C, MvPolynomial.aeval_C]
    rfl
  · intro k
    change MvPolynomial.eval₂Hom _ _ (MvPolynomial.X k) =
      MvPolynomial.aeval _ (MvPolynomial.X k)
    rw [MvPolynomial.eval₂Hom_X', MvPolynomial.aeval_X]
    change -r' (φU (chartCoordinate i (a k).1)) =
      ρ (algebraMap Γ(X, U.1) (Localization.Away f) (-φU (chartCoordinate i (a k).1)))
    rw [← map_neg]
    exact ((IsLocalization.algEquiv (Submonoid.powers f)
      (Localization.Away f) Γ(X, T.1)).commutes
      (-φU (chartCoordinate i (a k).1))).symm

end
end MaximalSeshadri.ProjectiveBertini


end
end

end OAI
