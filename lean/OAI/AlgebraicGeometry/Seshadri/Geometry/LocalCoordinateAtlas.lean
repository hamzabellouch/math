import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.FiniteAtlas

namespace OAI

section
noncomputable section
                                              
section

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace KaehlerDifferential
open MaximalSeshadri.Projective MaximalSeshadri.AlgebraicJets
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme} {σ : Type}

theorem etale_chart_of_affine_coordinates [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (h : X ⟶ Proj (PolyGrade K σ))
    (hbase : h ≫ projectiveToSpec = g)
    (i : σ) (V : X.affineOpens)
    (φ : PolyChart (R := K) i →+* Γ(X, V.1)) (hsurj : Function.Surjective φ)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
        V.2.fromSpec ≫ h)
    (W : X.Opens) (x : X) (hxW : x ∈ W) (hxV : x ∈ V.1) :
    ∃ C : EtaleProjectiveChart g h, x ∈ C.U.1 ∧ C.U.1 ≤ W ∧ C.coord = i := by
  classical
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

theorem finite_atlas_of_local_coordinates [IsIntegral X] [CompactSpace X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (h : X ⟶ Proj (PolyGrade K σ))
    (hbase : h ≫ projectiveToSpec = g)
    (hlocal : ∀ x : X, ∃ i : σ, ∃ V : X.affineOpens, x ∈ V.1 ∧
      ∃ φ : PolyChart (R := K) i →+* Γ(X, V.1), Function.Surjective φ ∧
        Spec.map (CommRingCat.ofHom φ) ≫
          Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
            V.2.fromSpec ≫ h) :
    Nonempty (OverlappingEtaleProjectiveAtlas g h) := by
  classical
  have hchart (W : X.Opens) (x : X) (hxW : x ∈ W) :
      ∃ C : EtaleProjectiveChart g h, x ∈ C.U.1 ∧ C.U.1 ≤ W := by
    obtain ⟨i, V, hxV, φ, hsurj, hφ⟩ := hlocal x
    obtain ⟨C, hxC, hCW, _⟩ :=
      etale_chart_of_affine_coordinates g h hbase i V φ hsurj hφ W x hxW hxV
    exact ⟨C, hxC, hCW⟩
  choose C hC using (fun x : X => hchart ⊤ x
    (show x ∈ (⊤ : X.Opens) from trivial))
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : X => ((C x).U.1 : Set X))
    (fun x => (C x).U.1.isOpen) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, (hC x).1⟩)
  have hcover : ∀ x : X, ∃ j : s, x ∈ (C j.1).U.1 := by
    intro x
    obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ⟨⟨j, hj⟩, hx⟩
  let x₀ : X := Classical.arbitrary X
  obtain ⟨j₀, _⟩ := hcover x₀
  have hov (j : s) : ∃ D : EtaleProjectiveChart g h,
      D.U.1 ≤ (C j₀.1).U.1 ∧ D.U.1 ≤ (C j.1).U.1 := by
    have hne (k : s) : ((C k.1).U.1 : Set X).Nonempty :=
      Set.nonempty_coe_sort.mp (C k.1).nonempty
    obtain ⟨x, hx₀, hx⟩ := nonempty_preirreducible_inter
      (C j₀.1).U.1.isOpen (C j.1).U.1.isOpen (hne j₀) (hne j)
    obtain ⟨D, _, hD⟩ := hchart
      ((C j₀.1).U.1 ⊓ (C j.1).U.1) x ⟨hx₀, hx⟩
    exact ⟨D, hD.trans inf_le_left, hD.trans inf_le_right⟩
  choose D hD₀ hD using hov
  refine ⟨{ ι := s ⊕ s
            finite := inferInstance
            chart := Sum.elim (fun j => C j.1) D
            cover := ?_
            base := Sum.inl j₀
            overlap := fun j => Sum.inr (Sum.elim id id j)
            left := ?_
            right := ?_ }⟩
  · intro x
    obtain ⟨j, hj⟩ := hcover x
    exact ⟨Sum.inl j, hj⟩
  · intro j
    cases j with
    | inl j => exact hD₀ j
    | inr j => exact hD₀ j
  · intro j
    cases j with
    | inl j => exact hD j
    | inr j => exact le_rfl

end
end MaximalSeshadri.ProjectiveBertini

end


end
end

end OAI
