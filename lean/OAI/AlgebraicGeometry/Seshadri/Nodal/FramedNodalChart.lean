import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Jets.QuadraticJets
import OAI.AlgebraicGeometry.Seshadri.Jets.CenteredJetChart

namespace OAI


                                          
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AlgebraicJets MaximalSeshadri.QuadraticJets
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K] [IsAlgClosed K] [Fintype σ] {X : Scheme} {M : X.Modules}

omit [IsAlgClosed K] in
theorem exists_centered_etale_ratios_in_open [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (k : K →+* Γ(X, ⊤)) (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)]
    (hbase : sectionsMorphism k s hs ≫ projectiveToSpec = g)
    (p : X) (hp : p ∉ centeredOpen s) (W : X.Opens) (hpW : p ∈ W) :
    ∃ U : X.affineOpens, p ∈ U.1 ∧ U.1 ≤ W ∧
      ∃ hU : U.1 ≤ SectionOpens.isoOpen (s none),
        ∃ i : Fin 2 → σ,
          (MvPolynomial.eval₂Hom (openScalars g U.1)
            (fun j => -affineSectionRatios s U hU (some (i j)))).Etale ∧
          (∀ j : σ, X.basicOpen (affineSectionRatios s U hU (some j)) ≤ centeredOpen s) ∧
          ∀ c : K, U.1.topIso.hom (U.1.ι.appTop (k c)) = openScalars g U.1 c := by
  classical
  have hp₀ := center_mem_distinguished s hs p hp
  obtain ⟨C, hpC, hCUW, hcoord⟩ := exists_etale_projective_chart g
    (sectionsMorphism k s hs) hbase none (W ⊓ SectionOpens.isoOpen (s none)) p ⟨hpW,hp₀⟩
      (by rwa [← sectionsMorphism_preimage k s hs none] at hp₀)
  have hCU := hCUW.trans inf_le_right
  let : Finite C.κ := C.finite
  let : Fintype C.κ := Fintype.ofFinite _
  have hcard : Fintype.card C.κ = 2 := by rw [← Nat.card_eq_fintype_card]; exact C.card
  let e : Fin 2 ≃ C.κ := (Fintype.equivFinOfCardEq hcard).symm
  have hi (j : Fin 2) : ∃ i : σ, (C.a (e j)).1 = some i :=
    Option.ne_none_iff_exists'.mp (by simpa only [hcoord] using (C.a (e j)).2)
  let i : Fin 2 → σ := fun j => (hi j).choose
  have his (j : Fin 2) : (C.a (e j)).1 = some (i j) := (hi j).choose_spec
  let φ : PolyChart (R := K) (none : Option σ) →+* Γ(X, C.U.1) := hcoord ▸ C.φ
  have hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K (Option σ)) (MvPolynomial.X none) (poly_X_mem none) (by decide) =
        C.U.2.fromSpec ≫ sectionsMorphism k s hs := by
    exact cast_chart_factor (sectionsMorphism k s hs) C.U hcoord C.φ C.factor
  have heq := sectionsMorphism_affine_ratios k s hs C.U hCU φ hφ
  refine ⟨C.U, hpC, hCUW.trans inf_le_left, hCU, i, ?_, ?_, ?_⟩
  · have h := etale_reindex (openScalars g C.U.1)
      (fun j => -C.φ (chartCoordinate C.coord (C.a j).1)) e C.etale
    convert h using 1
    congr 1
    funext j
    have hc : C.φ (chartCoordinate C.coord (C.a (e j)).1) =
        φ (chartCoordinate none (some (i j))) := by
      rw [his]
      exact cast_chart_coordinate C.U hcoord C.φ _
    rw [Function.comp_apply, hc, heq.1]
  · intro j
    rw [← heq.1]
    exact (chart_coordinate_basicOpen_le k s hs C.U none (some j) φ hφ).trans
      (le_iSup (fun j => SectionOpens.isoOpen (s (some j))) j)
  · intro c
    rw [← heq.2]
    let : Algebra K Γ(X, C.U.1) := (openScalars g C.U.1).toAlgebra
    exact projective_affine_constants (sectionsMorphism k s hs) g hbase
      C.U (spec_openScalars g C.U) none φ hφ c

theorem exists_centered_rational_jet_in_open [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (k : K →+* Γ(X, ⊤)) (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)]
    (hbase : sectionsMorphism k s hs ≫ projectiveToSpec = g)
    (p : X) (hp : p ∉ centeredOpen s) (W : X.Opens) (hpW : p ∈ W) :
    ∃ U : X.affineOpens, p ∈ U.1 ∧ U.1 ≤ W ∧
      ∃ hU : U.1 ≤ SectionOpens.isoOpen (s none),
        let _ : Algebra K Γ(X, U.1) := (openScalars g U.1).toAlgebra
        ∃ i : Fin 2 → σ, ∃ ρ : Γ(X, U.1) →ₐ[K] K,
          ∃ τ : Γ(X, U.1) →ₐ[K] JetAlgebra (Fin 2) K 3,
            (∀ j : σ, ρ (affineSectionRatios s U hU (some j)) = 0) ∧
            RingHom.ker τ = (RingHom.ker ρ)^3 ∧
            (∀ f, jetAugment 3 (by decide) (τ f) = ρ f) ∧
            (∀ j : Fin 2, τ (affineSectionRatios s U hU (some (i j))) =
              -Ideal.Quotient.mk _ (MvPolynomial.X j)) ∧
            (MvPolynomial.eval₂Hom (openScalars g U.1)
              (fun j => -affineSectionRatios s U hU (some (i j)))).Etale ∧
            ∀ c : K, U.1.topIso.hom (U.1.ι.appTop (k c)) = openScalars g U.1 c := by
  obtain ⟨U, hpU, hUW, hU, i, hi, hb, hk⟩ := exists_centered_etale_ratios_in_open g k s hs hbase p hp W hpW
  let : Algebra K Γ(X, U.1) := (openScalars g U.1).toAlgebra
  let a := affineSectionRatios s U hU
  let : Algebra (MvPolynomial (Fin 2) K) Γ(X, U.1) :=
    (eval₂Hom (openScalars g U.1) (fun j => -a (some (i j)))).toAlgebra
  let : IsScalarTower K (MvPolynomial (Fin 2) K) Γ(X, U.1) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext c
      exact (eval₂Hom_C (openScalars g U.1) _ c).symm)
  let : Algebra.Etale (MvPolynomial (Fin 2) K) Γ(X, U.1) := hi
  let : Algebra.FiniteType K Γ(X, U.1) := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType K (MvPolynomial (Fin 2) K))
    (inferInstance : Algebra.FiniteType (MvPolynomial (Fin 2) K) Γ(X, U.1))
  let x : PrimeSpectrum Γ(X, U.1) := U.2.isoSpec.hom ⟨p, hpU⟩
  let : x.asIdeal.IsPrime := x.isPrime
  have hpx : U.2.fromSpec x = p := by
    change (U.2.isoSpec.hom ≫ U.2.fromSpec) ⟨p, hpU⟩ = p
    rw [U.2.isoSpec_hom_fromSpec]
    rfl
  have ham (j : σ) : a (some j) ∈ x.asIdeal := by
    by_contra h
    have hx : x ∈ PrimeSpectrum.basicOpen (a (some j)) := h
    rw [← U.2.fromSpec_preimage_basicOpen] at hx
    change U.2.fromSpec x ∈ X.basicOpen (a (some j)) at hx
    rw [hpx] at hx
    exact hp (hb j hx)
  obtain ⟨ρ₀⟩ := exists_point_finite_type (K := K) (R := Γ(X, U.1) ⧸ x.asIdeal)
  let ρ : Γ(X, U.1) →ₐ[K] K := ρ₀.comp (Ideal.Quotient.mkₐ K x.asIdeal)
  have ha (j : σ) : ρ (a (some j)) = 0 := by
    change ρ₀ (Ideal.Quotient.mk _ (a (some j))) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (ham j), map_zero]
  obtain ⟨τ, hτ, haug, hc⟩ := exists_quadratic_jet_of_etale a ρ ha i hi
  exact ⟨U, hpU, hUW, hU, i, ρ, τ, ha, hτ, haug, hc, hi, hk⟩

end
end MaximalSeshadri.Projective

end


end OAI
