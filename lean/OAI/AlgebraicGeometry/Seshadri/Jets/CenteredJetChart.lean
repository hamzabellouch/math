import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.GlobalIntegralQuartic

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.ProjectiveBertini
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K] {X : Scheme} {M : X.Modules}

def affineSectionRatios (s : Option σ → (O X ⟶ M))
    (U : X.affineOpens) (hU : U.1 ≤ SectionOpens.isoOpen (s none))
    (j : Option σ) : Γ(X, U.1) :=
  U.1.topIso.hom (coefficient (sectionFrameOn (s none) U.1 hU)
    (restrictSection U.1.ι (s j)))

lemma affineSectionRatios_none (s : Option σ → (O X ⟶ M))
    (U : X.affineOpens) (hU : U.1 ≤ SectionOpens.isoOpen (s none)) :
    affineSectionRatios s U hU none = 1 := by
  simp only [affineSectionRatios, sectionFrameOn_normalized, map_one]

lemma sectionsMorphism_affine_ratios (k : K →+* Γ(X, ⊤))
    (s : Option σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (U : X.affineOpens) (hU : U.1 ≤ SectionOpens.isoOpen (s none))
    (φ : PolyChart (R := K) (none : Option σ) →+* Γ(X, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K (Option σ)) (MvPolynomial.X none) (poly_X_mem none) (by decide) =
        U.2.fromSpec ≫ sectionsMorphism k s hs) :
    (∀ j, φ (chartCoordinate none j) = affineSectionRatios s U hU j) ∧
      ∀ c, φ (chartConstants none c) =
        U.1.topIso.hom (U.1.ι.appTop (k c)) := by
  let a := affineSectionRatios s U hU
  let kU : K →+* Γ(X, U.1) := U.1.topIso.hom.hom.comp (U.1.ι.appTop.hom.comp k)
  have hai : a none = 1 := affineSectionRatios_none s U hU
  have hφ' : φ = evalAway (MvPolynomial.eval₂Hom kU a) (MvPolynomial.X none)
      (by simpa only [MvPolynomial.eval₂Hom_X', hai] using
        (isUnit_one : IsUnit (1 : Γ(X, U.1)))) := by
    apply_fun CommRingCat.ofHom
    · apply Spec.map_injective
      rw [← cancel_mono (Proj.awayι (PolyGrade K (Option σ)) (MvPolynomial.X none)
        (poly_X_mem none) (by decide))]
      rw [hφ, ← U.2.isoSpec_inv_ι, Category.assoc, sectionsMorphism_on k s hs none U.1 hU,
        affine_coordinates_factor]
      rfl
    · exact fun _ _ hh => congrArg CommRingCat.Hom.hom hh
  constructor
  · intro j
    rw [hφ']
    exact evalAway_coordinate kU a none hai j
  · intro c
    rw [hφ']
    exact RingHom.congr_fun (evalAway_constants kU a none hai) c

lemma etale_reindex {A ι ι' : Type} [CommRing A] (k : K →+* A)
    (v : ι → A) (e : ι' ≃ ι) (hv : (MvPolynomial.eval₂Hom k v).Etale) :
    (MvPolynomial.eval₂Hom k (v ∘ e)).Etale := by
  have h := RingHom.Etale.respectsIso.2 (MvPolynomial.eval₂Hom k v)
    (MvPolynomial.renameEquiv K e).toRingEquiv hv
  convert h using 1
  apply MvPolynomial.ringHom_ext
  · intro c; simp
  · intro i; simp

lemma cast_chart_factor (h : X ⟶ Proj (PolyGrade K (Option σ))) (U : X.affineOpens)
    {i j : Option σ} (hij : i = j) (φ : PolyChart (R := K) i →+* Γ(X, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K (Option σ)) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
        U.2.fromSpec ≫ h) :
    Spec.map (CommRingCat.ofHom (hij ▸ φ)) ≫
      Proj.awayι (PolyGrade K (Option σ)) (MvPolynomial.X j) (poly_X_mem j) (by decide) =
        U.2.fromSpec ≫ h := by
  cases hij
  exact hφ

lemma cast_chart_coordinate (U : X.affineOpens)
    {i j : Option σ} (hij : i = j) (φ : PolyChart (R := K) i →+* Γ(X, U.1))
    (l : Option σ) : φ (chartCoordinate i l) = (hij ▸ φ) (chartCoordinate j l) := by
  cases hij
  rfl

theorem exists_centered_etale_ratios [Fintype σ] [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (k : K →+* Γ(X, ⊤)) (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)]
    (hbase : sectionsMorphism k s hs ≫ projectiveToSpec = g)
    (p : X) (hp : p ∉ centeredOpen s) :
    ∃ U : X.affineOpens, p ∈ U.1 ∧
      ∃ hU : U.1 ≤ SectionOpens.isoOpen (s none),
        ∃ i : Fin 2 → σ,
          (MvPolynomial.eval₂Hom (openScalars g U.1)
            (fun j => -affineSectionRatios s U hU (some (i j)))).Etale ∧
          (∀ j : σ, X.basicOpen (affineSectionRatios s U hU (some j)) ≤ centeredOpen s) ∧
          ∀ c : K, U.1.topIso.hom (U.1.ι.appTop (k c)) = openScalars g U.1 c := by
  classical
  have hp₀ := center_mem_distinguished s hs p hp
  obtain ⟨C, hpC, hCU, hcoord⟩ := exists_etale_projective_chart g
    (sectionsMorphism k s hs) hbase none (SectionOpens.isoOpen (s none)) p hp₀
      (by rwa [← sectionsMorphism_preimage k s hs none] at hp₀)
  have : Finite C.κ := C.finite
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
  refine ⟨C.U, hpC, hCU, i, ?_, ?_, ?_⟩
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

end
end MaximalSeshadri.Projective
end


end
end

end OAI
