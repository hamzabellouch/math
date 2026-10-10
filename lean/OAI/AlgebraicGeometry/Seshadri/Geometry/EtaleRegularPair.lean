import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.ProjectiveRefinement
import OAI.AlgebraicGeometry.Seshadri.Divisors.CenteredSections
import OAI.AlgebraicGeometry.Seshadri.Projective.QuarticSubsystem

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.ProjectiveBertini
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Projective MaximalSeshadri.BertiniIntegral MaximalSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

lemma basicOpen_neg {X : Scheme} {U : X.Opens} (r : Γ(X, U)) :
    X.basicOpen (-r) = X.basicOpen r := by
  apply SetLike.ext
  intro x
  rw [Scheme.mem_basicOpen'', Scheme.mem_basicOpen'']
  simp only [map_neg, IsUnit.neg_iff]

lemma etale_coordinates_regular_pair {K A ι : Type} [Field K] [CommRing A]
    (k : K →+* A) (v : ι → A) (hv : (MvPolynomial.eval₂Hom k v).Etale)
    (i j : ι) (hij : i ≠ j) :
    IsSMulRegular A (v i) ∧ ∀ a : A, v i ∣ v j * a → v i ∣ a := by
  let : Algebra (MvPolynomial ι K) A := (MvPolynomial.eval₂Hom k v).toAlgebra
  let : Algebra.Etale (MvPolynomial ι K) A := hv
  let : Module.Flat (MvPolynomial ι K) A := inferInstance
  have hab : ∀ p : MvPolynomial ι K,
      MvPolynomial.X i ∣ MvPolynomial.X j * p → MvPolynomial.X i ∣ p := by
    intro p hp
    exact (MvPolynomial.X_dvd_mul_iff.mp hp).resolve_left (by simpa using hij)
  have h := flat_regular_pair (S := A) (MvPolynomial.X i) (MvPolynomial.X j)
    (show IsSMulRegular (MvPolynomial ι K) (MvPolynomial.X i) from
      MvPolynomial.isRegular_X.left) hab
  simpa only [RingHom.algebraMap_toAlgebra, MvPolynomial.eval₂Hom_X'] using h

lemma sectionsMorphism_coordinate_preimage {K σ : Type} [Field K] [Fintype σ]
    {X : Scheme} {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : Option σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (U : X.affineOpens) (i j : Option σ)
    (φ : PolyChart (R := K) i →+* Γ(X, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K (Option σ)) (MvPolynomial.X i)
        (poly_X_mem i) (by decide) = U.2.fromSpec ≫ sectionsMorphism k s hs) :
    U.2.fromSpec ⁻¹ᵁ SectionOpens.isoOpen (s j) =
      PrimeSpectrum.basicOpen (φ (chartCoordinate i j)) := by
  classical
  have h := hyperplane_affine_preimage (sectionsMorphism k s hs) U i φ hφ (Pi.single j 1)
  rw [linearEquation_single, MvPolynomial.C_1, one_mul, sectionsMorphism_preimage] at h
  convert h using 1
  simp [Pi.single_apply]

lemma chart_coordinate_basicOpen_le {K σ : Type} [Field K] [Fintype σ]
    {X : Scheme} {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : Option σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (U : X.affineOpens) (i j : Option σ)
    (φ : PolyChart (R := K) i →+* Γ(X, U.1))
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (PolyGrade K (Option σ)) (MvPolynomial.X i)
        (poly_X_mem i) (by decide) = U.2.fromSpec ≫ sectionsMorphism k s hs) :
    X.basicOpen (φ (chartCoordinate i j)) ≤ SectionOpens.isoOpen (s j) := by
  intro x hx
  have hxU := (X.basicOpen_le (φ (chartCoordinate i j))) hx
  obtain ⟨p, rfl⟩ := (U.2.range_fromSpec ▸ hxU : x ∈ Set.range U.2.fromSpec)
  have hp : p ∈ PrimeSpectrum.basicOpen (φ (chartCoordinate i j)) := by
    rwa [← U.2.fromSpec_preimage_basicOpen]
  rwa [← sectionsMorphism_coordinate_preimage k s hs U i j φ hφ] at hp

theorem exists_centered_regular_pair {K σ : Type} [Field K] [Fintype σ]
    {X : Scheme} [IsIntegral X] {M : X.Modules}
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (k : K →+* Γ(X, ⊤)) (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)]
    (hbase : sectionsMorphism k s hs ≫ projectiveToSpec = g)
    (p : X) (hp : p ∈ SectionOpens.isoOpen (s none)) :
    ∃ U : X.affineOpens, p ∈ U.1 ∧ U.1 ≤ SectionOpens.isoOpen (s none) ∧
      ∃ x y : Γ(X, U.1), x ≠ 0 ∧
        (∀ a : Γ(X, U.1), x ∣ y * a → x ∣ a) ∧
        X.basicOpen x ≤ centeredOpen s ∧ X.basicOpen y ≤ centeredOpen s := by
  classical
  obtain ⟨C, hpC, hCU, hcoord⟩ := exists_etale_projective_chart g
    (sectionsMorphism k s hs) hbase none (SectionOpens.isoOpen (s none)) p hp
      (by rwa [← sectionsMorphism_preimage k s hs none] at hp)
  let : Nonempty C.U.1 := C.nonempty
  let : Finite C.κ := C.finite
  let : Fintype C.κ := Fintype.ofFinite _
  have hcard : Fintype.card C.κ = 2 := by rw [← Nat.card_eq_fintype_card]; exact C.card
  let : Nontrivial C.κ := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨i, j, hij⟩ := exists_pair_ne C.κ
  have hr := etale_coordinates_regular_pair (openScalars g C.U.1)
    (fun a => -C.φ (chartCoordinate C.coord (C.a a).1)) C.etale i j hij
  refine ⟨C.U, hpC, hCU, _, _, ?_, hr.2, ?_, ?_⟩
  · intro hz
    apply one_ne_zero (α := Γ(X, C.U.1))
    apply hr.1
    simp only [hz, smul_eq_mul, zero_mul]
  · rw [basicOpen_neg]
    have hc := (chart_coordinate_basicOpen_le k s hs C.U C.coord (C.a i).1 C.φ C.factor)
    apply hc.trans
    have hne : (C.a i).1 ≠ none := by simpa only [hcoord] using (C.a i).2
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hne
    rw [ha]
    exact le_iSup (fun a => SectionOpens.isoOpen (s (some a))) a
  · rw [basicOpen_neg]
    have hc := (chart_coordinate_basicOpen_le k s hs C.U C.coord (C.a j).1 C.φ C.factor)
    apply hc.trans
    have hne : (C.a j).1 ≠ none := by simpa only [hcoord] using (C.a j).2
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hne
    rw [ha]
    exact le_iSup (fun a => SectionOpens.isoOpen (s (some a))) a

end
end MaximalSeshadri.ProjectiveBertini
end


end
end

end OAI
