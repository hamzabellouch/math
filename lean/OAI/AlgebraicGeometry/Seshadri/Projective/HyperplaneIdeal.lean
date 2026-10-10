import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.PolynomialCharts
import OAI.AlgebraicGeometry.Seshadri.Sheaves.CartierModule
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.LinearRadical

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.IdealPullback
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X Y : Scheme} {R : Type} [CommRing R]

lemma vanishingIdeal_comap_open (Z : Closeds Y) (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap f =
      Scheme.IdealSheafData.vanishingIdeal (Z.preimage f.continuous) := by
  let I := (Scheme.IdealSheafData.vanishingIdeal Z).comap f
  have hs : I.support = Z.preimage f.continuous := by
    ext x
    simp only [I, Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rw [← hs, Scheme.IdealSheafData.vanishingIdeal_support]
  symm
  ext U : 2
  rw [Scheme.IdealSheafData.radical_ideal]
  change (I.ideal U).radical = I.ideal U
  rw [show I = (Scheme.IdealSheafData.vanishingIdeal Z).comap f from rfl,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.vanishingIdeal_ideal]
  exact ((PrimeSpectrum.isRadical_vanishingIdeal _).comap _).radical

lemma specIdeal_support (I : Ideal R) :
    ((specIdeal I).support : Set (Spec (.of R))) = PrimeSpectrum.zeroLocus I := by
  rw [specIdeal, Scheme.IdealSheafData.coe_support_ofIdealTop, Spec_zeroLocus]
  congr 1
  change ((I.map (Scheme.ΓSpecIso (.of R)).inv.hom).comap
    (Scheme.ΓSpecIso (.of R)).inv.hom : Set R) = _
  rw [Ideal.comap_map_of_bijective _ (ConcreteCategory.bijective_of_isIso _)]

lemma specIdeal_radical_eq (I : Ideal R) (hI : I.IsRadical) :
    (specIdeal I).radical = specIdeal I := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.IdealSheafData.radical_ideal, specIdeal_top]
  let e : R ≃+* Γ(Spec (.of R), ⊤) :=
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  change (I.map e.toRingHom).radical = I.map e.toRingHom
  have he : I.map e.toRingHom = I.comap e.symm.toRingHom := Ideal.map_comap_of_equiv e
  rw [he]
  exact (hI.comap e.symm.toRingHom).radical

lemma vanishingIdeal_open_chart (D : X.Opens) (f : Spec (.of R) ⟶ X)
    [IsOpenImmersion f] (a : R)
    (hD : f ⁻¹ᵁ D = PrimeSpectrum.basicOpen a)
    (ha : (Ideal.span ({a} : Set R)).IsRadical) :
    (Scheme.IdealSheafData.vanishingIdeal D.compl).comap f =
      specIdeal (Ideal.span {a}) := by
  rw [vanishingIdeal_comap_open]
  have hs : D.compl.preimage f.continuous = (specIdeal (Ideal.span {a})).support := by
    apply SetLike.coe_injective
    rw [specIdeal_support, PrimeSpectrum.zeroLocus_span]
    change f ⁻¹' ((D : Set X)ᶜ) = PrimeSpectrum.zeroLocus {a}
    have h := congrArg (fun U : (Spec (.of R)).Opens => (U : Set (Spec (.of R)))) hD
    change f ⁻¹' (D : Set X) = (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum R)) at h
    rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl] at h
    rw [Set.preimage_compl, h]
    exact compl_compl _
  rw [hs, Scheme.IdealSheafData.vanishingIdeal_support, specIdeal_radical_eq _ ha]

end
end MaximalSeshadri.IdealPullback

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [Field K] [Fintype σ]

lemma chart_linear_equation_radical (t : σ → K) (i : σ) :
    (Ideal.span ({∑ j, chartConstants i (t j) * chartCoordinate i j} :
      Set (PolyChart (R := K) i))).IsRadical := by
  classical
  let a : PolyChart (R := K) i := ∑ j, chartConstants i (t j) * chartCoordinate i j
  let e := polynomialChartEquiv (R := K) i
  have hdeg : (e a).totalDegree ≤ 1 := by
    change (chartToPoly i a).totalDegree ≤ 1
    simp only [a, map_sum, map_mul, chartToPoly_constants, chartToPoly_coordinate]
    apply totalDegree_finsetSum_le
    intro j hj
    split_ifs
    · simp
    · apply (totalDegree_mul _ _).trans
      simp
  have hrad := span_isRadical_of_totalDegree_le_one (e a) hdeg
  have he : (Ideal.span ({e a} : Set (MvPolynomial (ChartVariables i) K))).comap
      e.toRingHom = Ideal.span {a} := by
    rw [← Set.image_singleton, ← Ideal.map_span]
    exact Ideal.comap_map_of_bijective e.toRingHom e.bijective
  rw [← he]
  exact hrad.comap e.toRingHom

def ambientHyperplane (t : σ → K) : (Proj (PolyGrade K σ)).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (Proj.basicOpen (PolyGrade K σ) (linearEquation t)).compl

lemma ambientHyperplane_chart (t : σ → K) (i : σ) :
    (ambientHyperplane t).comap
      (Proj.awayι (PolyGrade K σ) (X i) (poly_X_mem i) (by decide)) =
        IdealPullback.specIdeal (Ideal.span {∑ j, chartConstants i (t j) * chartCoordinate i j}) :=
  IdealPullback.vanishingIdeal_open_chart _ _ _ (hyperplane_chart_preimage t i)
    (chart_linear_equation_radical t i)

end
end MaximalSeshadri.Projective
end


end
end

end OAI
