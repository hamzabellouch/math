import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Analytic.PointCharts
import OAI.AlgebraicGeometry.Seshadri.Jets.EtaleAnalytic

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.QuadraticJets
noncomputable section
open MvPolynomial MaximalSeshadri.AlgebraicJets
open scoped Topology

lemma polynomial_binary_standardSmooth :
    Algebra.IsStandardSmoothOfRelativeDimension 2 ℂ (MvPolynomial (Fin 2) ℂ) := by
  let b := KaehlerDifferential.mvPolynomialBasis ℂ (Fin 2)
  have : Algebra.IsStandardSmooth ℂ (MvPolynomial (Fin 2) ℂ) :=
    Algebra.IsStandardSmooth.of_basis_kaehlerDifferential b (by
      rintro _ ⟨i,rfl⟩
      exact ⟨X i, (KaehlerDifferential.mvPolynomialBasis_apply ℂ (Fin 2) i).symm⟩)
  rw [Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth]
  rw [rank_eq_card_basis b]
  simp

variable {A : Type} [CommRing A] [Algebra ℂ A]
  [Algebra (MvPolynomial (Fin 2) ℂ) A] [IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) A]
  [Algebra.Etale (MvPolynomial (Fin 2) ℂ) A]

theorem exists_etale_analytic_chart
    (ρ : A →ₐ[ℂ] ℂ)
    (hρ : ∀ i : Fin 2, ρ (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i)) = 0) :
    ∃ q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ), q 0 = ρ ∧
      (∀ s : A, AnalyticAt ℂ (fun z => q z s) 0) ∧
      ∀ᶠ z in 𝓝 0, ∀ i : Fin 2,
        q z (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i)) =
          if i = 0 then z.2 else z.1 := by
  classical
  have : Algebra.IsStandardSmoothOfRelativeDimension 2 ℂ (MvPolynomial (Fin 2) ℂ) :=
    polynomial_binary_standardSmooth
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (Fin 2) ℂ) A :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp inferInstance
  have : Algebra.IsStandardSmoothOfRelativeDimension 2 ℂ A :=
    Algebra.IsStandardSmoothOfRelativeDimension.trans 2 0 ℂ (MvPolynomial (Fin 2) ℂ) A
  obtain ⟨ι,σ,hσ,hι,P,hP⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.out (n := 2) (R := ℂ) (S := A)
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype σ := Fintype.ofFinite σ
  have hcard : Fintype.card {i : ι // i ∉ Set.range P.map} = 2 := by
    rw [← hP]
    change Fintype.card ((Set.range P.map)ᶜ : Set ι) = P.dimension
    simp only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card,
      Fintype.card_compl_set, Set.card_range_of_injective P.map_inj]
  let e : {i : ι // i ∉ Set.range P.map} ≃ Fin 2 :=
    Fintype.equivFinOfCardEq hcard
  obtain ⟨q,hq₀,hq,hcoord⟩ := exists_binary_point_chart P e ρ
  have hu : ∀ᶠ z in 𝓝 0, q z (P.val (e.symm 1)) = ρ (P.val (e.symm 1)) + z.1 := by
    filter_upwards [hcoord] with z hz
    simpa using hz 1
  have hw : ∀ᶠ z in 𝓝 0, q z (P.val (e.symm 0)) = ρ (P.val (e.symm 0)) + z.2 := by
    filter_upwards [hcoord] with z hz
    simpa using hz 0
  obtain ⟨ψ,hψ₀,hψ,hψcoord,-,-⟩ :=
    etale_coordinates_analytic_inverse ρ hρ q hq₀ hq _ _ hu hw
  refine ⟨fun z => q (ψ z), by simp [hψ₀,hq₀], ?_, hψcoord⟩
  intro s
  exact (hq s).comp_of_eq hψ hψ₀
end
end MaximalSeshadri.QuadraticJets
end


end
end

end OAI
