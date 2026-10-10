import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Projective.PolynomialCharts

namespace OAI

section
noncomputable section
                                          
section
namespace MaximalSeshadri.BertiniIntegral
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Polynomial
open MaximalSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Polynomial.algebra
attribute [local instance 1100] Polynomial.algebraOfAlgebra

theorem smooth_integral_zero_family_with_equations
    {K α : Type} {n : ℕ} [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
    [Countable α] (X : Scheme.{0}) (g : X ⟶ Spec (CommRingCat.of K))
    (U : α → X.affineOpens) (hcover : ∀ x : X, ∃ j, x ∈ (U j).1)
    [∀ j, IsDomain Γ(X, (U j).1)]
    [∀ j, Algebra K Γ(X, (U j).1)] [∀ j, Algebra.FiniteType K Γ(X, (U j).1)]
    (hOver : ∀ j, Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, (U j).1))) =
      (U j).2.fromSpec ≫ g)
    (σ : α → Type) [∀ j, Algebra (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    [∀ j, IsScalarTower K (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    [∀ j, Algebra.Etale (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    (v : ∀ j, Fin n → Γ(X, (U j).1)) (i₁ i₂ : α → Fin n) (a b : ∀ j, σ j)
    (hab : ∀ j, a j ≠ b j)
    (hva : ∀ j, v j (i₁ j) =
      algebraMap (MvPolynomial (σ j) K) Γ(X, (U j).1) (MvPolynomial.X (a j)))
    (hvb : ∀ j, v j (i₂ j) =
      algebraMap (MvPolynomial (σ j) K) Γ(X, (U j).1) (MvPolynomial.X (b j)))
    (e : α → (Option (Fin n) ≃ Option (Fin n)))
    (D : (Option (Fin n) → K) → X.Opens)
    (hD : ∀ t j, (U j).2.fromSpec ⁻¹ᵁ D t = PrimeSpectrum.basicOpen
      (algebraMap K Γ(X, (U j).1) (t (e j none)) -
        ∑ k, algebraMap K Γ(X, (U j).1) (t (e j (some k))) * v j k))
    (j₀ : α) (overlap : α → α)
    (hleft : ∀ j, (U (overlap j)).1 ≤ (U j₀).1)
    (hright : ∀ j, (U (overlap j)).1 ≤ (U j).1)
    (q : MvPolynomial (Option (Fin n)) K) (hq : q ≠ 0) :
    ∃ t : Option (Fin n) → K, MvPolynomial.aeval t q ≠ 0 ∧
      IsIntegral (Scheme.IdealSheafData.vanishingIdeal (D t).compl).subscheme ∧
      Smooth ((Scheme.IdealSheafData.vanishingIdeal (D t).compl).subschemeι ≫ g) ∧
      ∀ j, (Scheme.IdealSheafData.vanishingIdeal (D t).compl).ideal (U j) =
        Ideal.span {algebraMap K Γ(X, (U j).1) (t (e j none)) -
          ∑ k, algebraMap K Γ(X, (U j).1) (t (e j (some k))) * v j k} := by
  obtain ⟨T, _, hqT, f, hf, hh⟩ := simultaneous_reindexed_smooth_integral_hyperplanes
    (fun j => Γ(X, (U j).1)) σ v i₁ i₂ a b hab hva hvb e
    (q.coeffs : Set K) q.coeffs.countable_toSet
  let t : Option (Fin n) → K := fun o => f (hyperplaneVariable o)
  have hqv : MvPolynomial.aeval t q ≠ 0 := by
    have ht : t = (fun o => o.elim (f Polynomial.X)
        (fun i => f (C (MvPolynomial.X i)))) := by
      funext o
      cases o <;> rfl
    rw [ht]
    exact hyperplane_parameter_polynomial_ne_zero T q hq hqT f hf
  let I := Scheme.IdealSheafData.vanishingIdeal (D t).compl
  have hI (j : α) : I.ideal (U j) = Ideal.span
      {algebraMap K Γ(X, (U j).1) (t (e j none)) -
        ∑ k, algebraMap K Γ(X, (U j).1) (t (e j (some k))) * v j k} := by
    let := (hh j).1
    exact vanishingIdeal_compl_eq_span (D t) (U j) _ (hD t j)
  have hDom (j : α) : IsDomain (Γ(X, (U j).1) ⧸ I.ideal (U j)) := by
    rw [hI]
    exact (hh j).1
  have hS (j : α) : Algebra.Smooth K (Γ(X, (U j).1) ⧸ I.ideal (U j)) := by
    rw [hI]
    exact (hh j).2
  let : ∀ j, IsDomain (Γ(X, (U j).1) ⧸ I.ideal (U j)) := hDom
  let : ∀ j, Algebra.Smooth K (Γ(X, (U j).1) ⧸ I.ideal (U j)) := hS
  exact ⟨t, hqv,
    integral_subscheme_of_affine_overlap_quotients X U hcover I j₀ overlap hleft hright,
    MaximalSeshadri.SchemeBertini.smooth_subscheme_of_affine_quotients
      X g U hcover hOver I, hI⟩

theorem smooth_integral_hyperplane_of_etale_atlas_with_equations
    {K α : Type} {n : ℕ} [Field K] [CharZero K] [IsAlgClosed K] [Uncountable K]
    [Countable α] (X : Scheme.{0}) (g : X ⟶ Spec (CommRingCat.of K))
    (h : X ⟶ Proj (PolyGrade K (Option (Fin n))))
    (hbase : h ≫ projectiveToSpec = g)
    (U : α → X.affineOpens) (hcover : ∀ x : X, ∃ j, x ∈ (U j).1)
    [∀ j, IsDomain Γ(X, (U j).1)]
    [∀ j, Algebra K Γ(X, (U j).1)] [∀ j, Algebra.FiniteType K Γ(X, (U j).1)]
    (hOver : ∀ j, Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, (U j).1))) =
      (U j).2.fromSpec ≫ g)
    (e : α → (Option (Fin n) ≃ Option (Fin n)))
    (φ : ∀ j, PolyChart (R := K) (e j none) →+* Γ(X, (U j).1))
    (hφ : ∀ j, Spec.map (CommRingCat.ofHom (φ j)) ≫
      Proj.awayι (PolyGrade K (Option (Fin n))) (MvPolynomial.X (e j none))
        (poly_X_mem (e j none)) (by decide) = (U j).2.fromSpec ≫ h)
    (σ : α → Type) [∀ j, Algebra (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    [∀ j, IsScalarTower K (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    [∀ j, Algebra.Etale (MvPolynomial (σ j) K) Γ(X, (U j).1)]
    (i₁ i₂ : α → Fin n) (a b : ∀ j, σ j) (hab : ∀ j, a j ≠ b j)
    (hva : ∀ j, -φ j (chartCoordinate (e j none) (e j (some (i₁ j)))) =
      algebraMap (MvPolynomial (σ j) K) Γ(X, (U j).1) (MvPolynomial.X (a j)))
    (hvb : ∀ j, -φ j (chartCoordinate (e j none) (e j (some (i₂ j)))) =
      algebraMap (MvPolynomial (σ j) K) Γ(X, (U j).1) (MvPolynomial.X (b j)))
    (j₀ : α) (overlap : α → α)
    (hleft : ∀ j, (U (overlap j)).1 ≤ (U j₀).1)
    (hright : ∀ j, (U (overlap j)).1 ≤ (U j).1)
    (q : MvPolynomial (Option (Fin n)) K) (hq : q ≠ 0) :
    ∃ t : Option (Fin n) → K, MvPolynomial.aeval t q ≠ 0 ∧
      IsIntegral (projectiveHyperplane h t).subscheme ∧
      Smooth ((projectiveHyperplane h t).subschemeι ≫ g) ∧
      ∀ j, (projectiveHyperplane h t).ideal (U j) =
        Ideal.span {∑ k, φ j (chartConstants (e j none) (t k)) *
          φ j (chartCoordinate (e j none) k)} := by
  obtain ⟨t, ht, hI, hS, heq⟩ := smooth_integral_zero_family_with_equations X g U hcover hOver σ
    (fun j k => -φ j (chartCoordinate (e j none) (e j (some k))))
    i₁ i₂ a b hab hva hvb e
    (fun t => h ⁻¹ᵁ Proj.basicOpen (PolyGrade K (Option (Fin n))) (linearEquation t))
    (fun t j => hyperplane_affine_preimage_reindexed h (U j) (e j) (φ j) (hφ j)
      (projective_affine_constants h g hbase (U j) (hOver j) _ (φ j) (hφ j)) t)
    j₀ overlap hleft hright q hq

  refine ⟨t, ht, hI, hS, fun j => ?_⟩
  unfold projectiveHyperplane
  rw [heq j]
  congr 1
  rw [← (e j).sum_comp]
  simp only [Fintype.sum_option, chartCoordinate_self, map_one, mul_one,
    projective_affine_constants h g hbase (U j) (hOver j) _ (φ j) (hφ j),
    mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]

end
end MaximalSeshadri.BertiniIntegral
end


end
end

end OAI
