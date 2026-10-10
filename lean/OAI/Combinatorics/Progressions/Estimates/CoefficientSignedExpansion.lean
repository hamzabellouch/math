import OAI.Combinatorics.Progressions.Polynomial.CoefficientPolynomialIdentity

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

noncomputable def signedExpansionCoefficients {F A : Type*} (c : F → ℂ) (a : A → ℂ) : F ⊕ A → ℂ :=
  Sum.elim c (fun t => -a t)

theorem signedExpansion_sum {F A : Type*} [Fintype F] [Fintype A]
    (c : F → ℂ) (a : A → ℂ) (f : F → ℂ) (g : A → ℂ) :
    (∑ t : F ⊕ A, signedExpansionCoefficients c a t * Sum.elim f g t) =
      (∑ t, c t * f t) - ∑ t, a t * g t := by
  simp only [Fintype.sum_sum_type, signedExpansionCoefficients, Sum.elim_inl, Sum.elim_inr,
    neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem signedExpansion_mass {F A : Type*} [Fintype F] [Fintype A]
    (c : F → ℂ) (a : A → ℂ) :
    (∑ t : F ⊕ A, ‖signedExpansionCoefficients c a t‖) =
      (∑ t, ‖c t‖) + ∑ t, ‖a t‖ := by
  simp only [Fintype.sum_sum_type, signedExpansionCoefficients, Sum.elim_inl, Sum.elim_inr, norm_neg]

end Erdos3.VectorPolynomial

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped BigOperators Classical

theorem coefficient_polynomial_difference_approximation
    {m q : ℕ} {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (rows : ∀ j, O j → Finset (Fin q))
    (d D : ℕ) (hD : 0 < D) (hd : d ∣ D)
    {F A : Type*} [Fintype F] [Fintype A]
    (period : A → ℕ) (hperiod : ∀ t, period t ∣ D)
    (c : F → ℂ) (a : A → ℂ)
    (f : F → (CoefficientAmbientIndex (Fin q) J → UnitAddCircle) → ℂ)
    (g : A → (CoefficientAmbientIndex (Fin q) J → UnitAddCircle) → ℂ)
    (density model : EuclideanJetLayers U O → ℂ) {δ : ℝ}
    (happrox : ∀ z : CoefficientTorus (K := Fin q) U,
      ‖density (euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ) rows z) -
        ∑ t, c t * f t (coefficientAmbientTorus U z)‖ ≤ δ)
    (hmodel : ∀ (p : ∀ j, VectorPolynomial (Fin q) ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : Fin q → ℕ) (j.val + 1) (p j))
      (hm : ∀ j e, coefficients (p j) e ∈ U j) (v : Fin q → (Unit ⊕ Fin q) → ℤ),
      model (physicalCubeRowSample U d rows p hm v) =
        ∑ t, a t * g t (coefficientAmbientTorus U (affineCoefficientCoverSample U p hm (period t)
          (fun k x => (standardPhysicalCubeFrame v (k,x) : ℝ))))) :
    ∀ z : CoefficientTorus (K := Fin q) U,
      let y := euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ) rows
        (quotientIntegerCover (coefficientIntegerLattice U) (D / d) z)
      ‖(density y - model y) -
        ∑ t : F ⊕ A, signedExpansionCoefficients c a t *
          Sum.elim f g t ((D / Sum.elim (fun _ => d) period t) • coefficientAmbientTorus U z)‖ ≤ δ := by
  intro z y
  have hm := coefficient_polynomial_identity_transfer U rows d D hD hd period hperiod a g model hmodel z
  change model y = _ at hm
  have ha := happrox (quotientIntegerCover (coefficientIntegerLattice U) (D / d) z)
  rw [coefficientAmbientTorus_cover] at ha
  change ‖density y - _‖ ≤ δ at ha
  have hs : (∑ t : F ⊕ A, signedExpansionCoefficients c a t *
      Sum.elim f g t ((D / Sum.elim (fun _ => d) period t) • coefficientAmbientTorus U z)) =
      (∑ t, c t * f t ((D / d) • coefficientAmbientTorus U z)) - model y := by
    rw [hm]
    simp only [Fintype.sum_sum_type, signedExpansionCoefficients, Sum.elim_inl, Sum.elim_inr,
      neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  rw [hs]
  convert ha using 1
  congr 1
  ring

theorem coefficient_physical_difference_approximation
    {X : Type*} {m q : ℕ} {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (rows : ∀ j, O j → Finset (Fin q)) (d : ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    {F A : Type*} [Fintype F] [Fintype A] (period : A → ℕ)
    (c : F → ℂ) (a : A → ℂ)
    (f : F → (CoefficientAmbientIndex (Fin q) J → UnitAddCircle) → ℂ)
    (g : A → (CoefficientAmbientIndex (Fin q) J → UnitAddCircle) → ℂ)
    (density model : EuclideanJetLayers U O → ℂ) {δ : ℝ}
    (happrox : ∀ z : CoefficientTorus (K := Fin q) U,
      ‖density (euclideanCoefficientJetMap U (fun _ => 0) (1 : Matrix (Fin q) (Fin q) ℤ) rows z) -
        ∑ t, c t * f t (coefficientAmbientTorus U z)‖ ≤ δ)
    (hmodel : ∀ v : X → (Unit ⊕ Fin q) → ℤ,
      model (physicalCubeRowSample U d rows p hm v) =
        ∑ t, a t * g t (coefficientAmbientTorus U (affineCoefficientCoverSample U p hm (period t)
          (fun k x => (standardPhysicalCubeFrame v (k,x) : ℝ)))))
    (v : X → (Unit ⊕ Fin q) → ℤ) :
    let y := physicalCubeRowSample U d rows p hm v
    ‖(density y - model y) -
      ∑ t : F ⊕ A, signedExpansionCoefficients c a t *
        Sum.elim f g t (coefficientAmbientTorus U (affineCoefficientCoverSample U p hm
          (Sum.elim (fun _ => d) period t) (fun k x => (standardPhysicalCubeFrame v (k,x) : ℝ))))‖ ≤ δ := by
  intro y
  have ha := happrox (affineCoefficientCoverSample U p hm d
    (fun k x => (standardPhysicalCubeFrame v (k,x) : ℝ)))
  rw [coefficientCoverSample_physicalRows U d p hp hm] at ha
  change ‖density y - _‖ ≤ δ at ha
  have hs : (∑ t : F ⊕ A, signedExpansionCoefficients c a t *
      Sum.elim f g t (coefficientAmbientTorus U (affineCoefficientCoverSample U p hm
        (Sum.elim (fun _ => d) period t) (fun k x => (standardPhysicalCubeFrame v (k,x) : ℝ))))) =
      (∑ t, c t * f t (coefficientAmbientTorus U (affineCoefficientCoverSample U p hm d
        (fun k x => (standardPhysicalCubeFrame v (k,x) : ℝ))))) - model y := by
    rw [hmodel v]
    simp only [Fintype.sum_sum_type, signedExpansionCoefficients, Sum.elim_inl, Sum.elim_inr,
      neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  rw [hs]
  convert ha using 1
  congr 1
  ring

end Erdos3.BooleanCubeKernel

end

end OAI
