import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.FourTensorKernel
import OAI.Combinatorics.Chromatic.Shuffle.ColumnTaylor
import OAI.Combinatorics.Chromatic.Shuffle.SeparationHomogeneity
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentScalarNaturality
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentUnitSigns

namespace OAI

namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel
open SeparationInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] cancelTensorRing cancelTensorAlg cancelFourRing cancelFourAlg
attribute [local instance] cancelTensorSelf cancelTensorNonUnital cancelFourNonUnital cancelSeriesRing

noncomputable local instance cellSepTensorSemiring (d e : I → ℕ) : Semiring (S d⊗[ℚ]S e) :=
  (cancelTensorRing d e).toSemiring
noncomputable local instance cellSepTensorNonAssoc (d e : I → ℕ) : NonAssocSemiring (S d⊗[ℚ]S e) :=
  (cancelTensorRing d e).toNonAssocSemiring
noncomputable local instance cellSepFourSemiring (d₁ e₁ d₂ e₂ : I → ℕ) :
    Semiring ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :=
  (cancelFourRing d₁ e₁ d₂ e₂).toSemiring
noncomputable local instance cellSepFourNonAssoc (d₁ e₁ d₂ e₂ : I → ℕ) :
    NonAssocSemiring ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :=
  (cancelFourRing d₁ e₁ d₂ e₂).toNonAssocSemiring
noncomputable local instance cellSepFourModule (d₁ e₁ d₂ e₂ : I → ℕ) :
    Module ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) := Semiring.toModule

noncomputable def fourInputSeries (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) :=
  mapRing (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom (tensorSeparationSeries a d₁ d₂ f) *
    mapRing (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom (tensorSeparationSeries a e₁ e₂ g) *
    (mappedInverseKernel a e₁ d₂ (crossingColumnAlg d₁ e₁ d₂ e₂) *
      (mappedInverseKernel (fun i j=>a j i) e₁ d₂ (crossingColumnAlg d₁ e₁ d₂ e₂))⁻¹).val

lemma fourGrid_relativeTaylor_factor (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    fourRelativeTaylor d₁ e₁ d₂ e₂
      (separateFour d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂))=
    Polynomial.map (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom
      (relativeTaylor d₁ d₂ (restrictTensor (firstCut d₁ d₂) f)) *
    Polynomial.map (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom
      (relativeTaylor e₁ e₂ (restrictTensor (firstCut e₁ e₂) g)) *
    fourRelativeTaylor d₁ e₁ d₂ e₂ (fourCrossTensor a d₁ e₁ d₂ e₂) := by
  rw [separateFour_grid_factor a d₁ e₁ d₂ e₂ (firstCut d₁ d₂) (firstCut e₁ e₂)]
  rw [←fourColumns_product d₁ e₁ d₂ e₂]
  simp only [map_mul,←firstColumn_relativeTaylor,←secondColumn_relativeTaylor]

lemma polynomial_mapped_product {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* T) (g : S →+* T) (p : Polynomial R) (q : Polynomial S) (r : Polynomial T) :
    polynomial (Polynomial.map f p * Polynomial.map g q * r)=
      mapRing f (polynomial p)*mapRing g (polynomial q)*polynomial r := by
  rw [polynomial.map_mul,polynomial.map_mul,←polynomial_map,←polynomial_map]

omit [Fintype I] [DecidableEq I] in
private lemma fourPolynomial_mapped_product_pair (d₁ e₁ d₂ e₂ : I → ℕ)
    (p : Polynomial (S d₁⊗[ℚ]S d₂)) (q : Polynomial (S e₁⊗[ℚ]S e₂)) :
    polynomial (Polynomial.map (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom p *
      Polynomial.map (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom q)=
      mapRing (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom (polynomial p)*
        mapRing (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom (polynomial q) :=
  (polynomial.map_mul _ _).trans
    (congrArg₂ (fun x y => x * y)
      (polynomial_map (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom p).symm
      (polynomial_map (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom q).symm)

omit [Fintype I] [DecidableEq I] in
lemma fourPolynomial_mapped_product (d₁ e₁ d₂ e₂ : I → ℕ)
    (p : Polynomial (S d₁⊗[ℚ]S d₂)) (q : Polynomial (S e₁⊗[ℚ]S e₂))
    (r : Polynomial ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂))) :
    polynomial (Polynomial.map (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom p *
      Polynomial.map (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom q * r)=
      mapRing (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom (polynomial p)*
        mapRing (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom (polynomial q)*polynomial r := by
  calc
    _ = polynomial (Polynomial.map (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom p *
        Polynomial.map (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom q) * polynomial r :=
      polynomial.map_mul _ _
    _ = _ := congrArg (fun t => t * polynomial r)
      (fourPolynomial_mapped_product_pair d₁ e₁ d₂ e₂ p q)

lemma fourGrid_taylor_factor (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂
      (separateFour d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂)))=
    mapRing (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom
      (polynomial (relativeTaylor d₁ d₂ (restrictTensor (firstCut d₁ d₂) f))) *
    mapRing (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom
      (polynomial (relativeTaylor e₁ e₂ (restrictTensor (firstCut e₁ e₂) g))) *
    polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂ (fourCrossTensor a d₁ e₁ d₂ e₂)) := by
  rw [fourGrid_relativeTaylor_factor]
  exact fourPolynomial_mapped_product d₁ e₁ d₂ e₂ _ _ _

lemma negative_unit_word_rat {R : Type*} [CommRing R] [Algebra ℚ R]
    (n : ℤ) (A B D : (LaurentSeries R)ˣ) :
    ((-1)^n*(A*B*D)).val=HahnSeries.C (algebraMap ℚ R ((-1 : ℚ)^n))*(A.val*B.val*D.val) := by
  rw [Units.val_mul,negative_unit_rat,Units.val_mul,Units.val_mul]

lemma fourTensorKernelRHS_scalar (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    (fourTensorKernelRHS a d₁ e₁ d₂ e₂).val=
      HahnSeries.C (algebraMap ℚ ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) ((-1 : ℚ)^eulerForm a d₂ e₁)) *
        ((fourFirstInverseUnit a d₁ e₁ d₂ e₂).val *
          (fourSecondInverseUnit a d₁ e₁ d₂ e₂).val *
          (fourCrossingInverseUnit a d₁ e₁ d₂ e₂ *
            (fourCrossingInverseUnit (fun i j=>a j i) d₁ e₁ d₂ e₂)⁻¹).val) := by
  unfold fourTensorKernelRHS
  rw [Units.val_mul, negative_unit_rat]
  rfl

lemma kernel_product_rearrange {R : Type*} [CommRing R]
    (K L A B C D P Q r : R) (h : K*L*C=r*(A*B*D)) :
    K*L*(P*Q*C)=r*((A*P)*(B*Q)*D) := by
  calc
    _ = (K*L*C)*(P*Q) := by ring
    _ = _ := by rw [h]; ring

omit [Fintype I] [DecidableEq I] in
lemma four_rat_smul_series (d₁ e₁ d₂ e₂ : I → ℕ) (r : ℚ)
    (x : LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂))) :
    r • x=HahnSeries.C (algebraMap ℚ ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) r)*x :=
  @rat_smul_series ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂))
    (cancelFourRing d₁ e₁ d₂ e₂) (cancelFourAlg d₁ e₁ d₂ e₂) r x

lemma firstColumn_tensorSeparationSeries (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S (d₁+d₂)) :
    mapRing (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom (tensorSeparationSeries a d₁ d₂ f)=
      (fourFirstInverseUnit a d₁ e₁ d₂ e₂).val *
        mapRing (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom
          (polynomial (relativeTaylor d₁ d₂ (restrictTensor (firstCut d₁ d₂) f))) :=
  (mapRing (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom).map_mul _ _

lemma secondColumn_tensorSeparationSeries (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (g : S (e₁+e₂)) :
    mapRing (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom (tensorSeparationSeries a e₁ e₂ g)=
      (fourSecondInverseUnit a d₁ e₁ d₂ e₂).val *
        mapRing (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom
          (polynomial (relativeTaylor e₁ e₂ (restrictTensor (firstCut e₁ e₂) g))) :=
  (mapRing (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom).map_mul _ _

lemma fourInputSeries_factor (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    fourInputSeries a d₁ e₁ d₂ e₂ f g=
      ((fourFirstInverseUnit a d₁ e₁ d₂ e₂).val *
        mapRing (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom
          (polynomial (relativeTaylor d₁ d₂ (restrictTensor (firstCut d₁ d₂) f)))) *
      ((fourSecondInverseUnit a d₁ e₁ d₂ e₂).val *
        mapRing (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom
          (polynomial (relativeTaylor e₁ e₂ (restrictTensor (firstCut e₁ e₂) g)))) *
      (fourCrossingInverseUnit a d₁ e₁ d₂ e₂ *
        (fourCrossingInverseUnit (fun i j=>a j i) d₁ e₁ d₂ e₂)⁻¹).val := by
  exact congrArg₂
    (fun x y : LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)) =>
      x * y * (fourCrossingInverseUnit a d₁ e₁ d₂ e₂ *
        (fourCrossingInverseUnit (fun i j=>a j i) d₁ e₁ d₂ e₂)⁻¹).val)
    (firstColumn_tensorSeparationSeries a d₁ e₁ d₂ e₂ f)
    (secondColumn_tensorSeparationSeries a d₁ e₁ d₂ e₂ g)

lemma kernel_product_rearrange_with_factors {R : Type*} [CommRing R]
    (K L A B C D P Q r X Y : R) (h : K*L*C=r*(A*B*D))
    (hX : X=P*Q*C) (hY : Y=(A*P)*(B*Q)*D) : K*L*X=r*Y := by
  rw [hX,hY]
  exact kernel_product_rearrange K L A B C D P Q r h

lemma fourGrid_normalized_algebra (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S (d₁+d₂)) (g : S (e₁+e₂))
    (K L r : LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)))
    (h : K*L*polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂ (fourCrossTensor a d₁ e₁ d₂ e₂))=
      r*((fourFirstInverseUnit a d₁ e₁ d₂ e₂).val *
        (fourSecondInverseUnit a d₁ e₁ d₂ e₂).val *
        (fourCrossingInverseUnit a d₁ e₁ d₂ e₂ *
          (fourCrossingInverseUnit (fun i j=>a j i) d₁ e₁ d₂ e₂)⁻¹).val)) :
    K*L*polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂
      (separateFour d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂)))=
      r*fourInputSeries a d₁ e₁ d₂ e₂ f g :=
  @kernel_product_rearrange_with_factors
    (LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂))) (cancelSeriesRing d₁ e₁ d₂ e₂)
    K L _ _ _ _ _ _ r _ _ h
    (fourGrid_taylor_factor a d₁ e₁ d₂ e₂ f g) (fourInputSeries_factor a d₁ e₁ d₂ e₂ f g)

lemma fourGrid_normalized (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ e₁) (B : Cut d₂ e₂)
    (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    (mappedInverseKernel a (d₁+e₁) (d₂+e₂) (restrictRows d₁ e₁ d₂ e₂ A B)).val *
      ((mappedInverseKernel (fun _ _ : I=>0) (d₁+e₁) (d₂+e₂) (restrictRows d₁ e₁ d₂ e₂ A B))⁻¹).val *
      polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂
        (separateFour d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂)))=
    ((-1 : ℚ)^eulerForm a d₂ e₁) • fourInputSeries a d₁ e₁ d₂ e₂ f g := by
  apply (fourGrid_normalized_algebra a d₁ e₁ d₂ e₂ f g _ _ _
    ((fourTensorKernel_cancellation a d₁ e₁ d₂ e₂ A B).trans
      (fourTensorKernelRHS_scalar a d₁ e₁ d₂ e₂))).trans
  exact (four_rat_smul_series d₁ e₁ d₂ e₂ _ _).symm

end ElementaryPositivity.RawShuffle

end OAI
