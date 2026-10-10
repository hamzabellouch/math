import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.PolynomialCharts

namespace OAI

/-! Curve Coordinates. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
lemma exists_uniform_pow_mul_integer_of_integral_inverse
    {k B K ι : Type*} [CommRing k] [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Field K] [Algebra B K] [IsFractionRing B K] [Fintype ι]
    (c : k →+* B) (s : B) (hs : s ≠ 0) (x : ι → K)
    (hx : ∀ i, (Polynomial.eval₂RingHom ((algebraMap B K).comp c)
      (algebraMap B K s)⁻¹).IsIntegralElem (x i)) :
    ∃ n : ℕ, ∀ d : ℕ, n ≤ d → ∃ b : ι → B,
      ∀ i, algebraMap B K (b i) = (algebraMap B K s)^d * x i := by
  classical
  choose n b hb using fun i => exists_pow_mul_integer_of_integral_inverse c s hs (x i) (hx i)
  refine ⟨∑ i, n i, fun d hd => ?_⟩
  refine ⟨fun i => s^(d-n i) * b i, fun i => ?_⟩
  have hni : n i ≤ d := (Finset.single_le_sum (fun j _ => Nat.zero_le (n j))
    (Finset.mem_univ i)).trans hd
  rw [map_mul, map_pow, hb i, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hni]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable def PolynomialCurveChart.scalar {C : Scheme} [IsIntegral C]
    {sC : C ⟶ Spec (.of ℂ)} {a : C.functionField} (A : PolynomialCurveChart sC a) :
    ℂ →+* Γ(C,A.U) := A.poly.comp Polynomial.C
noncomputable def PolynomialCurveChart.germ {C : Scheme} [IsIntegral C]
    {sC : C ⟶ Spec (.of ℂ)} {a : C.functionField} (A : PolynomialCurveChart sC a) :
    Γ(C,A.U) →+* C.functionField := (C.presheaf.germ A.U (genericPoint C) A.generic_mem).hom
lemma PolynomialCurveChart.germ_scalar {C : Scheme} [IsIntegral C]
    {sC : C ⟶ Spec (.of ℂ)} {a : C.functionField} (A : PolynomialCurveChart sC a) :
    A.germ.comp A.scalar = curveFieldScalar sC := by
  apply RingHom.ext
  intro c
  have h := RingHom.congr_fun A.germ_poly (Polynomial.C c)
  simpa only [germ, scalar, RingHom.comp_apply, curveFunctionPolynomial,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C] using h
lemma PolynomialCurveChart.germ_X {C : Scheme} [IsIntegral C]
    {sC : C ⟶ Spec (.of ℂ)} {a : C.functionField} (A : PolynomialCurveChart sC a) :
    A.germ (A.poly Polynomial.X) = a := by
  have h := RingHom.congr_fun A.germ_poly Polynomial.X
  simpa only [germ, RingHom.comp_apply, curveFunctionPolynomial,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using h
lemma PolynomialCurveChart.generators {C : Scheme} [IsIntegral C]
    {sC : C ⟶ Spec (.of ℂ)} {a : C.functionField} (A : PolynomialCurveChart sC a) :
    ∃ m : ℕ, ∃ x : Fin m → Γ(C,A.U), Function.Surjective (MvPolynomial.eval₂Hom A.scalar x) := by
  let : Algebra ℂ Γ(C,A.U) := A.scalar.toAlgebra
  have hC : (Polynomial.C : ℂ →+* Polynomial ℂ).FiniteType :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  let : Algebra.FiniteType ℂ Γ(C,A.U) := A.finite.finiteType.comp hC
  obtain ⟨m,f,hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType ℂ Γ(C,A.U))
  refine ⟨m, fun i => f (MvPolynomial.X i), ?_⟩
  have he : MvPolynomial.eval₂Hom A.scalar (fun i => f (MvPolynomial.X i)) = f.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [MvPolynomial.eval₂Hom_C]
      change (algebraMap ℂ Γ(C,A.U)) c = f ((algebraMap ℂ (MvPolynomial (Fin m) ℂ)) c)
      exact (f.commutes c).symm
    · intro i
      simp
  rw [he]
  exact hf
lemma nonconstant_inv {K : Type*} [Field K] (c : ℂ →+* K) {a : K}
    (ha : a ∉ Set.range c) : a⁻¹ ∉ Set.range c := by
  rintro ⟨b,hb⟩
  apply ha
  refine ⟨b⁻¹, ?_⟩
  rw [map_inv₀, hb, inv_inv]
lemma PolynomialCurveChart.clear {C : Scheme} [IsIntegral C]
    {sC : C ⟶ Spec (.of ℂ)} [SmoothOfRelativeDimension 1 sC]
    {a : C.functionField} (ha : a ≠ 0) (A : PolynomialCurveChart sC a)
    (B : PolynomialCurveChart sC a⁻¹) {ι : Type*} [Fintype ι] (x : ι → Γ(C,A.U)) :
    ∃ n : ℕ, ∀ d : ℕ, n ≤ d → ∃ b : ι → Γ(C,B.U),
      ∀ i, B.germ (b i) = (a⁻¹)^d * A.germ (x i) := by
  let : Nonempty A.U := ⟨⟨genericPoint C,A.generic_mem⟩⟩
  let : Nonempty B.U := ⟨⟨genericPoint C,B.generic_mem⟩⟩
  let : IsFractionRing Γ(C,B.U) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C B.U B.affine
  let : IsIntegrallyClosed Γ(C,B.U) := B.normal sC a⁻¹
  have hb0 : B.poly Polynomial.X ≠ 0 := by
    intro he
    have hh := B.germ_X
    rw [he,map_zero] at hh
    exact (inv_ne_zero ha) hh.symm
  have he : Polynomial.eval₂RingHom
      ((algebraMap Γ(C,B.U) C.functionField).comp B.scalar)
      (algebraMap Γ(C,B.U) C.functionField (B.poly Polynomial.X))⁻¹ =
      A.germ.comp A.poly := by
    change Polynomial.eval₂RingHom (B.germ.comp B.scalar) (B.germ (B.poly Polynomial.X))⁻¹ = _
    rw [B.germ_scalar,B.germ_X,inv_inv]
    exact A.germ_poly.symm
  obtain ⟨n,hn⟩ := exists_uniform_pow_mul_integer_of_integral_inverse B.scalar
    (B.poly Polynomial.X) hb0 (fun i => A.germ (x i)) (fun i => by
      rw [he]
      exact (A.finite.to_isIntegral (x i)).map A.germ)
  refine ⟨n, fun d hd => ?_⟩
  obtain ⟨b,hb⟩ := hn d hd
  refine ⟨b, fun i => ?_⟩
  have hbi := hb i
  change B.germ (b i) = B.germ (B.poly Polynomial.X)^d * A.germ (x i) at hbi
  simpa only [B.germ_X] using hbi
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory TopologicalSpace
lemma polynomial_eval_surjective_of_contains {k R σ τ : Type*} [CommRing k] [CommRing R]
    (c : k →+* R) (x : σ → R) (y : τ → R) (l : τ → σ)
    (hl : x ∘ l = y) (h : Function.Surjective (MvPolynomial.eval₂Hom c y)) :
    Function.Surjective (MvPolynomial.eval₂Hom c x) := by
  intro b
  obtain ⟨p,hp⟩ := h b
  refine ⟨MvPolynomial.rename l p,?_⟩
  rw [MvPolynomial.eval₂Hom_rename,hl,hp]
lemma PolynomialCurveChart.clear_reciprocal {C : Scheme} [IsIntegral C]
    {sC : C ⟶ Spec (.of ℂ)} [SmoothOfRelativeDimension 1 sC]
    {a b : C.functionField} (ha : a ≠ 0) (hb : b = a⁻¹)
    (A : PolynomialCurveChart sC a) (B : PolynomialCurveChart sC b)
    {ι : Type*} [Fintype ι] (x : ι → Γ(C,A.U)) :
    ∃ n : ℕ, ∀ d : ℕ, n ≤ d → ∃ y : ι → Γ(C,B.U),
      ∀ i, B.germ (y i) = b^d * A.germ (x i) := by
  subst b
  exact PolynomialCurveChart.clear ha A B x
structure ProjectiveCurveCoordinates {C : Scheme} [IsIntegral C]
    {sC : C ⟶ Spec (.of ℂ)} {a : C.functionField}
    (A : PolynomialCurveChart sC a) (B : PolynomialCurveChart sC a⁻¹) where
  N : ℕ
  d : ℕ
  positive : 0 < d
  i : Fin (N+1)
  j : Fin (N+1)
  x : Fin (N+1) → Γ(C,A.U)
  y : Fin (N+1) → Γ(C,B.U)
  xi : x i = 1
  yj : y j = 1
  xj : x j = (A.poly Polynomial.X)^d
  yi : y i = (B.poly Polynomial.X)^d
  compatible : ∀ k, B.germ (y k) = (a⁻¹)^d * A.germ (x k)
  surjective_x : Function.Surjective (MvPolynomial.eval₂Hom A.scalar x)
  surjective_y : Function.Surjective (MvPolynomial.eval₂Hom B.scalar y)
lemma exists_projectiveCurveCoordinates {C : Scheme} [IsIntegral C]
    {sC : C ⟶ Spec (.of ℂ)} [SmoothOfRelativeDimension 1 sC]
    {a : C.functionField} (ha : a ≠ 0)
    (A : PolynomialCurveChart sC a) (B : PolynomialCurveChart sC a⁻¹) :
    Nonempty (ProjectiveCurveCoordinates A B) := by
  obtain ⟨m,xa,hxa⟩ := A.generators
  obtain ⟨n,xb,hxb⟩ := B.generators
  obtain ⟨na,hna⟩ := PolynomialCurveChart.clear ha A B xa
  have hclear := PolynomialCurveChart.clear_reciprocal (inv_ne_zero ha) (inv_inv a).symm B A xb
  obtain ⟨nb,hnb⟩ := hclear
  let d := na+nb+1
  obtain ⟨ya,hya⟩ := hna d (by omega)
  obtain ⟨yb,hyb⟩ := hnb d (by omega)
  let x : Fin (m+n+1+1) → Γ(C,A.U) := Fin.snoc (Fin.snoc (Fin.append xa yb) ((A.poly Polynomial.X)^d)) 1
  let y : Fin (m+n+1+1) → Γ(C,B.U) := Fin.snoc (Fin.snoc (Fin.append ya xb) 1) ((B.poly Polynomial.X)^d)
  let i : Fin (m+n+1+1) := Fin.last (m+n+1)
  let j : Fin (m+n+1+1) := (Fin.last (m+n)).castSucc
  refine ⟨⟨m+n+1,d,by omega,i,j,x,y,by simp [x,i],by simp [y,j],
    by simp [x,j],by simp [y,i],?_,?_,?_⟩⟩
  · intro k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simp [x,y,map_pow,B.germ_X]
    · refine Fin.lastCases ?_ (fun k => ?_) k
      · simp only [x,y,Fin.snoc_castSucc,Fin.snoc_last,map_one,map_pow,A.germ_X]
        rw [← mul_pow,inv_mul_cancel₀ ha,one_pow]
      · simp only [x,y,Fin.snoc_castSucc]
        refine Fin.addCases (fun k => ?_) (fun k => ?_) k
        · simpa only [Fin.append_left] using hya k
        · simp only [Fin.append_right]
          rw [hyb k,← mul_assoc,← mul_pow,inv_mul_cancel₀ ha,one_pow,one_mul]
  · apply polynomial_eval_surjective_of_contains A.scalar x xa
      (fun k => ((Fin.castAdd n k).castSucc).castSucc) ?_ hxa
    funext k
    simp only [Function.comp_apply,x,Fin.snoc_castSucc,Fin.append_left]
  · apply polynomial_eval_surjective_of_contains B.scalar y xb
      (fun k => ((Fin.natAdd m k).castSucc).castSucc) ?_ hxb
    funext k
    simp only [Function.comp_apply,y,Fin.snoc_castSucc,Fin.append_right]
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
variable {σ k R : Type*} [CommRing k] [CommRing R]
noncomputable def projectiveChartRingHom (c : k →+* R) (x : σ → R)
    (i : σ) (hi : x i = 1) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule σ k)
      (MvPolynomial.X i) →+* R :=
  (Localization.awayLift (MvPolynomial.eval₂Hom c x) (MvPolynomial.X i)
    (by simpa only [MvPolynomial.eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))).comp
      (algebraMap _ (Localization.Away (MvPolynomial.X i : MvPolynomial σ k)))
noncomputable def projectiveChartRatio (i j : σ) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule σ k)
      (MvPolynomial.X i) :=
  HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X k i)
    1 (MvPolynomial.X j) (by simpa using MvPolynomial.isHomogeneous_X k j)
lemma projectiveChartRingHom_mk (c : k →+* R) (x : σ → R)
    (i : σ) (hi : x i = 1) (n : ℕ) (p : MvPolynomial σ k)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule σ k (n • 1)) :
    projectiveChartRingHom c x i hi (HomogeneousLocalization.Away.mk _
      (MvPolynomial.isHomogeneous_X k i) n p hp) = MvPolynomial.eval₂Hom c x p := by
  change (Localization.awayLift (MvPolynomial.eval₂Hom c x) (MvPolynomial.X i)
    (by simpa only [MvPolynomial.eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R))))
    (Localization.mk p ⟨MvPolynomial.X i ^ n, n, rfl⟩) = _
  simpa using Localization.awayLift_mk (MvPolynomial.eval₂Hom c x)
    (MvPolynomial.X i) p 1 (by simp only [MvPolynomial.eval₂Hom_X', hi, mul_one]) n
lemma projectiveChartRingHom_ratio (c : k →+* R) (x : σ → R)
    (i : σ) (hi : x i = 1) (j : σ) :
    projectiveChartRingHom c x i hi (projectiveChartRatio (k := k) i j) = x j := by
  rw [projectiveChartRatio, projectiveChartRingHom_mk]
  exact MvPolynomial.eval₂Hom_X' _ _ _
lemma projectiveChartRingHom_constants (c : k →+* R) (x : σ → R)
    (i : σ) (hi : x i = 1) (a : k) :
    projectiveChartRingHom c x i hi
      (HomogeneousLocalization.fromZeroRingHom (MvPolynomial.homogeneousSubmodule σ k) _
        ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C _ a⟩) = c a := by
  exact (projectiveChartRingHom_mk c x i hi 0 (MvPolynomial.C a)
    (by exact MvPolynomial.isHomogeneous_C σ a)).trans (MvPolynomial.eval₂Hom_C c x a)
lemma projectiveChartRingHom_surjective (c : k →+* R) (x : σ → R)
    (i : σ) (hi : x i = 1)
    (h : Function.Surjective (MvPolynomial.eval₂Hom c x)) :
    Function.Surjective (projectiveChartRingHom c x i hi) := by
  intro a
  obtain ⟨p,rfl⟩ := h a
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨HomogeneousLocalization.fromZeroRingHom _ _
      ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C _ a⟩,
      (projectiveChartRingHom_constants c x i hi a).trans
        (MvPolynomial.eval₂Hom_C c x a).symm⟩
  | add p q hp hq =>
    obtain ⟨p',hp'⟩ := hp
    obtain ⟨q',hq'⟩ := hq
    exact ⟨p' + q', by simp only [map_add, hp', hq']⟩
  | mul_X p j hp =>
    obtain ⟨p',hp'⟩ := hp
    exact ⟨p' * projectiveChartRatio i j, by
      simp only [map_mul, hp', projectiveChartRingHom_ratio, MvPolynomial.eval₂Hom_X']⟩
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type} [CommRing R] {N : ℕ}
lemma projectiveVariable_mem {N : ℕ} (i : Fin (N+1)) :
    MvPolynomial.X i ∈ MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ 1 :=
  MvPolynomial.isHomogeneous_X ℂ i
noncomputable def projectiveAffineMap (c : ℂ →+* R) (x : Fin (N+1) → R)
    (i : Fin (N+1)) (hi : x i = 1) : Spec (.of R) ⟶ complexProjectiveSpace N :=
  Spec.map (CommRingCat.ofHom (projectiveChartRingHom c x i hi)) ≫
    Proj.awayι _ (MvPolynomial.X i) (projectiveVariable_mem i) (by decide : 0 < 1)
lemma projectiveAffineMap_over (c : ℂ →+* R) (x : Fin (N+1) → R)
    (i : Fin (N+1)) (hi : x i = 1) :
    projectiveAffineMap c x i hi ≫ complexProjectiveSpaceMap N = Spec.map (CommRingCat.ofHom c) := by
  change (Spec.map _ ≫ Proj.awayι _ _ _ _) ≫
    Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom (projectiveConstants N)) = _
  rw [Category.assoc, ← Category.assoc (Proj.awayι _ _ _ _), Proj.awayι_toSpecZero,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact projectiveChartRingHom_constants c x i hi a
lemma projectiveAffineMap_preimage (c : ℂ →+* R) (x : Fin (N+1) → R)
    (i : Fin (N+1)) (hi : x i = 1) (j : Fin (N+1)) :
    projectiveAffineMap c x i hi ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ) (MvPolynomial.X j) =
        PrimeSpectrum.basicOpen (x j) := by
  change (Spec.map (CommRingCat.ofHom (projectiveChartRingHom c x i hi)) ≫
    Proj.awayι _ (MvPolynomial.X i) (projectiveVariable_mem i) (by decide : 0 < 1)) ⁻¹ᵁ
    Proj.basicOpen _ (MvPolynomial.X j) = _
  rw [Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen _ (projectiveVariable_mem i) (by decide : 0 < 1)
      (projectiveVariable_mem j) (by decide : 0 < 1)]
  have he : projectiveChartRingHom c x i hi
      (Away.isLocalizationElem (projectiveVariable_mem i)
        (projectiveVariable_mem j)) = x j := by
    change projectiveChartRingHom c x i hi (Away.mk _ _ 1 (MvPolynomial.X j ^ 1) _) = _
    rw [projectiveChartRingHom_mk, map_pow, MvPolynomial.eval₂Hom_X', pow_one]
  ext p
  change projectiveChartRingHom c x i hi _ ∉ p.asIdeal ↔ x j ∉ p.asIdeal
  rw [he]
lemma projectiveAffineMap_immersion (c : ℂ →+* R) (x : Fin (N+1) → R)
    (i : Fin (N+1)) (hi : x i = 1)
    (h : Function.Surjective (MvPolynomial.eval₂Hom c x)) :
    IsImmersion (projectiveAffineMap c x i hi) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (projectiveChartRingHom c x i hi))) :=
    IsClosedImmersion.spec_of_surjective _ (projectiveChartRingHom_surjective c x i hi h)
  change IsImmersion (Spec.map (CommRingCat.ofHom (projectiveChartRingHom c x i hi)) ≫
    Proj.awayι _ (MvPolynomial.X i) (projectiveVariable_mem i) (by decide : 0 < 1))
  exact IsImmersion.comp _ _
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
lemma eval₂_homogeneous_scaling {σ k R : Type*} [Fintype σ]
    [CommSemiring k] [CommSemiring R] (c : k →+* R) (x : σ → R)
    (u : R) {p : MvPolynomial σ k} {n : ℕ} (hp : p.IsHomogeneous n) :
    MvPolynomial.eval₂Hom c (fun j => u * x j) p =
      u ^ n * MvPolynomial.eval₂Hom c x p := by
  classical
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : ∑ j, d j = n := by
    rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp hd)
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open HomogeneousLocalization AlgebraicGeometry CategoryTheory
variable {A K σ : Type*} [CommRing A] [Field K] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
noncomputable def homogeneousFieldEval (h : A →+* K) (f : A) (hf : h f ≠ 0) :
    HomogeneousLocalization.Away 𝒜 f →+* K :=
  (Localization.awayLift h f (isUnit_iff_ne_zero.mpr hf)).comp
    (algebraMap _ (Localization.Away f))
lemma homogeneousFieldEval_mk (h : A →+* K) (f : A) (hf : h f ≠ 0)
    {d : ℕ} (hfd : f ∈ 𝒜 d) (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    homogeneousFieldEval 𝒜 h f hf (Away.mk 𝒜 hfd n a ha) = h a * (h f)⁻¹ ^ n := by
  change (Localization.awayLift h f (isUnit_iff_ne_zero.mpr hf))
    (Localization.mk a ⟨f^n,n,rfl⟩) = _
  exact Localization.awayLift_mk h f a (h f)⁻¹ (mul_inv_cancel₀ hf) n
lemma homogeneousFieldEval_awayMap (h : A →+* K) {f g : A}
    (hf : h f ≠ 0) (hg : h g ≠ 0) {d e : ℕ} (hfd : f ∈ 𝒜 d) (hge : g ∈ 𝒜 e) :
    (homogeneousFieldEval 𝒜 h (f*g) (by rw [map_mul]; exact mul_ne_zero hf hg)).comp
      (awayMap 𝒜 hge rfl) = homogeneousFieldEval 𝒜 h f hf := by
  apply RingHom.ext
  intro a
  obtain ⟨n,a,ha,rfl⟩ := Away.mk_surjective 𝒜 hfd a
  rw [RingHom.comp_apply, awayMap_mk]
  rw [homogeneousFieldEval_mk, homogeneousFieldEval_mk]
  simp only [map_mul, map_pow, mul_inv_rev, mul_pow]
  calc
    _ = h a * ((h g)^n * (h g)⁻¹^n) * (h f)⁻¹^n := by ring
    _ = _ := by rw [← mul_pow, mul_inv_cancel₀ hg]; simp

end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open HomogeneousLocalization AlgebraicGeometry CategoryTheory
universe u v
variable {A K : Type u} {σ : Type v} [CommRing A] [Field K] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
lemma homogeneousFieldEval_awayMap' (h : A →+* K) {f g z : A}
    (hf : h f ≠ 0) (hg : h g ≠ 0) (hz : z = f*g)
    {d e : ℕ} (hfd : f ∈ 𝒜 d) (hge : g ∈ 𝒜 e) :
    (homogeneousFieldEval 𝒜 h z (by rw [hz, map_mul]; exact mul_ne_zero hf hg)).comp
      (awayMap 𝒜 hge hz) = homogeneousFieldEval 𝒜 h f hf := by
  subst z
  exact homogeneousFieldEval_awayMap 𝒜 h hf hg hfd hge
lemma homogeneousFieldPoint_independent (h : A →+* K) {f g : A}
    (hf : h f ≠ 0) (hg : h g ≠ 0) {d : ℕ} (hd : 0 < d)
    (hfd : f ∈ 𝒜 d) (hgd : g ∈ 𝒜 d) :
    Spec.map (CommRingCat.ofHom (homogeneousFieldEval 𝒜 h f hf)) ≫ Proj.awayι 𝒜 f hfd hd =
    Spec.map (CommRingCat.ofHom (homogeneousFieldEval 𝒜 h g hg)) ≫ Proj.awayι 𝒜 g hgd hd := by
  have hfg : h (f*g) ≠ 0 := by rw [map_mul]; exact mul_ne_zero hf hg
  let E := Spec.map (CommRingCat.ofHom (homogeneousFieldEval 𝒜 h (f*g) hfg))
  have H (a b : A) (ha : h a ≠ 0) (hb : h b ≠ 0)
      (had : a ∈ 𝒜 d) (hbd : b ∈ 𝒜 d) (he : f*g = a*b) :
      Spec.map (CommRingCat.ofHom (homogeneousFieldEval 𝒜 h a ha)) ≫ Proj.awayι 𝒜 a had hd =
        E ≫ Proj.awayι 𝒜 (f*g) (he ▸ SetLike.mul_mem_graded had hbd)
          (hd.trans_le (d.le_add_right d)) := by
    have hr := homogeneousFieldEval_awayMap' 𝒜 h ha hb he had hbd
    have heq : Spec.map (CommRingCat.ofHom (homogeneousFieldEval 𝒜 h a ha)) =
        E ≫ Spec.map (CommRingCat.ofHom (awayMap 𝒜 hbd he)) := by
      rw [← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext hr.symm
    rw [heq, Category.assoc, Proj.SpecMap_awayMap_awayι]
  exact (H f g hf hg hfd hgd rfl).trans (H g f hg hf hgd hfd (mul_comm f g)).symm
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type} [Field K] {N : ℕ}
noncomputable def projectiveFieldMap (c : ℂ →+* K) (x : Fin (N+1) → K)
    (i : Fin (N+1)) (hi : x i ≠ 0) : Spec (.of K) ⟶ complexProjectiveSpace N :=
  Spec.map (CommRingCat.ofHom (homogeneousFieldEval
    (MvPolynomial.homogeneousSubmodule (Fin (N+1)) ℂ)
    (MvPolynomial.eval₂Hom c x) (MvPolynomial.X i)
    (by simpa only [MvPolynomial.eval₂Hom_X'] using hi))) ≫
      Proj.awayι _ (MvPolynomial.X i) (projectiveVariable_mem i) (by decide : 0 < 1)
lemma projectiveFieldMap_independent (c : ℂ →+* K) (x : Fin (N+1) → K)
    (i j : Fin (N+1)) (hi : x i ≠ 0) (hj : x j ≠ 0) :
    projectiveFieldMap c x i hi = projectiveFieldMap c x j hj := by
  exact homogeneousFieldPoint_independent _ _
    (by simpa only [MvPolynomial.eval₂Hom_X'] using hi)
    (by simpa only [MvPolynomial.eval₂Hom_X'] using hj)
    (by decide : 0 < 1) (projectiveVariable_mem i) (projectiveVariable_mem j)
lemma projectiveFieldMap_scaling (c : ℂ →+* K) (x : Fin (N+1) → K)
    (i : Fin (N+1)) (hi : x i ≠ 0) (u : K) (hu : u ≠ 0) :
    projectiveFieldMap c (fun j => u * x j) i (mul_ne_zero hu hi) =
      projectiveFieldMap c x i hi := by
  unfold projectiveFieldMap
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  obtain ⟨n,p,hp,rfl⟩ := Away.mk_surjective _ (projectiveVariable_mem i) a
  simp only [CommRingCat.hom_ofHom]
  rw [homogeneousFieldEval_mk, homogeneousFieldEval_mk]
  rw [eval₂_homogeneous_scaling c x u hp]
  simp only [MvPolynomial.eval₂Hom_X', smul_eq_mul, mul_one, mul_inv_rev, mul_pow]
  calc
    _ = (MvPolynomial.eval₂Hom c x p * (x i)⁻¹^n) * (u^n * u⁻¹^n) := by ring
    _ = _ := by rw [← mul_pow, mul_inv_cancel₀ hu]; simp
lemma projectiveFieldMap_eq_affine (c : ℂ →+* K) (x : Fin (N+1) → K)
    (i : Fin (N+1)) (hi : x i = 1) :
    projectiveFieldMap c x i (by rw [hi]; exact one_ne_zero) =
      projectiveAffineMap c x i hi := by
  unfold projectiveFieldMap projectiveAffineMap
  congr 2
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

namespace NumericalDimensionOne
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
lemma projectiveChartRingHom_naturality {k R S σ : Type*}
    [CommRing k] [CommRing R] [CommRing S]
    (c : k →+* R) (x : σ → R) (i : σ) (hi : x i = 1) (r : R →+* S) :
    r.comp (projectiveChartRingHom c x i hi) =
      projectiveChartRingHom (r.comp c) (fun j => r (x j)) i (by rw [hi,map_one]) := by
  apply RingHom.ext
  intro a
  obtain ⟨n,p,hp,rfl⟩ := Away.mk_surjective _ (MvPolynomial.isHomogeneous_X k i) a
  simp only [RingHom.comp_apply, projectiveChartRingHom_mk, MvPolynomial.map_eval₂Hom]
lemma projectiveAffineMap_naturality {R S : Type} [CommRing R] [CommRing S] {N : ℕ}
    (c : ℂ →+* R) (x : Fin (N+1) → R) (i : Fin (N+1)) (hi : x i = 1) (r : R →+* S) :
    Spec.map (CommRingCat.ofHom r) ≫ projectiveAffineMap c x i hi =
      projectiveAffineMap (r.comp c) (fun j => r (x j)) i (by rw [hi,map_one]) := by
  change Spec.map (CommRingCat.ofHom r) ≫ (Spec.map _ ≫ Proj.awayι _ _ _ _) = _
  rw [← Category.assoc, ← Spec.map_comp]
  have h := projectiveChartRingHom_naturality c x i hi r
  exact congrArg (fun e => Spec.map (CommRingCat.ofHom e) ≫
    Proj.awayι _ (MvPolynomial.X i) (projectiveVariable_mem i) (by decide : 0 < 1)) h
lemma projectiveFieldMap_over {K : Type} [Field K] {N : ℕ}
    (c : ℂ →+* K) (x : Fin (N+1) → K) (i : Fin (N+1)) (hi : x i ≠ 0) :
    projectiveFieldMap c x i hi ≫ complexProjectiveSpaceMap N =
      Spec.map (CommRingCat.ofHom c) := by
  have hnorm : (x i)⁻¹ * x i = 1 := inv_mul_cancel₀ hi
  have hmap := projectiveFieldMap_scaling c x i hi (x i)⁻¹ (inv_ne_zero hi)
  rw [← hmap, projectiveFieldMap_eq_affine c _ i hnorm]
  exact projectiveAffineMap_over c _ i hnorm
end NumericalDimensionOne

end OAI
