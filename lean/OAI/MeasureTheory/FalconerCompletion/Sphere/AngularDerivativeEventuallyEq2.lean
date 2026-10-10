import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereAmbient2

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set
open scoped ContDiff RealInnerProductSpace
variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Fintype ι]
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma angularDerivativeND_eventuallyEq (A : V →L[ℝ] V) {f g : V → ℂ} {x : V}
    (h : f =ᶠ[nhds x] g) : angularDerivativeND A f =ᶠ[nhds x] angularDerivativeND A g := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  exact congrArg (fun L : V →L[ℝ] ℂ => L (A y)) hy

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma sphereCasimirND_eventuallyEq (B : OrthonormalBasis ι ℝ V) {f g : V → ℂ} {x : V}
    (h : f =ᶠ[nhds x] g) : sphereCasimirND B f =ᶠ[nhds x] sphereCasimirND B g := by
  have he (i j : ι) := angularDerivativeND_eventuallyEq (angularGeneratorND (B i) (B j))
    (angularDerivativeND_eventuallyEq (angularGeneratorND (B i) (B j)) h)
  have hh : ∀ᶠ y in nhds x, ∀ i j, angularDerivativeND (angularGeneratorND (B i) (B j))
      (angularDerivativeND (angularGeneratorND (B i) (B j)) f) y =
      angularDerivativeND (angularGeneratorND (B i) (B j))
      (angularDerivativeND (angularGeneratorND (B i) (B j)) g) y := by
    exact Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j => he i j))
  filter_upwards [hh] with y hy
  simp only [sphereCasimirND,hy]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma angularDerivativeND_add (A : V →L[ℝ] V) {f g : V → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    angularDerivativeND A (fun x => f x+g x) = fun x => angularDerivativeND A f x+angularDerivativeND A g x := by
  funext x
  unfold angularDerivativeND
  rw [fderiv_fun_add (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma angularDerivativeND_const_mul (A : V →L[ℝ] V) {f : V → ℂ}
    (hf : ContDiff ℝ ∞ f) (c : ℂ) :
    angularDerivativeND A (fun x => c*f x) = fun x => c*angularDerivativeND A f x := by
  funext x
  unfold angularDerivativeND
  rw [fderiv_const_mul (hf.differentiable (by simp) x)]
  simp

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma sphereCasimirND_add (B : OrthonormalBasis ι ℝ V) {f g : V → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    sphereCasimirND B (fun x => f x+g x) = fun x => sphereCasimirND B f x+sphereCasimirND B g x := by
  funext x
  simp only [sphereCasimirND,angularDerivativeND_add _ hf hg,
    angularDerivativeND_add _ (angularDerivativeND_contDiff _ hf) (angularDerivativeND_contDiff _ hg),
    Finset.sum_add_distrib,mul_add]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma sphereCasimirND_const_mul (B : OrthonormalBasis ι ℝ V) {f : V → ℂ}
    (hf : ContDiff ℝ ∞ f) (c : ℂ) :
    sphereCasimirND B (fun x => c*f x) = fun x => c*sphereCasimirND B f x := by
  funext x
  simp only [sphereCasimirND,angularDerivativeND_const_mul _ hf,
    angularDerivativeND_const_mul _ (angularDerivativeND_contDiff _ hf),← Finset.mul_sum]
  ring

noncomputable def casimirPolynomialND (B : OrthonormalBasis ι ℝ V) (shift : ℕ → ℂ) :
    ℕ → (V → ℂ) → V → ℂ
  | 0, b => b
  | j+1, b => fun w => casimirPolynomialND B shift j (sphereCasimirND B b) w +
      shift j*casimirPolynomialND B shift j b w

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma casimirPolynomialND_contDiff (B : OrthonormalBasis ι ℝ V) (shift : ℕ → ℂ)
    (j : ℕ) {b : V → ℂ} (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (casimirPolynomialND B shift j b) := by
  induction j generalizing b with
  | zero => exact hb
  | succ j ih => exact (ih (sphereCasimirND_contDiff B hb)).add (contDiff_const.mul (ih hb))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma casimirPolynomialND_commute (B : OrthonormalBasis ι ℝ V) (shift : ℕ → ℂ)
    (j : ℕ) {b : V → ℂ} (hb : ContDiff ℝ ∞ b) :
    sphereCasimirND B (casimirPolynomialND B shift j b) =
      casimirPolynomialND B shift j (sphereCasimirND B b) := by
  induction j generalizing b with
  | zero => rfl
  | succ j ih =>
    rw [casimirPolynomialND,sphereCasimirND_add B
      (casimirPolynomialND_contDiff B shift j (sphereCasimirND_contDiff B hb))
      (contDiff_const.mul (casimirPolynomialND_contDiff B shift j hb)),
      sphereCasimirND_const_mul B (casimirPolynomialND_contDiff B shift j hb)]
    rw [ih hb,ih (sphereCasimirND_contDiff B hb)]
    rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma casimirPolynomialND_factor (B : OrthonormalBasis ι ℝ V) (shift : ℕ → ℂ)
    (j : ℕ) {b : V → ℂ} (hb : ContDiff ℝ ∞ b) :
    casimirPolynomialND B shift (j+1) b = fun x =>
      sphereCasimirND B (casimirPolynomialND B shift j b) x +
        shift j*casimirPolynomialND B shift j b x := by
  rw [casimirPolynomialND_commute B shift j hb]
  rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma casimirPolynomialND_eventuallyEq (B : OrthonormalBasis ι ℝ V) (shift : ℕ → ℂ)
    (j : ℕ) {f g : V → ℂ} {x : V} (h : f =ᶠ[nhds x] g) :
    casimirPolynomialND B shift j f =ᶠ[nhds x] casimirPolynomialND B shift j g := by
  induction j generalizing f g with
  | zero => exact h
  | succ j ih =>
    exact (ih (sphereCasimirND_eventuallyEq B h)).add (Filter.EventuallyEq.mul
      (Filter.EventuallyEq.refl _ _) (ih h))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma tsupport_casimirPolynomialND_subset (B : OrthonormalBasis ι ℝ V) (shift : ℕ → ℂ)
    (j : ℕ) (b : V → ℂ) : tsupport (casimirPolynomialND B shift j b) ⊆ tsupport b := by
  induction j generalizing b with
  | zero => exact Subset.rfl
  | succ j ih =>
    apply closure_minimal _ (isClosed_tsupport b)
    intro x hx
    by_contra hn
    have h₀ : casimirPolynomialND B shift j b x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hn (ih b h))
    have h₁ : casimirPolynomialND B shift j (sphereCasimirND B b) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hn ((tsupport_sphereCasimirND_subset B b)
        (ih (sphereCasimirND B b) h)))
    exact hx (by simp [casimirPolynomialND,h₀,h₁])

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma angularDerivativeND_second (A : V →L[ℝ] V) {f : V → ℂ}
    (hf : ContDiff ℝ ∞ f) (x : V) :
    angularDerivativeND A (angularDerivativeND A f) x =
      fderiv ℝ (fderiv ℝ f) x (A x) (A x) + fderiv ℝ f x (A (A x)) := by
  unfold angularDerivativeND
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  rw [fderiv_clm_apply (hdf.differentiable (by simp) x) A.differentiableAt]
  simp [add_comm]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma bilinearND_basis_expansion (B : OrthonormalBasis ι ℝ V)
    (T : V →L[ℝ] V →L[ℝ] ℂ) (x y : V) :
    T x y = ∑ i, ∑ j, (inner ℝ (B i) x : ℂ)*(inner ℝ (B j) y : ℂ)*T (B i) (B j) := by
  conv_lhs => rw [← B.sum_repr x,← B.sum_repr y]
  simp only [map_sum,sum_apply,map_smul,smul_apply,
    OrthonormalBasis.repr_apply_apply,real_inner_comm x,real_inner_comm y,
    Complex.real_smul,Finset.mul_sum,mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma angularGeneratorND_sum_bilinear (B : OrthonormalBasis ι ℝ V)
    (T : V →L[ℝ] V →L[ℝ] ℂ) (x : V) :
    (∑ i, ∑ j, T (angularGeneratorND (B i) (B j) x) (angularGeneratorND (B i) (B j) x)) =
      2*((‖x‖:ℂ)^2*(∑ i, T (B i) (B i)) - T x x) := by
  have ht (i j : ι) :
      T (angularGeneratorND (B i) (B j) x) (angularGeneratorND (B i) (B j) x) =
      (inner ℝ (B i) x : ℂ)^2*T (B j) (B j) +
      (inner ℝ (B j) x : ℂ)^2*T (B i) (B i) -
      ((inner ℝ (B i) x : ℂ)*(inner ℝ (B j) x : ℂ)*T (B j) (B i) +
       (inner ℝ (B i) x : ℂ)*(inner ℝ (B j) x : ℂ)*T (B i) (B j)) := by
    simp only [angularGeneratorND_apply,map_sub,sub_apply,map_smul,
      smul_apply,Complex.real_smul]
    ring
  simp_rw [ht,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  have hs : (∑ i, (inner ℝ (B i) x : ℂ)^2) = (‖x‖:ℂ)^2 := by
    exact_mod_cast B.sum_sq_inner_right x
  have h₀ : (∑ i, ∑ j, (inner ℝ (B i) x : ℂ)^2*T (B j) (B j)) =
      (‖x‖:ℂ)^2*∑ i, T (B i) (B i) := by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul,hs]
  have h₁ : (∑ i, ∑ j, (inner ℝ (B j) x : ℂ)^2*T (B i) (B i)) =
      (‖x‖:ℂ)^2*∑ i, T (B i) (B i) := by
    simp_rw [← Finset.sum_mul,hs]
    rw [← Finset.mul_sum]
  have h₂ : (∑ i, ∑ j, (inner ℝ (B i) x : ℂ)*(inner ℝ (B j) x : ℂ)*T (B j) (B i)) = T x x := by
    rw [Finset.sum_comm]
    rw [bilinearND_basis_expansion B T x x]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h₃ := (bilinearND_basis_expansion B T x x).symm
  rw [h₀,h₁,h₂,h₃]
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma angularGeneratorND_sum_second_vector (B : OrthonormalBasis ι ℝ V) (x : V) :
    (∑ i, ∑ j, angularGeneratorND (B i) (B j) (angularGeneratorND (B i) (B j) x)) =
      -(2*((Fintype.card ι:ℝ)-1)) • x := by
  classical
  simp_rw [angularGeneratorND_apply,inner_sub_right,inner_smul_right,B.inner_eq_ite]
  have ht (i j : ι) :
      (inner ℝ (B i) x * (if i = j then (1:ℝ) else 0) - inner ℝ (B j) x * 1) • B j -
        (inner ℝ (B i) x * 1 - inner ℝ (B j) x * (if j = i then (1:ℝ) else 0)) • B i =
      (if i=j then (2:ℝ) • (inner ℝ (B i) x • B i) else 0) -
        inner ℝ (B j) x • B j - inner ℝ (B i) x • B i := by
    by_cases h : i = j
    · subst j; simp; module
    · simp [h,Ne.symm h]
  simp only [ite_true]
  simp_rw [ht,Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.sum_const,Finset.card_univ]
  have hr : (∑ i, inner ℝ (B i) x • B i) = x := by simpa [OrthonormalBasis.repr_apply_apply] using B.sum_repr x
  rw [← Finset.smul_sum,hr,← Finset.smul_sum,hr]
  module

omit [MeasurableSpace V] [BorelSpace V] in
lemma sphereCasimirND_eq_intrinsic (B : OrthonormalBasis ι ℝ V) {f : V → ℂ}
    (hf : ContDiff ℝ ∞ f) (x : V) :
    sphereCasimirND B f x =
      (‖x‖:ℂ)^2 * (Laplacian.laplacian f x) - fderiv ℝ (fderiv ℝ f) x x x -
      ((Module.finrank ℝ V:ℂ)-1)*fderiv ℝ f x x := by
  unfold sphereCasimirND
  simp_rw [angularDerivativeND_second _ hf,Finset.sum_add_distrib]
  rw [angularGeneratorND_sum_bilinear B]
  have hl : (∑ i, ∑ j, fderiv ℝ f x
      (angularGeneratorND (B i) (B j) (angularGeneratorND (B i) (B j) x))) =
      -(2*((Fintype.card ι:ℝ)-1)) • fderiv ℝ f x x := by
    simp_rw [← map_sum]
    rw [angularGeneratorND_sum_second_vector,map_smul]
  rw [hl]
  have he : Laplacian.laplacian f x = ∑ i, fderiv ℝ (fderiv ℝ f) x (B i) (B i) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f B]
    simp [iteratedFDeriv_two_apply]
  rw [← he, Module.finrank_eq_card_basis B.toBasis]
  simp only [Complex.real_smul]
  push_cast
  ring

omit [MeasurableSpace V] [BorelSpace V] in
lemma sphereCasimirND_basis_independent {κ : Type*} [Fintype κ]
    (B : OrthonormalBasis ι ℝ V) (C : OrthonormalBasis κ ℝ V)
    {f : V → ℂ} (hf : ContDiff ℝ ∞ f) : sphereCasimirND B f = sphereCasimirND C f := by
  funext x
  rw [sphereCasimirND_eq_intrinsic B hf,sphereCasimirND_eq_intrinsic C hf]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma angularGeneratorND_isometry (Q : V ≃ₗᵢ[ℝ] V) (v w x : V) :
    Q (angularGeneratorND v w x) = angularGeneratorND (Q v) (Q w) (Q x) := by
  simp [angularGeneratorND_apply]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma angularDerivativeND_comp_isometry (Q : V ≃ₗᵢ[ℝ] V) (v w : V)
    {f : V → ℂ} (hf : ContDiff ℝ ∞ f) :
    angularDerivativeND (angularGeneratorND v w) (f ∘ Q) =
      (angularDerivativeND (angularGeneratorND (Q v) (Q w)) f) ∘ Q := by
  funext x
  unfold angularDerivativeND
  rw [fderiv_comp x (hf.differentiable (by simp) _) Q.differentiableAt]
  simp only [ContinuousLinearMap.comp_apply,LinearIsometryEquiv.fderiv]
  change (fderiv ℝ f (Q x)) (Q (angularGeneratorND v w x)) = _
  rw [angularGeneratorND_isometry]
  rfl

omit [MeasurableSpace V] [BorelSpace V] in
lemma sphereCasimirND_comp_isometry (B : OrthonormalBasis ι ℝ V)
    (Q : V ≃ₗᵢ[ℝ] V) {f : V → ℂ} (hf : ContDiff ℝ ∞ f) :
    sphereCasimirND B (f ∘ Q) = (sphereCasimirND B f) ∘ Q := by
  have hh : sphereCasimirND B (f ∘ Q) = (sphereCasimirND (B.map Q) f) ∘ Q := by
    funext x
    simp only [sphereCasimirND,Function.comp_apply,OrthonormalBasis.map_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [angularDerivativeND_comp_isometry Q (B i) (B j) hf,
      angularDerivativeND_comp_isometry Q (B i) (B j)
        (angularDerivativeND_contDiff _ hf)]
    rfl
  rw [hh,sphereCasimirND_basis_independent (B.map Q) B hf]

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
