import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.SharedBinSupportCollision

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set
open scoped ContDiff RealInnerProductSpace
variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [Fintype ι]
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
noncomputable def angularDerivativeND (A : V →L[ℝ] V) (f : V → ℂ) (x : V) : ℂ :=
  fderiv ℝ f x (A x)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma angularDerivativeND_contDiff (A : V →L[ℝ] V) {f : V → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (angularDerivativeND A f) :=
  (hf.fderiv_right (by simp)).clm_apply A.contDiff

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
noncomputable def angularGeneratorND (v w : V) : V →L[ℝ] V :=
  InnerProductSpace.rankOne ℝ w v - InnerProductSpace.rankOne ℝ v w

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
noncomputable def sphereCasimirND (b : OrthonormalBasis ι ℝ V) (f : V → ℂ) (x : V) : ℂ :=
  (1/2:ℂ)*∑ i, ∑ j, angularDerivativeND (angularGeneratorND (b i) (b j))
    (angularDerivativeND (angularGeneratorND (b i) (b j)) f) x

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma sphereCasimirND_contDiff (b : OrthonormalBasis ι ℝ V) {f : V → ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (sphereCasimirND b f) := by
  unfold sphereCasimirND
  apply contDiff_const.mul
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    angularDerivativeND_contDiff _ (angularDerivativeND_contDiff _ hf)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma tsupport_angularDerivativeND_subset (A : V →L[ℝ] V) (f : V → ℂ) :
    tsupport (angularDerivativeND A f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra hn
  have hz := fderiv_of_notMem_tsupport ℝ hn
  exact hx (by simp [angularDerivativeND,hz])

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma tsupport_sphereCasimirND_subset (B : OrthonormalBasis ι ℝ V) (f : V → ℂ) :
    tsupport (sphereCasimirND B f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra hn
  have hz (i j : ι) : angularDerivativeND (angularGeneratorND (B i) (B j))
      (angularDerivativeND (angularGeneratorND (B i) (B j)) f) x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun h => hn ((tsupport_angularDerivativeND_subset _ _)
      ((tsupport_angularDerivativeND_subset _ _) h))
  exact hx (by simp [sphereCasimirND,hz])

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

end CurrentFalconer
end GraphLiteralSupport
end
end

end OAI
