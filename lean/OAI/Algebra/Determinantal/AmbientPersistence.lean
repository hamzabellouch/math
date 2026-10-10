import OAI.Algebra.Determinantal.AmbientOperators
import OAI.Algebra.Determinantal.AmbientMixedCount

namespace OAI

namespace PermanentBorder.AmbientPolar
open MvPolynomial Matrix PolarAnalysis KernelBilinear
open scoped Classical
variable {σ κ ι : Type} [Fintype σ] [Fintype κ] [Fintype ι]

lemma polynomialSystem_differentiable (b : σ → ℂ)
    (L : (Option κ → ℂ) →L[ℂ] (σ → ℂ)) (h : κ → σ → ℂ)
    (P : Poly σ) (z : Option κ → ℂ) :
    DifferentiableAt ℂ (polynomialSystem (operators b L h) P) z := by
  apply differentiableAt_pi.mpr
  intro i
  exact ((contDiff_mvPolynomial_eval ((operators b L h i) P)).differentiable
    (by decide)).differentiableAt

/-- A selected finite family of simple polar zeros persists in one determinant approximant. -/
theorem exists_affine_polar_approximant {n : ℕ} {P : Poly σ}
    (hb : HasBorderDeterminant n P) (b : σ → ℂ)
    (L : (Option κ → ℂ) →L[ℂ] (σ → ℂ)) (h : κ → σ → ℂ)
    (x : ι → ℂ × (κ → ℂ)) (hx : Function.Injective x)
    (hz : ∀ j, polarPair (fun y => eval y P)
      (fun z => b + L (optionProduct.symm z)) h (x j) = 0)
    (hs : ∀ j, (fderiv ℂ (polarPair (fun y => eval y P)
      (fun z => b + L (optionProduct.symm z)) h) (x j)).IsInvertible) :
    ∃ (A₀ : Matrix (Fin n) (Fin n) ℂ) (A : σ → Matrix (Fin n) (Fin n) ℂ)
      (y : ι → Option κ → ℂ), Function.Injective y ∧
      ∀ i, SimplePolynomialZero (operators b L h)
        (affineMatrixPolynomial n A₀ A) (y i) := by
  classical
  let Q := polynomialSystem (operators b L h) P
  let F := polarPair (fun y => eval y P)
    (fun z => b + L (optionProduct.symm z)) h
  have hrel : F = fun z => optionProduct (Q (optionProduct.symm z)) :=
    polarPair_operators b L h P
  have hF (z) : DifferentiableAt ℂ F z := by
    rw [hrel]
    exact optionProduct.differentiableAt.comp z
      ((polynomialSystem_differentiable b L h P _).comp z
        optionProduct.symm.differentiableAt)
  have hconj : (fun z => optionProduct.symm (F (optionProduct z))) = Q := by
    funext z
    rw [hrel]
    simp only [ContinuousLinearEquiv.symm_apply_apply]
  apply PolarAnalysis.HasBorderDeterminant.exists_simple_approximant hb
    (operators b L h) (fun j => optionProduct.symm (x j))
    (optionProduct.symm.injective.comp hx)
  intro j
  constructor
  · have hzj : optionProduct (Q (optionProduct.symm (x j))) = 0 := by
      exact (congrFun hrel (x j)).symm.trans (hz j)
    exact optionProduct.injective (hzj.trans (map_zero optionProduct).symm)
  · have hh := Polar.simple_conjugate optionProduct.symm (hF (x j)) (hs j)
    simp only [ContinuousLinearEquiv.symm_symm] at hh
    rw [hconj] at hh
    exact hh

/-- The number of selected simple polar zeros is bounded by the mixed coefficient. -/
theorem border_polar_mixed_count {n : ℕ} {P : Poly σ}
    (hb : HasBorderDeterminant (n+1) P) (b : σ → ℂ)
    (L : (Option κ → ℂ) →L[ℂ] (σ → ℂ)) (h : κ → σ → ℂ)
    (x : ι → ℂ × (κ → ℂ)) (hx : Function.Injective x)
    (hz : ∀ j, polarPair (fun y => eval y P)
      (fun z => b + L (optionProduct.symm z)) h (x j) = 0)
    (hs : ∀ j, (fderiv ℂ (polarPair (fun y => eval y P)
      (fun z => b + L (optionProduct.symm z)) h) (x j)).IsInvertible) :
    Fintype.card ι ≤
      (Multigraded.mixedPolynomial (firstGroup (κ := κ) (n := n)) secondGroup).coeff
        (dimensions κ n) := by
  classical
  obtain ⟨A₀,A,y,hy,hys⟩ := exists_affine_polar_approximant hb b L h x hx hz hs
  let P' := affineMatrixPolynomial (n+1) A₀ A
  let Q := polynomialSystem (operators b L h) P'
  have hrel : polarPair (fun y => (affine A₀ A y).det)
      (fun z => b + L (optionProduct.symm z)) h =
      fun z => optionProduct (Q (optionProduct.symm z)) := by
    have heval : (fun y => (affine A₀ A y).det) = (fun y => eval y P') := by
      funext z
      exact (Polar.eval_matrix A₀ A z).symm
    rw [heval]
    exact polarPair_operators b L h P'
  apply affine_polar_mixed_count A₀ A b L h (fun j => optionProduct (y j))
    (optionProduct.injective.comp hy)
  · intro j
    rw [hrel]
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    have hzj : Q (y j) = 0 := (hys j).1
    rw [hzj, map_zero]
  · intro j
    rw [hrel]
    exact Polar.simple_conjugate optionProduct
      (polynomialSystem_differentiable b L h P' (y j)) (hys j).2

end PermanentBorder.AmbientPolar

end OAI
