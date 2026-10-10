import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import OAI.AlgebraicGeometry.PlaneCurves.AnalyticTaylor

namespace OAI

/-!
# Analytic normal charts and their invertible Jacobians; Multiplicity in analytic normal charts; Equations for the inverse analytic normal chart
-/

section

/-!
# A genuine local analytic normal-coordinate chart
-/

noncomputable section
namespace Nagata.Workers.W28

abbrev ComplexPlane := ℂ × ℂ

/-- Evaluate an actual two-variable polynomial on the complex affine plane. -/
def planePolynomialEval (G : MvPolynomial (Fin 2) ℂ) (z : ComplexPlane) : ℂ :=
  MvPolynomial.eval (fun i => if i = 0 then z.1 else z.2) G

/-- Tangential coordinate and actual polynomial defining equation. -/
def polynomialNormalCoordinates (G : MvPolynomial (Fin 2) ℂ)
    (z : ComplexPlane) : ComplexPlane := (z.1, planePolynomialEval G z)

theorem planePolynomialEval_analyticAt (G : MvPolynomial (Fin 2) ℂ)
    (p : ComplexPlane) : AnalyticAt ℂ (planePolynomialEval G) p := by
  obtain ⟨q, hq, hz⟩ := polynomial_order_implies_analytic_order G p 0
    (Nagata.AffineMultiplicity.orderAtLeast_zero _ _)
  exact hq.analyticAt

theorem polynomialNormalCoordinates_analyticAt (G : MvPolynomial (Fin 2) ℂ)
    (p : ComplexPlane) : AnalyticAt ℂ (polynomialNormalCoordinates G) p := by
  exact ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt p).prod
    (planePolynomialEval_analyticAt G p)

/-- If the actual Jacobian of `(ζ,G)` is nonsingular, it provides an open
local chart whose inverse is analytic at the image of the marked point.
No abstract geometric object or prescribed chart-existence field is assumed. -/
theorem exists_analytic_normal_chart
    (G : MvPolynomial (Fin 2) ℂ) (p : ComplexPlane)
    (hdet : (fderiv ℂ (polynomialNormalCoordinates G) p).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph ComplexPlane ComplexPlane,
      (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G ∧
      p ∈ e.source ∧
      AnalyticAt ℂ e.symm (polynomialNormalCoordinates G p) := by
  let D := fderiv ℂ (polynomialNormalCoordinates G) p
  let L : ComplexPlane ≃L[ℂ] ComplexPlane :=
    D.toContinuousLinearEquivOfDetNeZero hdet
  have hL : (L : ComplexPlane →L[ℂ] ComplexPlane) = D :=
    D.coe_toContinuousLinearEquivOfDetNeZero hdet
  have ha := polynomialNormalCoordinates_analyticAt G p
  have hd : HasStrictFDerivAt (polynomialNormalCoordinates G)
      (L : ComplexPlane →L[ℂ] ComplexPlane) p := by
    rw [hL]
    exact ha.hasStrictFDerivAt
  let e := hd.toOpenPartialHomeomorph (polynomialNormalCoordinates G)
  have he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G := rfl
  have hp : p ∈ e.source := hd.mem_toOpenPartialHomeomorph_source
  refine ⟨e, he, hp, ?_⟩
  have hi : AnalyticAt ℂ e.symm (e p) :=
    e.analyticAt_symm' hp (by simpa only [he] using ha) (by simpa only [he] using hL.symm)
  simpa only [he] using hi

end Nagata.Workers.W28

end
end

section

noncomputable section
namespace Nagata.Workers.W28
open scoped Topology

/-- Actual polynomial ideal-power multiplicity is preserved by the inverse
of a genuine analytic local chart at its marked image. -/
theorem polynomial_order_in_inverse_chart
    (P : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (p : ComplexPlane) (hp : p ∈ e.source)
    (he : AnalyticAt ℂ e.symm (e p)) (m : ℕ)
    (hP : Nagata.AffineMultiplicity.orderAtLeast
      (fun i : Fin 2 => if i = 0 then p.1 else p.2) m P) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ) (planePolynomialEval P ∘ e.symm) (e p) m := by
  have h := polynomial_order_implies_analytic_order P p m hP
  have hh : HasAnalyticOrderAtLeast (𝕜 := ℂ) (planePolynomialEval P)
      (e.symm (e p)) m := by
    rw [e.left_inv hp]
    exact h
  exact hh.comp he

/-- At any actual point of the inverse chart, normal rescaling transports
polynomial ordinary multiplicity to the rescaled local analytic function.
The polynomial point in the hypothesis is the actual inverse image of `(u,s*w)`. -/
theorem polynomial_order_in_rescaled_inverse_chart
    (P : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (s : ℂ) (q : ComplexPlane) (m : ℕ)
    (he : AnalyticAt ℂ e.symm (analyticNormalScale s q))
    (hP : Nagata.AffineMultiplicity.orderAtLeast
      (fun i : Fin 2 => if i = 0 then (e.symm (analyticNormalScale s q)).1
        else (e.symm (analyticNormalScale s q)).2) m P) :
    HasAnalyticOrderAtLeast (𝕜 := ℂ)
      ((planePolynomialEval P ∘ e.symm) ∘ analyticNormalScale s) q m := by
  have h := polynomial_order_implies_analytic_order P (e.symm (analyticNormalScale s q)) m hP
  exact (h.comp he).comp (analyticNormalScale_analyticAt s q)

/-- The analytic inverse obtained from a nonsingular polynomial chart remains
analytic throughout some genuine neighborhood of the marked chart image. -/
theorem exists_normal_chart_with_locally_analytic_inverse
    (G : MvPolynomial (Fin 2) ℂ) (p : ComplexPlane)
    (hdet : (fderiv ℂ (polynomialNormalCoordinates G) p).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph ComplexPlane ComplexPlane,
      (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G ∧
      p ∈ e.source ∧ ∀ᶠ y in 𝓝 (e p), AnalyticAt ℂ e.symm y := by
  obtain ⟨e, he, hp, ha⟩ := exists_analytic_normal_chart G p hdet
  refine ⟨e, he, hp, ?_⟩
  have hh : AnalyticAt ℂ e.symm (e p) := by simpa only [he] using ha
  exact hh.eventually_analyticAt

end Nagata.Workers.W28

end
end

section

noncomputable section
namespace Nagata.Workers.W28

/-- The continuous linear map given by the two actual polynomial partials. -/
def polynomialGradient (G : MvPolynomial (Fin 2) ℂ) (p : ComplexPlane) :
    ComplexPlane →L[ℂ] ℂ :=
  planePolynomialEval (MvPolynomial.pderiv 0 G) p • ContinuousLinearMap.fst ℂ ℂ ℂ +
  planePolynomialEval (MvPolynomial.pderiv 1 G) p • ContinuousLinearMap.snd ℂ ℂ ℂ

/-- Algebraic partial derivatives agree with the complex Fréchet derivative. -/
theorem planePolynomialEval_hasFDerivAt (G : MvPolynomial (Fin 2) ℂ)
    (p : ComplexPlane) :
    HasFDerivAt (planePolynomialEval G) (polynomialGradient G p) p := by
  induction G using MvPolynomial.induction_on with
  | C a =>
      have hf : planePolynomialEval (MvPolynomial.C a) = fun _ : ComplexPlane => a := by
        funext z
        simp [planePolynomialEval]
      have hg : polynomialGradient (MvPolynomial.C a) p = 0 := by
        apply ContinuousLinearMap.ext
        intro z
        simp [polynomialGradient, planePolynomialEval]
      rw [hf, hg]
      exact hasFDerivAt_const (𝕜 := ℂ) a p
  | add P Q hP hQ =>
      have hf : planePolynomialEval (P + Q) = fun z => planePolynomialEval P z + planePolynomialEval Q z := by
        funext z
        simp [planePolynomialEval]
      have hg : polynomialGradient (P + Q) p = polynomialGradient P p + polynomialGradient Q p := by
        apply ContinuousLinearMap.ext
        intro z
        simp [polynomialGradient, planePolynomialEval]
        ring
      rw [hf, hg]
      exact hP.add hQ
  | mul_X P i hP =>
      fin_cases i
      · have hf : planePolynomialEval (P * MvPolynomial.X 0) = fun z => planePolynomialEval P z * z.1 := by
          funext z
          simp [planePolynomialEval]
        have hg : polynomialGradient (P * MvPolynomial.X 0) p =
            planePolynomialEval P p • ContinuousLinearMap.fst ℂ ℂ ℂ +
              p.1 • polynomialGradient P p := by
          apply ContinuousLinearMap.ext
          intro z
          simp [polynomialGradient, planePolynomialEval]
          ring
        change HasFDerivAt (planePolynomialEval (P * MvPolynomial.X (0 : Fin 2))) (polynomialGradient (P * MvPolynomial.X (0 : Fin 2)) p) p
        rw [hf, hg]
        exact hP.mul ((ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt (x := p))
      · have hf : planePolynomialEval (P * MvPolynomial.X 1) = fun z => planePolynomialEval P z * z.2 := by
          funext z
          simp [planePolynomialEval]
        have hg : polynomialGradient (P * MvPolynomial.X 1) p =
            planePolynomialEval P p • ContinuousLinearMap.snd ℂ ℂ ℂ +
              p.2 • polynomialGradient P p := by
          apply ContinuousLinearMap.ext
          intro z
          simp [polynomialGradient, planePolynomialEval]
          ring
        change HasFDerivAt (planePolynomialEval (P * MvPolynomial.X (1 : Fin 2))) (polynomialGradient (P * MvPolynomial.X (1 : Fin 2)) p) p
        rw [hf, hg]
        exact hP.mul ((ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt (x := p))

theorem polynomialNormalCoordinates_hasFDerivAt
    (G : MvPolynomial (Fin 2) ℂ) (p : ComplexPlane) :
    HasFDerivAt (polynomialNormalCoordinates G)
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).prod (polynomialGradient G p)) p :=
  ((ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt).prodMk
    (planePolynomialEval_hasFDerivAt G p)

/-- Exact Jacobian identity: det D(X,G) = ∂G/∂Y. -/
theorem polynomialNormalCoordinates_det
    (G : MvPolynomial (Fin 2) ℂ) (p : ComplexPlane) :
    (fderiv ℂ (polynomialNormalCoordinates G) p).det =
      planePolynomialEval (MvPolynomial.pderiv 1 G) p := by
  rw [(polynomialNormalCoordinates_hasFDerivAt G p).fderiv]
  change LinearMap.det
    (((ContinuousLinearMap.fst ℂ ℂ ℂ).prod (polynomialGradient G p)).toLinearMap) = _
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℂ)]
  rw [Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, polynomialGradient,
    Module.Basis.coe_finTwoProd_repr]

/-- A nonzero actual normal partial derivative supplies the local analytic chart. -/
theorem exists_analytic_normal_chart_of_partial_ne_zero
    (G : MvPolynomial (Fin 2) ℂ) (p : ComplexPlane)
    (hpartial : planePolynomialEval (MvPolynomial.pderiv 1 G) p ≠ 0) :
    ∃ e : OpenPartialHomeomorph ComplexPlane ComplexPlane,
      (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G ∧
      p ∈ e.source ∧
      AnalyticAt ℂ e.symm (polynomialNormalCoordinates G p) := by
  apply exists_analytic_normal_chart G p
  rwa [polynomialNormalCoordinates_det]

/-- The alternative tangential coordinate, used when the other partial is nonzero. -/
def polynomialOtherCoordinates (G : MvPolynomial (Fin 2) ℂ)
    (z : ComplexPlane) : ComplexPlane := (z.2, planePolynomialEval G z)

theorem polynomialOtherCoordinates_det
    (G : MvPolynomial (Fin 2) ℂ) (p : ComplexPlane) :
    (fderiv ℂ (polynomialOtherCoordinates G) p).det =
      -planePolynomialEval (MvPolynomial.pderiv 0 G) p := by
  have hd : HasFDerivAt (polynomialOtherCoordinates G)
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).prod (polynomialGradient G p)) p :=
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt).prodMk
      (planePolynomialEval_hasFDerivAt G p)
  rw [hd.fderiv]
  change LinearMap.det
    (((ContinuousLinearMap.snd ℂ ℂ ℂ).prod (polynomialGradient G p)).toLinearMap) = _
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℂ)]
  rw [Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, polynomialGradient,
    Module.Basis.coe_finTwoProd_repr]

theorem exists_analytic_other_chart_of_partial_ne_zero
    (G : MvPolynomial (Fin 2) ℂ) (p : ComplexPlane)
    (hpartial : planePolynomialEval (MvPolynomial.pderiv 0 G) p ≠ 0) :
    ∃ e : OpenPartialHomeomorph ComplexPlane ComplexPlane,
      (e : ComplexPlane → ComplexPlane) = polynomialOtherCoordinates G ∧
      p ∈ e.source ∧ AnalyticAt ℂ e.symm (polynomialOtherCoordinates G p) := by
  have hdet : (fderiv ℂ (polynomialOtherCoordinates G) p).det ≠ 0 := by
    rw [polynomialOtherCoordinates_det]
    exact neg_ne_zero.mpr hpartial
  let D := fderiv ℂ (polynomialOtherCoordinates G) p
  let L : ComplexPlane ≃L[ℂ] ComplexPlane := D.toContinuousLinearEquivOfDetNeZero hdet
  have hL : (L : ComplexPlane →L[ℂ] ComplexPlane) = D :=
    D.coe_toContinuousLinearEquivOfDetNeZero hdet
  have ha : AnalyticAt ℂ (polynomialOtherCoordinates G) p :=
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt p).prod (planePolynomialEval_analyticAt G p)
  have hd : HasStrictFDerivAt (polynomialOtherCoordinates G)
      (L : ComplexPlane →L[ℂ] ComplexPlane) p := by
    rw [hL]
    exact ha.hasStrictFDerivAt
  let e := hd.toOpenPartialHomeomorph (polynomialOtherCoordinates G)
  have he : (e : ComplexPlane → ComplexPlane) = polynomialOtherCoordinates G := rfl
  have hp : p ∈ e.source := hd.mem_toOpenPartialHomeomorph_source
  refine ⟨e, he, hp, ?_⟩
  have hi : AnalyticAt ℂ e.symm (e p) :=
    e.analyticAt_symm' hp (by simpa only [he] using ha) (by simpa only [he] using hL.symm)
  simpa only [he] using hi

/-- A nonzero polynomial gradient supplies one of the two genuine normal charts. -/
theorem exists_analytic_chart_of_nonzero_gradient
    (G : MvPolynomial (Fin 2) ℂ) (p : ComplexPlane)
    (hgradient : planePolynomialEval (MvPolynomial.pderiv 0 G) p ≠ 0 ∨
      planePolynomialEval (MvPolynomial.pderiv 1 G) p ≠ 0) :
    ∃ e : OpenPartialHomeomorph ComplexPlane ComplexPlane,
      ((e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G ∨
       (e : ComplexPlane → ComplexPlane) = polynomialOtherCoordinates G) ∧
      p ∈ e.source ∧ AnalyticAt ℂ e.symm (e p) := by
  rcases hgradient with h0 | h1
  · obtain ⟨e, he, hp, ha⟩ := exists_analytic_other_chart_of_partial_ne_zero G p h0
    exact ⟨e, Or.inr he, hp, by simpa only [he] using ha⟩
  · obtain ⟨e, he, hp, ha⟩ := exists_analytic_normal_chart_of_partial_ne_zero G p h1
    exact ⟨e, Or.inl he, hp, by simpa only [he] using ha⟩

end Nagata.Workers.W28

end
end

section

noncomputable section
namespace Nagata.Workers.W28

/-- The inverse chart's tangential coordinate is the actual first coordinate. -/
theorem inverse_normal_chart_first
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G)
    (q : ComplexPlane) (hq : q ∈ e.target) : (e.symm q).1 = q.1 := by
  have h := congrArg Prod.fst (e.right_inv hq)
  simpa only [he, polynomialNormalCoordinates] using h

/-- The defining polynomial evaluated in genuine normal coordinates is exactly
that normal coordinate, as an identity throughout the chart target. -/
theorem inverse_normal_chart_equation
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G)
    (q : ComplexPlane) (hq : q ∈ e.target) : planePolynomialEval G (e.symm q) = q.2 := by
  have h := congrArg Prod.snd (e.right_inv hq)
  simpa only [he, polynomialNormalCoordinates] using h

/-- Exact defining-equation identity after the normal degeneration substitution. -/
theorem rescaled_inverse_normal_chart_equation
    (G : MvPolynomial (Fin 2) ℂ)
    (e : OpenPartialHomeomorph ComplexPlane ComplexPlane)
    (he : (e : ComplexPlane → ComplexPlane) = polynomialNormalCoordinates G)
    (s : ℂ) (q : ComplexPlane) (hq : analyticNormalScale s q ∈ e.target) :
    planePolynomialEval G (e.symm (analyticNormalScale s q)) = s * q.2 :=
  inverse_normal_chart_equation G e he (analyticNormalScale s q) hq

end Nagata.Workers.W28

end
end

end OAI
