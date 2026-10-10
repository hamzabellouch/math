import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateTaylorIdentity
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialPerturbationCalculus
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace OAI

/-! Actual derivatives in the map variable of the coordinate polynomial. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma coordinatePolynomialValue_hasDerivAt {n : ℕ}
    {P : Fin 3 → Fin n → Expression} (hP : ∀ k l, (P k l).SmoothCoeffs univ)
    (ε t : ℝ) {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (x : Base) :
    HasDerivAt (fun s : ℝ => coordinatePolynomialValue P ε (G+s • H) t
        (planeCoordinateIsometry x))
      (coordinateRealLinearized P ε G (H ∘ planeCoordinateIsometry.symm) t
        (planeCoordinateIsometry x)) 0 := by
  have hcomp : (H ∘ planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry = H := by
    funext y
    simp only [Function.comp_apply,planeCoordinateIsometry.symm_apply_apply]
  apply hasDerivAt_pi.mpr
  intro k
  have hd := variation_hasDerivAt isOpen_univ (hP k) ε hG hH (x,t) (mem_univ _)
  simp only [coordinatePolynomialValue,coordinateRealLinearized,linearized,variation,
    eval,hcomp,planeCoordinateIsometry.symm_apply_apply] at hd ⊢
  convert hd using 1


lemma coordinateRealLinearized_hasDerivAt {n : ℕ}
    {P : Fin 3 → Fin n → Expression} (hP : ∀ k l, (P k l).SmoothCoeffs univ)
    (ε t : ℝ) {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (x : Base) :
    HasDerivAt (fun s : ℝ => coordinateRealLinearized P ε (G+s • H)
        (H ∘ planeCoordinateIsometry.symm) t (planeCoordinateIsometry x))
      ((2 : ℝ) • coordinateQuadraticPolynomial P ε G (H ∘ planeCoordinateIsometry.symm) t
        (planeCoordinateIsometry x)) 0 := by
  have hf : ∀ i : Fin 4, ContDiff ℝ ∞ (![G,H,H,0] i) := by
    intro i
    fin_cases i
    · exact hG
    · exact hH
    · exact hH
    · exact contDiff_const
  apply hasDerivAt_pi.mpr
  intro k
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
    ((P k l).second_variation_hasDerivAt isOpen_univ (hP k l) hf
      (x,t) (mem_univ _)).const_mul (ε^(l.val+1)))
  change HasDerivAt (fun s : ℝ => ∑ l, ε^(l.val+1) *
    (P k l).variation (G+s • H) H (x,t))
    (∑ l, ε^(l.val+1) * ((P k l).variations 1).eval ![G,H,H,0] (x,t)) 0 at hd
  have hcomp : (H ∘ planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry = H := by
    funext y
    simp only [Function.comp_apply,planeCoordinateIsometry.symm_apply_apply]
  have hsecond : ((2 : ℝ) • coordinateQuadraticPolynomial P ε G
      (H ∘ planeCoordinateIsometry.symm) t (planeCoordinateIsometry x)) k =
      ∑ l, ε^(l.val+1) * ((P k l).variations 1).eval ![G,H,H,0] (x,t) := by
    simp only [coordinateQuadraticPolynomial,hcomp,
      planeCoordinateIsometry.symm_apply_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hsecond]
  simpa only [coordinateRealLinearized,linearized,hcomp,
    planeCoordinateIsometry.symm_apply_apply] using hd

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
