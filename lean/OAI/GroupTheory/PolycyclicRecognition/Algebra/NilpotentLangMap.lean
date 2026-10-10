import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialModelExponential
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinFiniteDifference
import OAI.GroupTheory.PolycyclicRecognition.Algebra.LinearInvariantInverse

namespace OAI

/-! # The Lang map for a nilpotent Lie automorphism without fixed vectors

The nonlinear error raises the lower central series. After applying the
inverse of A - 1, the finite correction algorithm gives a global inverse.
-/

noncomputable section
namespace PolycyclicRecognition
open LieModule


variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]

/-- Fixed-point-freeness of the linear automorphism suffices for bijectivity of
its nonlinear twisted difference on the simply connected nilpotent group. -/
theorem polynomial_lang_bijective (A : L ≃ₗ⁅ℝ⁆ L)
    (hA : Function.Bijective (fun x : L => A x - x)) :
    Function.Bijective (fun x : L => x⁻¹ * A x) := by
  let e : L ≃ₗ[ℝ] L := LinearEquiv.ofBijective (A.toLinearMap - (LinearMap.id : L →ₗ[ℝ] L)) hA
  have he (x : L) : e x = A x - x := rfl
  let V : ℕ → Submodule ℝ L := fun k => (lowerCentralSeries ℝ L L k).toSubmodule
  have hpres (k : ℕ) (x : L) (hx : x ∈ V k) : A x ∈ V k :=
    LieIdeal.map_lowerCentralSeries_le k (LieIdeal.mem_map hx)
  have hinv (k : ℕ) (x : L) (hx : x ∈ V k) : e.symm x ∈ V k :=
    inverse_mem_of_preserves_submodule e (V k)
      (fun y hy => by rw [he]; exact (V k).sub_mem (hpres k y hy) hy) hx
  let f : L → L := fun x => x⁻¹ * A x
  have hraise (k : ℕ) (x y : L) (hxy : x - y ∈ V k) :
      (f x - f y) - e (x - y) ∈ V (k + 1) := by
    have hh := finiteDynkinPolynomial_sub_linear_mem_succ P.coefficients
      ![-x, A x] ![-y, A y] k (by
        intro i
        fin_cases i
        · change -x - -y ∈ V k
          simpa only [neg_sub_neg, neg_sub] using (V k).neg_mem hxy
        · change A x - A y ∈ V k
          rw [← map_sub]
          exact hpres k (x - y) hxy)
    have hv : ![-x, A x] - ![-y, A y] = ![-(x - y), A (x - y)] := by
      ext i
      fin_cases i
      · change -x - -y = -(x - y)
        abel
      · change A x - A y = A (x - y)
        rw [map_sub]
    rw [hv, binaryDynkinLinearPart P.coefficients
      (PolynomialExponentialCoordinates.axis_normalized)] at hh
    have hterm : -(x - y) + A (x - y) = A (x - y) - (x - y) := by abel
    rw [hterm] at hh
    change (finiteDynkinPolynomial P.coefficients ![-x, A x] -
      finiteDynkinPolynomial P.coefficients ![-y, A y]) -
      (A (x - y) - (x - y)) ∈ V (k + 1) at hh
    dsimp only [f]
    rw [P.inv_eq_neg, P.inv_eq_neg, P.mul_eq, P.mul_eq, he]
    exact hh
  obtain ⟨c, hc⟩ := (LieModule.isNilpotent_iff ℝ L L).mp (inferInstance : LieModule.IsNilpotent L L)
  have hbij : Function.Bijective (fun x => e.symm (f x)) := by
    apply bijective_of_raises_difference_filtration V (by simp [V])
      (congrArg LieSubmodule.toSubmodule hc)
    intro k x y hxy
    have hh := hinv (k + 1) ((f x - f y) - e (x - y)) (hraise k x y hxy)
    simpa only [map_sub, e.symm_apply_apply] using hh
  have hcomp := e.bijective.comp hbij
  simpa only [Function.comp_def, e.apply_symm_apply] using hcomp

end PolycyclicRecognition

end

end OAI
