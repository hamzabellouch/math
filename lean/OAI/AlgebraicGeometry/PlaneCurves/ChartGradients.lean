import OAI.AlgebraicGeometry.PlaneCurves.MovingConfigurations
import OAI.AlgebraicGeometry.PlaneCurves.NormalSpecialization

namespace OAI

/-!
# Direct and normalized gradients in smooth cubic charts
-/

section

noncomputable section
namespace Nagata.Workers.W25
open scoped BigOperators

/-- The affine partial derivative is the dehomogenized surviving ambient partial. -/
theorem pderiv_directChartHom (c : Fin 3) (G : MvPolynomial (Fin 3) ℂ) (i : Fin 2) :
    MvPolynomial.pderiv i (Nagata.W27.directChartHom c G) =
      Nagata.W27.directChartHom c (MvPolynomial.pderiv (c.succAbove i) G) := by
  classical
  let f := Fin.insertNth (α := fun _ : Fin 3 => MvPolynomial (Fin 2) ℂ) c 1 MvPolynomial.X
  have hderiv (j : Fin 3) : MvPolynomial.pderiv i (f j) =
      if j = c.succAbove i then 1 else 0 := by
    by_cases hj : j = c
    · subst j
      simp [f]
    · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
      simp [f, MvPolynomial.pderiv_X, Pi.single_apply, eq_comm]
  change MvPolynomial.pderiv i (MvPolynomial.eval₂ MvPolynomial.C f G) =
    MvPolynomial.eval₂ MvPolynomial.C f (MvPolynomial.pderiv (c.succAbove i) G)
  rw [Nagata.Workers.W14.pderiv_polynomial_substitution]
  simp_rw [hderiv, mul_ite, mul_one, mul_zero]
  simp

/-- Exact derivative scaling between a cone representative and its normalized chart. -/
theorem eval_pderiv_directChartHom_scale {G : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hG : G.IsHomogeneous d) (c : Fin 3) (x : Fin 3 → ℂ) (hc : x c ≠ 0) (i : Fin 2) :
    MvPolynomial.eval x (MvPolynomial.pderiv (c.succAbove i) G) =
      (x c) ^ (d - 1) * MvPolynomial.eval (fun j => x (c.succAbove j) / x c)
        (MvPolynomial.pderiv i (Nagata.W27.directChartHom c G)) := by
  rw [pderiv_directChartHom, Nagata.Workers.W17.eval_directChartHom]
  have hscale := Nagata.W16.homogeneous_eval_scale (hG.pderiv (i := c.succAbove i))
    (Fin.insertNth (α := fun _ : Fin 3 => ℂ) c 1 (fun j => x (c.succAbove j) / x c)) (x c)
  have hnorm : (fun a => x c * Fin.insertNth (α := fun _ : Fin 3 => ℂ) c 1
      (fun j => x (c.succAbove j) / x c) a) = x :=
    Nagata.Workers.W17.scaled_chart_vector c x hc
  rw [hnorm] at hscale
  exact hscale

/-- Every projective affine chart containing a nonsingular point has a nonzero
ordinary two-coordinate affine gradient. Euler's identity rules out the omitted
ambient partial being the only nonzero derivative. -/
theorem exists_nonzero_pderiv_directChartHom {G : MvPolynomial (Fin 3) ℂ} {d : ℕ}
    (hG : G.IsHomogeneous d) (c : Fin 3) (x : Fin 3 → ℂ)
    (hc : x c ≠ 0) (hzero : MvPolynomial.eval x G = 0)
    (hgrad : ∃ j : Fin 3, MvPolynomial.eval x (MvPolynomial.pderiv j G) ≠ 0) :
    ∃ i : Fin 2, MvPolynomial.eval (fun j => x (c.succAbove j) / x c)
      (MvPolynomial.pderiv i (Nagata.W27.directChartHom c G)) ≠ 0 := by
  classical
  by_contra h
  have haff (i : Fin 2) : MvPolynomial.eval (fun j => x (c.succAbove j) / x c)
      (MvPolynomial.pderiv i (Nagata.W27.directChartHom c G)) = 0 := by
    by_contra hi
    exact h ⟨i, hi⟩
  have hamb (i : Fin 2) : MvPolynomial.eval x (MvPolynomial.pderiv (c.succAbove i) G) = 0 := by
    rw [eval_pderiv_directChartHom_scale hG c x hc i, haff, mul_zero]
  have heuler := congrArg (MvPolynomial.eval x) hG.sum_X_mul_pderiv
  simp only [map_sum, map_mul, MvPolynomial.eval_X, map_nsmul, hzero, nsmul_zero] at heuler
  have hsum : (∑ j : Fin 3, x j * MvPolynomial.eval x (MvPolynomial.pderiv j G)) =
      x c * MvPolynomial.eval x (MvPolynomial.pderiv c G) := by
    apply Finset.sum_eq_single c
    · intro j _ hj
      obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hj
      rw [hamb, mul_zero]
    · simp
  have hcderiv : MvPolynomial.eval x (MvPolynomial.pderiv c G) = 0 :=
    (mul_eq_zero.mp (hsum.symm.trans heuler)).resolve_left hc
  obtain ⟨j, hj⟩ := hgrad
  by_cases hjc : j = c
  · subst j
    exact hj hcderiv
  · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hjc
    exact hj (hamb i)

end Nagata.Workers.W25

end
end

section

namespace Nagata.Workers.W25
open Nagata.Workers.W28

theorem planePolynomialEval_normalizedCurvePoint (P : MvPolynomial (Fin 2) ℂ)
    (X : Fin 3 → ℂ → ℂ) (c : Fin 3) (z : ℂ) :
    planePolynomialEval P (normalizedCurvePoint X c z) =
      MvPolynomial.eval (fun i => X (c.succAbove i) z / X c z) P := by
  apply congrArg (fun v : Fin 2 → ℂ => MvPolynomial.eval v P)
  funext i
  fin_cases i <;> rfl

/-- Every containing direct chart satisfies the exact smoothness input to the
coordinate-independent normal-polynomial construction. -/
theorem normalizedCurvePoint_gradient_ne_zero
    {G : MvPolynomial (Fin 3) ℂ} {d : ℕ} (hG : G.IsHomogeneous d)
    (c : Fin 3) (X : Fin 3 → ℂ → ℂ) (z : ℂ) (hc : X c z ≠ 0)
    (hzero : MvPolynomial.eval (fun j => X j z) G = 0)
    (hgrad : ∃ j : Fin 3, MvPolynomial.eval (fun i => X i z) (MvPolynomial.pderiv j G) ≠ 0) :
    polynomialGradient (Nagata.W27.directChartHom c G) (normalizedCurvePoint X c z) ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_nonzero_pderiv_directChartHom hG c (fun j => X j z) hc hzero hgrad
  apply (polynomialGradient_ne_zero_iff_partials _ _).mpr
  fin_cases i
  · left
    rwa [planePolynomialEval_normalizedCurvePoint]
  · right
    rwa [planePolynomialEval_normalizedCurvePoint]

end Nagata.Workers.W25

end

end OAI
