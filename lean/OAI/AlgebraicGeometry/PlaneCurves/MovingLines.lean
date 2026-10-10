import OAI.AlgebraicGeometry.PlaneCurves.CoverNormal

namespace OAI

/-!
# Polynomial motion of smooth line configurations
-/

section

/-! Concrete chart-2 motions for the checked k²+n line-arrangement marks.
The same construction covers square k² (n=0) and every triangle r≥10 (k=3,
n=r-9). Normal displacements are arbitrary complex numbers. -/
noncomputable section
namespace Nagata.Workers.W14
open Nagata.W06.LineArrangement Nagata.ProjectiveGeometry

/-- The certified Y derivative of the actual reduced line-union equation. -/
def lineMarkYDerivative (k n : ℕ) (i : Fin (k * k + n)) : ℂ :=
  planeEval (Nagata.Workers.W24.lineUnionEquation ℂ k).derivative
    (orderedAffinePoint k n i).1 (orderedAffinePoint k n i).2

theorem lineMarkYDerivative_ne_zero (k n : ℕ) (hk : 0 < k)
    (i : Fin (k * k + n)) : lineMarkYDerivative k n i ≠ 0 :=
  (orderedAffinePoint_nonsingular k hk n i).2

/-- Explicit vertical velocity realizing the requested normal displacement. -/
def lineMarkVelocity (k n : ℕ) (displacement : Fin (k * k + n) → ℂ)
    (i : Fin (k * k + n)) : ℂ × ℂ :=
  (0, displacement i / lineMarkYDerivative k n i)

theorem lineMarkVelocity_normal (k n : ℕ) (hk : 0 < k)
    (displacement : Fin (k * k + n) → ℂ) (i : Fin (k * k + n)) :
    lineMarkYDerivative k n i * (lineMarkVelocity k n displacement i).2 = displacement i := by
  exact mul_div_cancel₀ _ (lineMarkYDerivative_ne_zero k n hk i)

theorem lineMarkVelocity_zero (k n : ℕ) (displacement : Fin (k * k + n) → ℂ)
    (i : Fin (k * k + n)) (hi : displacement i = 0) :
    lineMarkVelocity k n displacement i = 0 := by simp [lineMarkVelocity, hi]

/-- Actual coordinate polynomials of the explicit vertical affine motions. -/
def lineMarkCoordinateMotion (k n : ℕ) (displacement : Fin (k * k + n) → ℂ) :
    Fin (k * k + n) × Fin 2 → Polynomial ℂ :=
  fun ij => Polynomial.C (pairCoordinates (orderedAffinePoint k n ij.1) ij.2) +
    Polynomial.X * Polynomial.C (pairCoordinates (lineMarkVelocity k n displacement ij.1) ij.2)

theorem lineMarkCoordinateMotion_eval (k n : ℕ)
    (displacement : Fin (k * k + n) → ℂ) (s : ℂ) (i : Fin (k * k + n)) :
    (fun j => (lineMarkCoordinateMotion k n displacement (i, j)).eval s) =
      pairCoordinates (orderedAffinePoint k n i + s • lineMarkVelocity k n displacement i) := by
  funext j
  fin_cases j <;>
    simp only [lineMarkCoordinateMotion, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, pairCoordinates, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> rfl

theorem lineMarkCoordinateMotion_base (k n : ℕ)
    (displacement : Fin (k * k + n) → ℂ) :
    configurationChartEmbedding (fun _ => 2)
      (fun ij => (lineMarkCoordinateMotion k n displacement ij).eval 0) =
      (orderedProjectiveConfiguration k n).val := by
  funext i
  change chartPoint₂ 2 (fun j => (lineMarkCoordinateMotion k n displacement (i,j)).eval 0) = _
  rw [lineMarkCoordinateMotion_eval]
  simp only [zero_smul, add_zero]
  rfl

theorem lineMarkCoordinateMotion_base_injective (k n : ℕ)
    (displacement : Fin (k * k + n) → ℂ) :
    Function.Injective (configurationChartEmbedding (fun _ => 2)
      (fun ij => (lineMarkCoordinateMotion k n displacement ij).eval 0)) := by
  rw [lineMarkCoordinateMotion_base]
  exact (orderedProjectiveConfiguration k n).property

/-- Actual universal equations give a single genuine homogeneous polynomial
family at the explicit line marks, with every chart order valid for every s. -/
theorem universalSupport_line_motion_family {k n d : ℕ}
    {m : Fin (k * k + n) → ℕ}
    (hU : Nagata.W13.UniversalSupport (k * k + n) d m)
    (displacement : Fin (k * k + n) → ℂ) :
    ∃ S : Polynomial (MvPolynomial (Fin 3) ℂ),
      S.coeff 0 ≠ 0 ∧ (∀ α, (S.coeff α).IsHomogeneous d) ∧
      ∀ s i, Nagata.AffineMultiplicity.orderAtLeast
        (pairCoordinates (orderedAffinePoint k n i + s • lineMarkVelocity k n displacement i))
        (m i) (Nagata.W27.directChartHom 2 (S.eval (MvPolynomial.C s))) := by
  obtain ⟨S, hzero, hhom, horder⟩ := Nagata.Workers.W17.universalSupport_polynomial_family
    hU (fun _ => 2) (lineMarkCoordinateMotion k n displacement)
    (lineMarkCoordinateMotion_base_injective k n displacement)
  refine ⟨S, hzero, hhom, ?_⟩
  intro s i
  simpa only [lineMarkCoordinateMotion_eval] using horder s i

/-- Triangle displacement pattern: zero at all nine original marks and one
at each extra point. -/
def triangleDisplacement (n : ℕ) (i : Fin (3 * 3 + n)) : ℂ :=
  if i.val < 9 then 0 else 1

theorem triangleDisplacement_first_nine (n : ℕ) (i : Fin (3 * 3 + n))
    (hi : i.val < 9) : triangleDisplacement n i = 0 := by simp [triangleDisplacement, hi]

theorem triangleDisplacement_extra (n : ℕ) (i : Fin (3 * 3 + n))
    (hi : 9 ≤ i.val) : triangleDisplacement n i = 1 := by
  simp [triangleDisplacement, Nat.not_lt.mpr hi]

end Nagata.Workers.W14

end
end

end OAI
