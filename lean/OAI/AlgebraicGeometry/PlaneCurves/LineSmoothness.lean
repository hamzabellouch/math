import Mathlib.Algebra.Polynomial.Derivative
import OAI.AlgebraicGeometry.PlaneCurves.LineConfigurations
import OAI.AlgebraicGeometry.PlaneCurves.LineRestriction

namespace OAI

/-!
# Smooth points and gradients of line arrangements
-/

section

/-!
# Partial-derivative certificates at the explicit line-arrangement marks

The ambient ring is the genuine iterated polynomial ring K[U][Y].
The Y-partial derivative is the ordinary derivative in the outer variable.
We prove its evaluation is a product of nonzero other-component factors.
This gives an explicit hypersurface nonsingularity certificate, without an
assumed smoothness predicate or an asserted geometric bridge.
-/
noncomputable section
namespace Nagata.W06.LineArrangement
open Polynomial
open scoped BigOperators

/-- Evaluation of an actual bivariate polynomial at affine coordinates (U,Y). -/
def planeEval {K : Type*} [CommRing K] (P : Polynomial (Polynomial K)) (U Y : K) : K :=
  P.eval₂ (Polynomial.evalRingHom U) Y

/-- Product-rule identity at a chosen root, valid before any nonvanishing assumption. -/
theorem derivative_prod_eval₂_root {A B ι : Type*} [CommRing A] [CommRing B]
    [Fintype ι] [DecidableEq ι] (f : A →+* B) (a : ι → A) (i : ι) :
    (∏ j : ι, (X - C (a j))).derivative.eval₂ f (f (a i)) =
      ∏ j ∈ Finset.univ.erase i, (f (a i) - f (a j)) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun j => (X - C (a j))) (Finset.mem_univ i)]
  simp only [derivative_mul, derivative_X_sub_C, eval₂_add, eval₂_mul,
    eval₂_sub, eval₂_X, eval₂_C, sub_self, zero_mul, one_mul,
    add_zero, eval₂_finsetProd]

variable {K : Type*} [Field K]

@[simp] theorem eval_affineLineGraph (i : ℕ) (U : K) :
    (Nagata.Workers.W24.affineLineGraph K i).eval U = graphValue i U := by
  simp [Nagata.Workers.W24.affineLineGraph, graphValue]

/-- The actual reduced curve equation evaluates to the product of its line equations. -/
theorem planeEval_lineUnion (k : ℕ) (U Y : K) :
    planeEval (Nagata.Workers.W24.lineUnionEquation K k) U Y =
      ∏ i : Fin k, lineValue i.val U Y := by
  unfold planeEval Nagata.Workers.W24.lineUnionEquation
  rw [eval₂_finsetProd]
  apply Finset.prod_congr rfl
  intro i hi
  rw [eval₂_sub, eval₂_X, eval₂_C]
  change Y - (Nagata.Workers.W24.affineLineGraph K i.val).eval U = lineValue i.val U Y
  rw [eval_affineLineGraph]
  rfl

/-- Each of the displayed marked points lies on the actual reduced curve equation. -/
theorem lineUnion_zero_at_mark (k : ℕ) (i s : Fin k) :
    planeEval (Nagata.Workers.W24.lineUnionEquation K k)
      (markedPoint K k i s).1 (markedPoint K k i s).2 = 0 := by
  rw [planeEval_lineUnion]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (markedPoint_on_line k i s)

variable [CharZero K]

/-- At any negative-U point on component i, the Y-partial derivative of the entire
line union is nonzero. All the other line factors are nonzero there. -/
theorem partialY_lineUnion_negative_mark (k : ℕ) (i : Fin k) (v : ℕ) (hv : 0 < v) :
    planeEval (Nagata.Workers.W24.lineUnionEquation K k).derivative
      (-(v : K)) (graphValue i.val (-(v : K))) ≠ 0 := by
  have hgraph : Polynomial.evalRingHom (-(v : K))
      (Nagata.Workers.W24.affineLineGraph K i.val) = graphValue i.val (-(v : K)) := by
    exact eval_affineLineGraph i.val _
  unfold planeEval Nagata.Workers.W24.lineUnionEquation
  rw [← hgraph]
  rw [derivative_prod_eval₂_root (Polynomial.evalRingHom (-(v : K)))
    (fun j : Fin k => Nagata.Workers.W24.affineLineGraph K j.val) i]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hij : i.val ≠ j.val := by
    intro h
    exact (Finset.mem_erase.mp hj).1 (Fin.ext h).symm
  change (Nagata.Workers.W24.affineLineGraph K i.val).eval (-(v : K)) -
    (Nagata.Workers.W24.affineLineGraph K j.val).eval (-(v : K)) ≠ 0
  rw [eval_affineLineGraph, eval_affineLineGraph]
  exact negative_mark_avoids_other_line (K := K) i.val j.val v hij hv

/-- The concrete nonzero Y-partial derivative at every one of the k² marks. -/
theorem partialY_lineUnion_at_mark (k : ℕ) (i s : Fin k) :
    planeEval (Nagata.Workers.W24.lineUnionEquation K k).derivative
      (markedPoint K k i s).1 (markedPoint K k i s).2 ≠ 0 := by
  exact partialY_lineUnion_negative_mark k i (markedCoordinate k i.val s)
    (markedCoordinate_pos k i.val s)

/-- A genuine equation/derivative nonsingularity certificate for all marked points. -/
theorem markedPoint_nonsingular_certificate (k : ℕ) (i s : Fin k) :
    planeEval (Nagata.Workers.W24.lineUnionEquation K k)
        (markedPoint K k i s).1 (markedPoint K k i s).2 = 0 ∧
      planeEval (Nagata.Workers.W24.lineUnionEquation K k).derivative
        (markedPoint K k i s).1 (markedPoint K k i s).2 ≠ 0 :=
  ⟨lineUnion_zero_at_mark k i s, partialY_lineUnion_at_mark k i s⟩

/-- The explicit k²-point configuration with its actual hypersurface certificates.
The formula is valid for every k, in particular every k≥4. -/
theorem line_arrangement_marked_configuration (k : ℕ) :
    (markedPoints K k).card = k ^ 2 ∧
      ∀ p ∈ markedPoints K k,
        planeEval (Nagata.Workers.W24.lineUnionEquation K k) p.1 p.2 = 0 ∧
        planeEval (Nagata.Workers.W24.lineUnionEquation K k).derivative p.1 p.2 ≠ 0 := by
  classical
  refine ⟨card_markedPoints k, ?_⟩
  intro p hp
  obtain ⟨⟨i, s⟩, _, rfl⟩ := Finset.mem_image.mp hp
  exact markedPoint_nonsingular_certificate k i s

/-- The extra point is also on the actual curve and has nonzero Y-partial derivative. -/
theorem additionalPoint_nonsingular_certificate (k : ℕ) (hk : 0 < k) :
    planeEval (Nagata.Workers.W24.lineUnionEquation K k)
        (additionalPoint K k).1 (additionalPoint K k).2 = 0 ∧
      planeEval (Nagata.Workers.W24.lineUnionEquation K k).derivative
        (additionalPoint K k).1 (additionalPoint K k).2 ≠ 0 := by
  constructor
  · rw [planeEval_lineUnion]
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨0, hk⟩ : Fin k)) (additionalPoint_on_zero k)
  · simpa [additionalPoint, graphValue] using
      partialY_lineUnion_negative_mark (K := K) k ⟨0, hk⟩ (k + 2) (by omega)

/-- Every target scalar of the actual vertical polynomial differential at the extra point is attained. -/
theorem exists_vertical_displacement_scalar (k : ℕ) (hk : 0 < k) (c : K) :
    ∃ t : K,
      planeEval (Nagata.Workers.W24.lineUnionEquation K k).derivative
        (additionalPoint K k).1 (additionalPoint K k).2 * t = c := by
  have h := (additionalPoint_nonsingular_certificate (K := K) k hk).2
  refine ⟨c / planeEval (Nagata.Workers.W24.lineUnionEquation K k).derivative
    (additionalPoint K k).1 (additionalPoint K k).2, ?_⟩
  exact mul_div_cancel₀ c h

/-- The complete k²+1 configuration, including the extra point required by the triangle case. -/
theorem line_arrangement_with_additional_point (k : ℕ) (hk : 0 < k) :
    (extendedMarkedPoints K k).card = k ^ 2 + 1 ∧
      ∀ p ∈ extendedMarkedPoints K k,
        planeEval (Nagata.Workers.W24.lineUnionEquation K k) p.1 p.2 = 0 ∧
        planeEval (Nagata.Workers.W24.lineUnionEquation K k).derivative p.1 p.2 ≠ 0 := by
  classical
  refine ⟨card_insert_additionalPoint k, ?_⟩
  intro p hp
  change p ∈ insert (additionalPoint K k) (markedPoints K k) at hp
  rcases Finset.mem_insert.mp hp with hp | hp
  · subst p
    exact additionalPoint_nonsingular_certificate k hk
  · exact (line_arrangement_marked_configuration k).2 p hp

end Nagata.W06.LineArrangement

end
end

end OAI
