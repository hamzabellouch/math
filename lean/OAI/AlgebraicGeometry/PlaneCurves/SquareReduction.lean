import OAI.AlgebraicGeometry.PlaneCurves.LineNormalData

namespace OAI

/-!
# Universal and very general square-configuration reduction
-/

section

/-! The strict square-case universal-system theorem for genuine plane forms
and ordinary projective chart multiplicities. -/
noncomputable section
namespace Nagata.Workers.W24
open Nagata.W06.LineArrangement

theorem marked_directChart_partial_ne_zero (k : ℕ) (i s : Fin k) :
    Nagata.Workers.W28.planePolynomialEval
      (MvPolynomial.pderiv 1 (Nagata.W27.directChartHom 2 (homogeneousLineUnion ℂ k)))
      (markedPoint ℂ k i s) ≠ 0 := by
  rw [directChart_union_eq_nestedToBivariate,
    Nagata.Workers.W14.planePolynomialEval_pderiv_one_nestedToBivariate]
  exact partialY_lineUnion_at_mark k i s

/-- Strict square-case degree bound, including all nonzero reducible and
nonreduced homogeneous equations in the genuine universal-system definition. -/
theorem square_universalSupport_degree_gt (k d m : ℕ) (hk : 4 ≤ k) (hm : 0 < m)
    (hU : Nagata.W13.UniversalSupport (k * k) d (fun _ => m)) : k * m < d := by
  by_contra hgt
  have hd : d ≤ k * m := by omega
  obtain ⟨c, hc⟩ := exists_square_normal_obstruction k hk
  let e : Fin (k * k) ≃ Fin k × Fin k := finProdFinEquiv.symm
  let line : Fin (k * k) → ℂ := fun b => ((e b).1.val : ℂ)
  let ξ : Fin (k * k) → ℂ := fun b => squareMarkedBase k (e b)
  let displacement : Fin (k * k) → ℂ := fun b => c (e b)
  have hbase : Function.Injective (fun b : Fin (k * k) =>
      (ξ b, (line b)^2 - line b * ξ b)) := by
    change Function.Injective (fun b => markedPoint ℂ k (e b).1 (e b).2)
    exact (markedPoint_injective k).comp e.injective
  have hline : ∀ b, Nagata.W04.ReducibleSquare.lineRestriction (line b)
      (homogeneousLineUnion ℂ k) = 0 := by
    intro b
    exact lineRestriction_union_zero k (e b).1
  have hpartial : ∀ b, Nagata.Workers.W28.planePolynomialEval
      (MvPolynomial.pderiv 1 (Nagata.W27.directChartHom 2 (homogeneousLineUnion ℂ k)))
      (ξ b, (line b)^2 - line b * ξ b) ≠ 0 := by
    intro b
    exact marked_directChart_partial_ne_zero k (e b).1 (e b).2
  obtain ⟨F, hhom, hweight, hne, horder⟩ :=
    Nagata.Workers.W17.universalSupport_line_normal_polynomial hU
      (homogeneousLineUnion ℂ k) k (homogeneousLineUnion_homogeneous k) (by omega)
      line ξ displacement hbase hline hpartial
  apply hc d m hm hd F hhom hweight hne
  intro p
  simpa only [line, ξ, displacement, Equiv.apply_symm_apply, planeNormalOnLine] using
    horder (e.symm p)

end Nagata.Workers.W24

end
end

section

noncomputable section
namespace Nagata.Workers.W24
open ProjectiveGeometry
open scoped BigOperators

/-- All unequal multiplicity vectors simultaneously satisfy the strict square
bound outside the one actual support exceptional union. -/
theorem square_strict_inequality_outside_supportExceptionalUnion
    (k : ℕ) (hk : 4 ≤ k) (p : OrderedDistinctPoints (k * k))
    (hp : p ∉ Nagata.W13.supportExceptionalUnion (k * k))
    (d : ℕ) (hd : 0 < d) (m : Fin (k * k) → ℕ)
    (F : MvPolynomial (Fin 3) ℂ) (hne : F ≠ 0) (hhom : F.IsHomogeneous d)
    (hmult : ∀ i, multiplicityAtLeast F (p.val i) (m i)) :
    (d : ℝ) * Real.sqrt ((k * k : ℕ) : ℝ) > ∑ i, (m i : ℝ) := by
  by_contra hbad
  have hle : (d : ℝ) * Real.sqrt ((k * k : ℕ) : ℝ) ≤ ∑ i, (m i : ℝ) := by
    exact le_of_not_gt hbad
  have hr : 0 < k * k := Nat.mul_pos (by omega) (by omega)
  obtain ⟨D, M, hD, hM, hslope, hU⟩ :=
    Nagata.W13.universalEqualSupport_of_violation hr hd hp ⟨F, hne, hhom, hmult⟩ hle
  have hDM : D ≤ k * M :=
    (Nagata.Workers.W14.square_ratio_le_iff (r := k * k) rfl hM).mp hslope
  exact (Nat.not_lt_of_ge hDM) (square_universalSupport_degree_gt k D M hk hM hU)

end Nagata.Workers.W24

end
end

end OAI
