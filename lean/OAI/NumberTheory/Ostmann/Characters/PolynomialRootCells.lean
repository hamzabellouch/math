import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Sort
import Mathlib.Topology.Algebra.Polynomial
import OAI.NumberTheory.Ostmann.Characters.MonotoneWeightVariation

namespace OAI

/-! # The root cells used to split the long-variable weights

A cell records the side of each real root, retaining the roots themselves as
separate cells. Polynomial inequalities are constant on a cell; polynomial
arguments are monotone when the derivative roots are included among the cuts.
-/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def rootCellCode (S : Finset ℝ) (x : ℝ) : S → Ordering :=
  fun r => compare x r.val

theorem rootCellCode_convex (S : Finset ℝ) {x y z : ℝ}
    (hxy : x ≤ y) (hyz : y ≤ z) (hcode : rootCellCode S x = rootCellCode S z) :
    rootCellCode S y = rootCellCode S x := by
  funext r
  have he := congrFun hcode r
  change compare x r.val = compare z r.val at he
  change compare y r.val = compare x r.val
  rcases lt_trichotomy x r.val with hx | hx | hx
  · have hz : z < r.val := compare_lt_iff_lt.mp (he.symm.trans (compare_lt_iff_lt.mpr hx))
    rw [compare_lt_iff_lt.mpr (hyz.trans_lt hz), compare_lt_iff_lt.mpr hx]
  · have hz : z = r.val := compare_eq_iff_eq.mp (he.symm.trans (compare_eq_iff_eq.mpr hx))
    have hy : y = r.val := le_antisymm (hyz.trans_eq hz) (hx ▸ hxy)
    rw [compare_eq_iff_eq.mpr hy, compare_eq_iff_eq.mpr hx]
  · have hy : r.val < y := hx.trans_le hxy
    rw [compare_gt_iff_gt.mpr hy, compare_gt_iff_gt.mpr hx]

theorem rootCellCode_no_root_between (S : Finset ℝ) {x y : ℝ}
    (hxy : x < y) (hcode : rootCellCode S x = rootCellCode S y) :
    ∀ r ∈ S, r ∉ Set.Icc x y := by
  intro r hr hrange
  have he := congrFun hcode ⟨r, hr⟩
  change compare x r = compare y r at he
  rcases lt_or_eq_of_le hrange.1 with hxr | hxr
  · have hyr : y < r := compare_lt_iff_lt.mp (he.symm.trans (compare_lt_iff_lt.mpr hxr))
    linarith [hrange.2]
  · have hyr : y = r := compare_eq_iff_eq.mp (he.symm.trans (compare_eq_iff_eq.mpr hxr))
    linarith

/-- A continuous real function with no zeros on an interval has one sign. -/
theorem continuous_sign_on_interval (f : ℝ → ℝ) (a b : ℝ)
    (hf : ContinuousOn f (Set.Ioo a b)) (hn : ∀ x ∈ Set.Ioo a b, f x ≠ 0) :
    (∀ x ∈ Set.Ioo a b, 0 ≤ f x) ∨ (∀ x ∈ Set.Ioo a b, f x ≤ 0) := by
  by_cases hpos : ∀ x ∈ Set.Ioo a b, 0 ≤ f x
  · exact Or.inl hpos
  · right
    push Not at hpos
    obtain ⟨x, hx, hfx⟩ := hpos
    intro y hy
    by_contra hfy
    have hfy' : 0 < f y := lt_of_not_ge hfy
    obtain ⟨z, hz, hfz⟩ := isPreconnected_Ioo.intermediate_value hx hy hf
      (show (0 : ℝ) ∈ Set.Icc (f x) (f y) from ⟨hfx.le, hfy'.le⟩)
    exact hn z hz hfz

theorem polynomial_monotoneOn_of_root_cell (P : Polynomial ℝ) (S : Finset ℝ)
    (hroots : ∀ r ∈ P.derivative.roots, r ∈ S) {a b : ℝ}
    (hcode : rootCellCode S a = rootCellCode S b) :
    MonotoneOn P.eval (Set.Icc a b) ∨ AntitoneOn P.eval (Set.Icc a b) := by
  by_cases hd : P.derivative = 0
  · left
    have hp := Polynomial.eq_C_of_derivative_eq_zero hd
    intro x hx y hy hxy
    have hv (t : ℝ) : P.eval t = P.coeff 0 := by
      have hh := congrArg (fun Q : Polynomial ℝ => Q.eval t) hp
      simpa only [Polynomial.eval_C] using hh
    change P.eval x ≤ P.eval y
    rw [hv x, hv y]
  · have hn : ∀ x ∈ Set.Ioo a b, P.derivative.eval x ≠ 0 := by
      intro x hx hz
      have hm : x ∈ P.derivative.roots := (Polynomial.mem_roots hd).mpr hz
      exact rootCellCode_no_root_between S (hx.1.trans hx.2) hcode x (hroots x hm)
        ⟨hx.1.le, hx.2.le⟩
    rcases continuous_sign_on_interval P.derivative.eval a b
        P.derivative.continuous.continuousOn hn with hpos | hneg
    · left
      apply monotoneOn_of_deriv_nonneg (convex_Icc a b) P.continuous.continuousOn
        P.differentiable.differentiableOn
      intro x hx
      rw [interior_Icc] at hx
      simpa only [P.deriv] using hpos x hx
    · right
      apply antitoneOn_of_deriv_nonpos (convex_Icc a b) P.continuous.continuousOn
        P.differentiable.differentiableOn
      intro x hx
      rw [interior_Icc] at hx
      simpa only [P.deriv] using hneg x hx

/-- Even the crude count of all codes is exponential only in the total degree,
as required by the eventual exp(poly(m)) weight bound. Empty cells cost nothing. -/
theorem rootCellCode_card (S : Finset ℝ) :
    Fintype.card (S → Ordering) = 3 ^ S.card := by
  have ho : Fintype.card Ordering = 3 := by decide
  simp [ho]

noncomputable def polynomialRootCuts {I : Type*} [Fintype I]
    (P : I → Polynomial ℝ) : Finset ℝ :=
  Finset.univ.biUnion (fun i => (P i).roots.toFinset)

theorem polynomialRootCuts_card {I : Type*} [Fintype I] (P : I → Polynomial ℝ) :
    (polynomialRootCuts P).card ≤ ∑ i, (P i).natDegree := by
  apply (Finset.card_biUnion_le).trans
  apply Finset.sum_le_sum
  intro i _
  exact (P i).roots.toFinset_card_le.trans (P i).card_roots'

end Ostmann

end OAI
