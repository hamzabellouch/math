import OAI.Combinatorics.ContingencyTables.Dense.DenseWeights
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace OAI

/-!
# The softened affine feasibility penalty

The dense sampler uses the maximum of zero and the negatives of its
normalized affine table entries, minus a fixed slack. This actual penalty
is continuous and convex. Its change bound is proved from the entry
coefficients, including the dependent row and column entries.
-/

namespace ContingencyTables.AffinePenalty

open scoped BigOperators

variable {I G : Type*} [Fintype I] [Fintype G]

def affineValue (offset : ℝ) (coeff : I → ℝ) (x : I → ℝ) : ℝ :=
  offset + ∑ j, coeff j * x j

theorem affineValue_combine (offset : ℝ) (coeff : I → ℝ) (x y : I → ℝ)
    (a b : ℝ) (hab : a + b = 1) :
    affineValue offset coeff (a • x + b • y) =
      a * affineValue offset coeff x + b * affineValue offset coeff y := by
  simp only [affineValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    mul_add, Finset.sum_add_distrib]
  simp_rw [mul_left_comm (coeff _) a, mul_left_comm (coeff _) b,
    ← Finset.mul_sum]
  nlinarith [congrArg (fun z => z * offset) hab]

theorem affineValue_change (offset : ℝ) (coeff : I → ℝ) (x y : I → ℝ)
    (c r : ℝ) (hc : 0 ≤ c) (hcoeff : ∀ j, |coeff j| ≤ c)
    (hxy : ∀ j, |x j - y j| ≤ r) :
    |affineValue offset coeff x - affineValue offset coeff y| ≤
      Fintype.card I * c * r := by
  have heq : affineValue offset coeff x - affineValue offset coeff y =
      ∑ j, coeff j * (x j - y j) := by
    simp [affineValue, mul_sub, Finset.sum_sub_distrib]
  rw [heq]
  calc
    _ ≤ ∑ j, |coeff j * (x j - y j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : I, c * r := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hcoeff j) (hxy j) (abs_nonneg _) hc
    _ = _ := by simp; ring

def component (offset : G → ℝ) (coeff : G → I → ℝ) (slack : ℝ) :
    Option G → (I → ℝ) → ℝ
  | none, _ => 0
  | some g, x => -affineValue (offset g) (coeff g) x - slack

noncomputable def penalty (offset : G → ℝ) (coeff : G → I → ℝ)
    (slack : ℝ) (x : I → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun g : Option G => component offset coeff slack g x)

theorem component_le_penalty (offset : G → ℝ) (coeff : G → I → ℝ)
    (slack : ℝ) (x : I → ℝ) (g : Option G) :
    component offset coeff slack g x ≤ penalty offset coeff slack x := by
  unfold penalty
  exact Finset.le_sup' (fun g : Option G => component offset coeff slack g x) (Finset.mem_univ g)

theorem penalty_nonnegative (offset : G → ℝ) (coeff : G → I → ℝ)
    (slack : ℝ) (x : I → ℝ) : 0 ≤ penalty offset coeff slack x :=
  component_le_penalty offset coeff slack x none

omit [Fintype G] in
private theorem component_combine (offset : G → ℝ) (coeff : G → I → ℝ)
    (slack : ℝ) (g : Option G) (x y : I → ℝ) (a b : ℝ) (hab : a + b = 1) :
    component offset coeff slack g (a • x + b • y) =
      a * component offset coeff slack g x + b * component offset coeff slack g y := by
  cases g with
  | none => simp [component]
  | some g =>
    simp only [component, affineValue_combine _ _ _ _ _ _ hab]
    nlinarith [congrArg (fun z => z * slack) hab]

theorem penalty_convex (offset : G → ℝ) (coeff : G → I → ℝ) (slack : ℝ)
    (K : Set (I → ℝ)) (hK : Convex ℝ K) :
    ConvexOn ℝ K (penalty offset coeff slack) := by
  refine ⟨hK, ?_⟩
  intro x _ y _ a b ha hb hab
  apply Finset.sup'_le
  intro g _
  rw [component_combine offset coeff slack g x y a b hab]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (component_le_penalty offset coeff slack x g) ha)
    (mul_le_mul_of_nonneg_left (component_le_penalty offset coeff slack y g) hb)

omit [Fintype G] in
private theorem component_change (offset : G → ℝ) (coeff : G → I → ℝ)
    (slack : ℝ) (g : Option G) (x y : I → ℝ) (c r : ℝ)
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hcoeff : ∀ g j, |coeff g j| ≤ c)
    (hxy : ∀ j, |x j - y j| ≤ r) :
    |component offset coeff slack g x - component offset coeff slack g y| ≤
      Fintype.card I * c * r := by
  cases g with
  | none => simp only [component, sub_self, abs_zero]; positivity
  | some g =>
    have heq : component offset coeff slack (some g) x -
        component offset coeff slack (some g) y =
        -(affineValue (offset g) (coeff g) x - affineValue (offset g) (coeff g) y) := by
      simp only [component]
      ring
    rw [heq, abs_neg]
    exact affineValue_change _ _ _ _ c r hc (hcoeff g) hxy

private theorem penalty_sub_le (offset : G → ℝ) (coeff : G → I → ℝ)
    (slack : ℝ) (x y : I → ℝ) (c r : ℝ)
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hcoeff : ∀ g j, |coeff g j| ≤ c)
    (hxy : ∀ j, |x j - y j| ≤ r) :
    penalty offset coeff slack x ≤ penalty offset coeff slack y + Fintype.card I * c * r := by
  apply Finset.sup'_le
  intro g _
  have h := (abs_le.mp (component_change offset coeff slack g x y c r hc hr hcoeff hxy)).2
  linarith [component_le_penalty offset coeff slack y g]

theorem penalty_change (offset : G → ℝ) (coeff : G → I → ℝ)
    (slack : ℝ) (x y : I → ℝ) (c r : ℝ)
    (hc : 0 ≤ c) (hr : 0 ≤ r) (hcoeff : ∀ g j, |coeff g j| ≤ c)
    (hxy : ∀ j, |x j - y j| ≤ r) :
    |penalty offset coeff slack x - penalty offset coeff slack y| ≤ Fintype.card I * c * r := by
  apply abs_le.mpr
  constructor
  · have h := penalty_sub_le offset coeff slack y x c r hc hr hcoeff
      (fun j => by simpa [abs_sub_comm] using hxy j)
    linarith
  · linarith [penalty_sub_le offset coeff slack x y c r hc hr hcoeff hxy]

theorem penalty_continuous (offset : G → ℝ) (coeff : G → I → ℝ) (slack : ℝ) :
    Continuous (penalty offset coeff slack) := by
  apply Continuous.finset_sup'_apply
  intro g _
  cases g with
  | none => exact continuous_const
  | some g =>
    exact (continuous_const.add (continuous_finsetSum Finset.univ
      (fun j _ => continuous_const.mul (continuous_apply j)))).neg.sub continuous_const

end ContingencyTables.AffinePenalty

end OAI
