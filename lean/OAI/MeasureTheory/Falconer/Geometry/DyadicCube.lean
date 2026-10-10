import OAI.MeasureTheory.Falconer.Estimates.AllDimensions
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# Dyadic cubes in the ambient dimension of the manuscript

Half-open cubes partition without boundary overlaps. Their centers and
Euclidean diameter bounds use the same original ambient coordinates as the
distance measure.
-/

namespace Falconer
open Set MeasureTheory

structure DyadicCube (d : ℕ) where
  origin : Space d
  side : ℝ

def DyadicCube.carrier {d : ℕ} (Q : DyadicCube d) : Set (Space d) :=
  {x | ∀ i, Q.origin i ≤ x i ∧ x i < Q.origin i + Q.side}

noncomputable def DyadicCube.child {d : ℕ} (Q : DyadicCube d) (b : Fin d → Bool) : DyadicCube d where
  origin := WithLp.toLp 2 (fun i => Q.origin i + if b i then Q.side / 2 else 0)
  side := Q.side / 2

noncomputable def DyadicCube.center {d : ℕ} (Q : DyadicCube d) : Space d :=
  WithLp.toLp 2 (fun i => Q.origin i + Q.side / 2)

theorem DyadicCube.measurable {d : ℕ} (Q : DyadicCube d) : MeasurableSet Q.carrier := by
  simp only [carrier, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_le measurable_const (EuclideanSpace.proj i).continuous.measurable).inter
    (measurableSet_lt (EuclideanSpace.proj i).continuous.measurable measurable_const)

theorem DyadicCube.child_subset {d : ℕ} (Q : DyadicCube d)
    (b : Fin d → Bool) : (Q.child b).carrier ⊆ Q.carrier := by
  intro x hx i
  have hh := hx i
  cases h : b i <;> simp only [child, PiLp.toLp_apply, h, Bool.false_eq_true,
    ite_false, ite_true, add_zero] at hh <;>
    constructor <;> linarith

theorem DyadicCube.cover_children {d : ℕ} (Q : DyadicCube d) :
    Q.carrier = ⋃ b : Fin d → Bool, (Q.child b).carrier := by
  classical
  apply subset_antisymm
  · intro x hx
    let b : Fin d → Bool := fun i => decide (Q.origin i + Q.side / 2 ≤ x i)
    apply mem_iUnion.mpr
    refine ⟨b, ?_⟩
    intro i
    have hi := hx i
    by_cases h : Q.origin i + Q.side / 2 ≤ x i
    · simp only [child, b, h, decide_true, ite_true, PiLp.toLp_apply]
      exact ⟨trivial, by linarith⟩
    · simp only [child, b, h, decide_false, Bool.false_eq_true, ite_false,
        PiLp.toLp_apply, add_zero]
      exact ⟨hi.1, lt_of_not_ge h⟩
  · exact iUnion_subset fun b => Q.child_subset b

theorem DyadicCube.children_disjoint {d : ℕ} (Q : DyadicCube d)
    {b b' : Fin d → Bool} (hne : b ≠ b') :
    Disjoint (Q.child b).carrier (Q.child b').carrier := by
  classical
  have hex : ∃ i, b i ≠ b' i := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨i, hi⟩ := hex
  apply Set.disjoint_left.mpr
  intro x hx hx'
  have h0 := hx i
  have h1 := hx' i
  cases hb : b i <;> cases hb' : b' i <;>
    simp_all only [child, PiLp.toLp_apply, Bool.false_eq_true,
      ite_false, ite_true, add_zero, ne_eq, not_true_eq_false] <;> linarith

theorem DyadicCube.center_mem {d : ℕ} (Q : DyadicCube d) (hQ : 0 < Q.side) :
    Q.center ∈ Q.carrier := by
  intro i
  change Q.origin i ≤ Q.origin i + Q.side / 2 ∧
    Q.origin i + Q.side / 2 < Q.origin i + Q.side
  constructor <;> linarith

/-- The cube diameter estimate used when choosing a same-ancestor witness. -/
theorem DyadicCube.dist_le {d : ℕ} (Q : DyadicCube d) (hQ : 0 ≤ Q.side)
    {x y : Space d} (hx : x ∈ Q.carrier) (hy : y ∈ Q.carrier) :
    dist x y ≤ Real.sqrt d * Q.side := by
  have hc (i : Fin d) : |x i - y i| ≤ Q.side := by
    have hxi := hx i
    have hyi := hy i
    rw [abs_le]
    constructor <;> linarith
  have hs := EuclideanSpace.dist_sq_eq x y
  have hb : ∑ i : Fin d, dist (x i) (y i)^2 ≤ (d : ℝ) * Q.side^2 := by
    calc
      _ ≤ ∑ _i : Fin d, Q.side^2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [Real.dist_eq]
        exact (sq_le_sq₀ (abs_nonneg _) hQ).mpr (hc i)
      _ = _ := by simp
  have hroot := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)
  rw [← hs] at hb
  have hprod : 0 ≤ Real.sqrt (d : ℝ) * Q.side := mul_nonneg (Real.sqrt_nonneg _) hQ
  nlinarith [dist_nonneg (x := x) (y := y)]

end Falconer

end OAI
