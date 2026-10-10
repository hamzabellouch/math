import OAI.Combinatorics.DiscreteConvexity.Basic
import OAI.Combinatorics.DiscreteConvexity.CoordinateObservations
import OAI.Combinatorics.DiscreteConvexity.UnionBound
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring

namespace OAI

namespace TalagrandDiscreteConvexity

open scoped BigOperators

noncomputable section

/-- One coordinate receives label zero with the residual mass, and each of the
`L` row labels with mass `p`. This does not assert independence of the rows. -/
def labelLaw (L : ℕ) (p : ℝ) (hp : 0 ≤ p) (hLp : (L : ℝ) * p ≤ 1) :
    FiniteLaw (Fin (L + 1)) := by
  classical
  exact {
    weight := fun j => if j = 0 then 1 - (L : ℝ) * p else p
    nonneg := fun j => by
      split_ifs
      · exact sub_nonneg.mpr hLp
      · exact hp
    total := by
      rw [Fin.sum_univ_succ]
      simp [nsmul_eq_mul] }

@[simp] theorem labelLaw_weight_zero (L : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hLp : (L : ℝ) * p ≤ 1) :
    (labelLaw L p hp hLp).weight 0 = 1 - (L : ℝ) * p := by
  simp [labelLaw]

@[simp] theorem labelLaw_weight_succ (L : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hLp : (L : ℝ) * p ≤ 1) (j : Fin L) :
    (labelLaw L p hp hLp).weight j.succ = p := by
  simp [labelLaw]

@[simp] theorem labelLaw_prob_zero (L : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hLp : (L : ℝ) * p ≤ 1) :
    (labelLaw L p hp hLp).prob (fun j => j = 0) = 1 - (L : ℝ) * p := by
  classical
  unfold FiniteLaw.prob
  refine (Finset.sum_eq_single (0 : Fin (L + 1)) ?_ ?_).trans ?_
  · intro k _ hk
    exact ite_eq_right hk
  · simp
  · simp only [ite_true, labelLaw_weight_zero]

@[simp] theorem labelLaw_prob_succ (L : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hLp : (L : ℝ) * p ≤ 1) (j : Fin L) :
    (labelLaw L p hp hLp).prob (fun k => k = j.succ) = p := by
  classical
  unfold FiniteLaw.prob
  refine (Finset.sum_eq_single j.succ ?_ ?_).trans ?_
  · intro k _ hk
    exact ite_eq_right hk
  · simp
  · simp only [ite_true, labelLaw_weight_succ]

@[simp] theorem labelLaw_prob_nonzero (L : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hLp : (L : ℝ) * p ≤ 1) :
    (labelLaw L p hp hLp).prob (fun j => j ≠ 0) = (L : ℝ) * p := by
  have h := (labelLaw L p hp hLp).prob_compl (fun j => j = 0)
  simpa only [labelLaw_prob_zero, sub_sub_cancel] using h

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Independent coordinate labels; the row membership events may be dependent. -/
def labelSamples (L : ℕ) (p : ℝ) (hp : 0 ≤ p) (hLp : (L : ℝ) * p ≤ 1) :
    FiniteLaw (α → Fin (L + 1)) :=
  FiniteLaw.pi (fun _ : α => labelLaw L p hp hLp)

/-- Row `j` contains exactly the coordinates labeled by its successor label. -/
def labelRow {L : ℕ} (ω : α → Fin (L + 1)) (j : Fin L) : Finset α := by
  classical
  exact cubeSet (fun i => decide (ω i = j.succ))

omit [DecidableEq α] in
@[simp] theorem mem_labelRow {L : ℕ} {ω : α → Fin (L + 1)}
    {j : Fin L} {i : α} : i ∈ labelRow ω j ↔ ω i = j.succ := by
  classical
  simp [labelRow]

theorem labelUnion_eq_cubeSet_nonzero {L : ℕ} (ω : α → Fin (L + 1)) :
    unionTuple (labelRow ω) = cubeSet (fun i => decide (ω i ≠ 0)) := by
  classical
  ext i
  simp only [mem_unionTuple, mem_labelRow, mem_cubeSet, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj⟩
    rw [hj]
    exact Fin.succ_ne_zero j
  · intro hi
    exact Fin.eq_succ_of_ne_zero hi

/-- Every row has the full Bernoulli law, proved from independent coordinates. -/
theorem labelRow_prob_eq_mass (L : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hLp : (L : ℝ) * p ≤ 1) (j : Fin L) (s : Finset α) :
    (labelSamples L p hp hLp).prob (fun ω => labelRow ω j = s) =
      bernoulliMass p s := by
  classical
  have hobs (i : α) :
      (labelLaw L p hp hLp).prob (fun k => decide (k = j.succ) = true) = p := by
    simpa only [decide_eq_true_eq] using labelLaw_prob_succ L p hp hLp j
  simpa only [labelSamples, labelRow] using
    prob_pi_cubeSet_eq_mass (fun _ : α => labelLaw L p hp hLp)
      (fun _ k => decide (k = j.succ)) p hobs s

theorem labelRow_prob_mem_family (L : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hLp : (L : ℝ) * p ≤ 1) (j : Fin L) (D : Family α) :
    (labelSamples L p hp hLp).prob (fun ω => labelRow ω j ∈ D) =
      familyMeasure p D := by
  classical
  have hobs (i : α) :
      (labelLaw L p hp hLp).prob (fun k => decide (k = j.succ) = true) = p := by
    simpa only [decide_eq_true_eq] using labelLaw_prob_succ L p hp hLp j
  simpa only [labelSamples, labelRow] using
    prob_pi_cubeSet_mem_family (fun _ : α => labelLaw L p hp hLp)
      (fun _ k => decide (k = j.succ)) p hobs D

/-- The row union has the full Bernoulli law at the amplified density `L * p`. -/
theorem labelUnion_prob_eq_mass (L : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hLp : (L : ℝ) * p ≤ 1) (s : Finset α) :
    (labelSamples L p hp hLp).prob (fun ω => unionTuple (labelRow ω) = s) =
      bernoulliMass ((L : ℝ) * p) s := by
  classical
  have hobs (i : α) :
      (labelLaw L p hp hLp).prob (fun k => decide (k ≠ 0) = true) = (L : ℝ) * p := by
    simpa only [decide_eq_true_eq] using labelLaw_prob_nonzero L p hp hLp
  simpa only [labelSamples, labelUnion_eq_cubeSet_nonzero] using
    prob_pi_cubeSet_eq_mass (fun _ : α => labelLaw L p hp hLp)
      (fun _ k => decide (k ≠ 0)) ((L : ℝ) * p) hobs s

theorem labelUnion_prob_mem_family (L : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hLp : (L : ℝ) * p ≤ 1) (D : Family α) :
    (labelSamples L p hp hLp).prob (fun ω => unionTuple (labelRow ω) ∈ D) =
      familyMeasure ((L : ℝ) * p) D := by
  classical
  have hobs (i : α) :
      (labelLaw L p hp hLp).prob (fun k => decide (k ≠ 0) = true) = (L : ℝ) * p := by
    simpa only [decide_eq_true_eq] using labelLaw_prob_nonzero L p hp hLp
  simpa only [labelSamples, labelUnion_eq_cubeSet_nonzero] using
    prob_pi_cubeSet_mem_family (fun _ : α => labelLaw L p hp hLp)
      (fun _ k => decide (k ≠ 0)) ((L : ℝ) * p) hobs D

/-- Dependent rows give the density bound using only a union bound on failures.
The law of the rows and of their union is supplied by the explicit label coupling. -/
theorem familyMeasure_unionFamily_label_lower (L : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hLp : (L : ℝ) * p ≤ 1) (D : Family α) :
    1 - (L : ℝ) * (1 - familyMeasure p D) ≤
      familyMeasure ((L : ℝ) * p) (unionFamily L D) := by
  classical
  have hgood := FiniteLaw.prob_forall_ge_of_const
    (labelSamples (α := α) L p hp hLp)
    (fun (j : Fin L) ω => labelRow ω j ∈ D) (familyMeasure p D)
    (fun j => labelRow_prob_mem_family L p hp hLp j D)
  have hinclusion := (labelSamples (α := α) L p hp hLp).prob_mono
    (P := fun ω => ∀ j : Fin L, labelRow ω j ∈ D)
    (Q := fun ω => unionTuple (labelRow ω) ∈ unionFamily L D)
    (fun ω hω => mem_unionFamily.mpr ⟨labelRow ω, hω, rfl⟩)
  rw [labelUnion_prob_mem_family] at hinclusion
  simpa only [Fintype.card_fin] using hgood.trans hinclusion

end

end TalagrandDiscreteConvexity

end OAI
