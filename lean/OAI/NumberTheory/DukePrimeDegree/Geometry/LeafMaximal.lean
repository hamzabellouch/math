import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafSmallRadius
import Mathlib.MeasureTheory.Covering.Besicovitch

namespace OAI

/-!
# A covering estimate for leafwise bad sets

The relative maximal estimate used in EKL (2006), Section 4.3, rests on
the one-dimensional Besicovitch covering theorem. We first prove the
estimate for an arbitrary bounded family of witnessing radii. The measure
on the line is arbitrary; no doubling property is used.
-/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology ENNReal

namespace DukePrimeDegree

theorem real_ball_covering_estimate
    {N : ℕ} {τ : ℝ} (hτ : 1 < τ)
    (hN : IsEmpty (Besicovitch.SatelliteConfig ℝ N τ))
    (ν : Measure ℝ) (E : Set ℝ) (hE : MeasurableSet E)
    (c : ℝ≥0∞) (S : Set ℝ) (r : S → ℝ) (R : ℝ)
    (hrpos : ∀ x, 0 < r x) (hrle : ∀ x, r x ≤ R)
    (hbad : ∀ x : S, c * ν (closedBall x (r x)) ≤ ν (E ∩ closedBall x (r x))) :
    c * ν S ≤ (N : ℝ≥0∞) * ν E := by
  let q : Besicovitch.BallPackage S ℝ :=
    ⟨Subtype.val, r, hrpos, R, hrle⟩
  obtain ⟨F, hdisj, hcover⟩ := Besicovitch.exist_disjoint_covering_families hτ hN q
  have hcount (i : Fin N) : (F i).Countable := by
    apply (hdisj i).countable_of_nonempty_interior
    intro x hx
    exact ⟨x, (ball_subset_interior_closedBall (ε := r x)) (mem_ball_self (hrpos x))⟩
  have hcover' : S ⊆ ⋃ i : Fin N, ⋃ x ∈ F i, closedBall (x : ℝ) (r x) := by
    intro x hx
    have h := hcover ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp h
    obtain ⟨y, hy⟩ := mem_iUnion.mp hi
    obtain ⟨hyF, hyball⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨y,
      mem_iUnion.mpr ⟨hyF, ball_subset_closedBall hyball⟩⟩⟩
  have hfamily (i : Fin N) :
      c * ν (⋃ x ∈ F i, closedBall (x : ℝ) (r x)) ≤ ν E := by
    calc
      c * ν (⋃ x ∈ F i, closedBall (x : ℝ) (r x))
          ≤ c * ∑' x : F i, ν (closedBall ((x : S) : ℝ) (r x)) :=
        mul_le_mul' le_rfl (measure_biUnion_le ν (hcount i) _)
      _ = ∑' x : F i, c * ν (closedBall ((x : S) : ℝ) (r x)) :=
        (ENNReal.tsum_mul_left).symm
      _ ≤ ∑' x : F i, ν (E ∩ closedBall ((x : S) : ℝ) (r x)) :=
        ENNReal.tsum_le_tsum fun x => hbad x
      _ = ν (⋃ x ∈ F i, E ∩ closedBall (x : ℝ) (r x)) := by
        symm
        apply measure_biUnion (hcount i)
        · exact (hdisj i).mono fun _ => inter_subset_right
        · intro x hx
          exact hE.inter isClosed_closedBall.measurableSet
      _ ≤ ν E := measure_mono (by
        intro x hx
        obtain ⟨y, hy⟩ := mem_iUnion.mp hx
        obtain ⟨_, hxy⟩ := mem_iUnion.mp hy
        exact hxy.1)
  calc
    c * ν S ≤ c * ν (⋃ i : Fin N, ⋃ x ∈ F i, closedBall (x : ℝ) (r x)) :=
      mul_le_mul' le_rfl (measure_mono hcover')
    _ ≤ c * ∑ i : Fin N, ν (⋃ x ∈ F i, closedBall (x : ℝ) (r x)) :=
      mul_le_mul' le_rfl (measure_iUnion_fintype_le ν _)
    _ = ∑ i : Fin N, c * ν (⋃ x ∈ F i, closedBall (x : ℝ) (r x)) :=
      Finset.mul_sum ..
    _ ≤ ∑ _i : Fin N, ν E := Finset.sum_le_sum fun i _ => hfamily i
    _ = (N : ℝ≥0∞) * ν E := by simp

/-- A single finite constant controls every bounded-radius relative
maximal set on a real leaf, uniformly in the leaf measure. -/
theorem exists_real_relative_maximal_constant :
    ∃ N : ℕ, ∀ (ν : Measure ℝ) (E : Set ℝ), MeasurableSet E →
      ∀ (c : ℝ≥0∞) (R : ℝ),
      c * ν {x | ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
        c * ν (closedBall x r) ≤ ν (E ∩ closedBall x r)} ≤ (N : ℝ≥0∞) * ν E := by
  obtain ⟨N, τ, hτ, hN⟩ := HasBesicovitchCovering.no_satelliteConfig (α := ℝ)
  refine ⟨N, ?_⟩
  intro ν E hE c R
  let S := {x | ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
    c * ν (closedBall x r) ≤ ν (E ∩ closedBall x r)}
  choose r hr using fun x : S => x.property
  exact real_ball_covering_estimate hτ hN ν E hE c S r R
    (fun x => (hr x).1) (fun x => (hr x).2.1) (fun x => (hr x).2.2)

/-- The same constant controls all radii. Continuity from below holds
for arbitrary increasing sets, so no measurability of the supremum over
the radius parameter has to be assumed. -/
theorem exists_real_relative_maximal_constant_all_radii :
    ∃ N : ℕ, ∀ (ν : Measure ℝ) (E : Set ℝ), MeasurableSet E →
      ∀ c : ℝ≥0∞,
      c * ν {x | ∃ r : ℝ, 0 < r ∧
        c * ν (closedBall x r) ≤ ν (E ∩ closedBall x r)} ≤ (N : ℝ≥0∞) * ν E := by
  obtain ⟨N, hN⟩ := exists_real_relative_maximal_constant
  refine ⟨N, ?_⟩
  intro ν E hE c
  let B : ℕ → Set ℝ := fun m => {x | ∃ r : ℝ, 0 < r ∧ r ≤ (m + 1 : ℝ) ∧
    c * ν (closedBall x r) ≤ ν (E ∩ closedBall x r)}
  have hmono : Monotone B := by
    intro a b hab x hx
    obtain ⟨r, hr, hra, hmass⟩ := hx
    exact ⟨r, hr, hra.trans (by exact_mod_cast Nat.add_le_add_right hab 1), hmass⟩
  have hunion : {x | ∃ r : ℝ, 0 < r ∧
      c * ν (closedBall x r) ≤ ν (E ∩ closedBall x r)} = ⋃ m, B m := by
    ext x
    constructor
    · rintro ⟨r, hr, hmass⟩
      obtain ⟨m, hm⟩ := exists_nat_gt r
      exact mem_iUnion.mpr ⟨m, r, hr, by linarith, hmass⟩
    · intro hx
      obtain ⟨m, r, hr, _, hmass⟩ := mem_iUnion.mp hx
      exact ⟨r, hr, hmass⟩
  rw [hunion, hmono.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le fun m => hN ν E hE c (m + 1)

end DukePrimeDegree

end

end OAI
