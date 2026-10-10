import OAI.Analysis.KadisonKastler.PeriodicMatrixUnits
import OAI.Analysis.KadisonKastler.PublishedIncreasingMatrixInjectivity
import Mathlib.Data.Nat.Factorial.Basic

namespace OAI

/-! # Increasing periodic matrix algebras

Divisibility of the period gives inclusion of the represented matrix
algebras.  A factorial sequence therefore gives increasing finite matrix
stages, while agreement on each fixed finite set of columns gives strong
approximation to the original countable matrix units.
-/

namespace KadisonKastler

open Generator Generator.Tracial Filter
open scoped BigOperators Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E] (F : FullMatrixCorner E)

namespace FullMatrixCorner

local instance periodicFactorialNeZero (n : ℕ) : NeZero n.factorial :=
  ⟨Nat.factorial_ne_zero n⟩

theorem periodicMatrixUnits_column_block (n : ℕ) [NeZero n]
    (i j k : Fin n) (q : ℕ) (x : E) :
    (F.periodicMatrixUnits n).entry i j (F.column (q * n + k) x) =
      if j = k then F.column (q * n + i) x else 0 := by
  change (F.finiteCuntz n).entry i
    (star ((F.finiteCuntz n).entry j) (F.column (q * n + k) x)) = _
  rw [F.finiteCuntz_adjoint_column]
  split_ifs <;> simp only [map_zero, F.finiteCuntz_column]

/-- A period-`n` matrix unit is the sum of its copies in any period `k*n`. -/
theorem periodicMatrixUnits_refinement (n k : ℕ) [NeZero n] [NeZero k]
    (i j : Fin n) :
    (F.periodicMatrixUnits n).entry i j =
      ∑ r : Fin k, (F.periodicMatrixUnits (k * n)).entry
        (finProdFinEquiv (r, i)) (finProdFinEquiv (r, j)) := by
  classical
  apply F.ext_on_columns
  intro l x
  let q := l / (k * n)
  let b : Fin (k * n) := ⟨l % (k * n), Nat.mod_lt _ (Nat.mul_pos
    (Nat.pos_of_ne_zero (NeZero.ne k)) (Nat.pos_of_ne_zero (NeZero.ne n)))⟩
  obtain ⟨⟨r, c⟩, hrc⟩ := finProdFinEquiv.surjective b
  have hl : l = q * (k * n) + (finProdFinEquiv (r, c)).val := by
    rw [hrc]
    exact (Nat.div_add_mod' l (k * n)).symm
  rw [hl]
  have hindex (a : Fin n) :
      q * (k * n) + (finProdFinEquiv (r, a)).val = (q * k + r.val) * n + a.val := by
    change q * (k * n) + (a.val + n * r.val) = (q * k + r.val) * n + a.val
    ring
  conv_lhs => rw [hindex c, F.periodicMatrixUnits_column_block]
  simp only [sum_apply, F.periodicMatrixUnits_column_block]
  have heq (s : Fin k) : finProdFinEquiv (s, j) = finProdFinEquiv (r, c) ↔
      s = r ∧ j = c := by
    rw [Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  simp only [heq]
  by_cases hjc : j = c
  · subst c
    simp only [and_true, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    rw [hindex i]
  · simp only [hjc, and_false, ite_false, Finset.sum_const_zero]

theorem periodicMatrixUnits_algebra_le_of_dvd (n m : ℕ) [NeZero n] [NeZero m]
    (hnm : n ∣ m) :
    (F.periodicMatrixUnits n).algebra ≤ (F.periodicMatrixUnits m).algebra := by
  classical
  obtain ⟨k, hk⟩ := hnm
  have hk0 : k ≠ 0 := by
    intro hz
    have : m = 0 := by simpa [hz] using hk
    exact NeZero.ne m this
  let : NeZero k := ⟨hk0⟩
  have hm : m = k * n := hk.trans (Nat.mul_comm n k)
  clear hk
  subst m
  apply ((F.periodicMatrixUnits n).algebra_le_iff _).mpr
  intro i j
  rw [F.periodicMatrixUnits_refinement n k i j]
  exact (F.periodicMatrixUnits (k * n)).algebra.sum_mem fun r _ =>
    (F.periodicMatrixUnits (k * n)).entry_mem _ _

private theorem matrixUnit_norm_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : MatrixUnitSystem ι (H →L[ℂ] H)) (i j : ι) : ‖A.entry i j‖ ≤ 1 := by
  have hp : IsStarProjection (A.entry j j) := ⟨by
    change A.entry j j * A.entry j j = A.entry j j
    rw [A.mul_entry, ite_eq_left rfl], A.star_entry j j⟩
  have hs : ‖A.entry i j‖ * ‖A.entry i j‖ = ‖A.entry j j‖ := by
    rw [← CStarRing.norm_star_mul_self, A.star_entry, A.mul_entry, ite_eq_left rfl]
  nlinarith [hp.norm_le, norm_nonneg (A.entry i j)]

private theorem entry_norm_le_one (i j : ℕ) : ‖F.entry i j‖ ≤ 1 := by
  have hp : IsStarProjection (F.entry j j) := ⟨by
    change F.entry j j * F.entry j j = F.entry j j
    rw [F.mul_entry, ite_eq_left rfl], F.star_entry j j⟩
  have hs : ‖F.entry i j‖ * ‖F.entry i j‖ = ‖F.entry j j‖ := by
    rw [← CStarRing.norm_star_mul_self, F.star_entry, F.mul_entry, ite_eq_left rfl]
  nlinarith [hp.norm_le, norm_nonneg (F.entry i j)]

/-- Uniformly bounded operators that eventually agree on each column
converge strongly.  Only finite sums of columns are used. -/
theorem tendsto_apply_of_eventually_eq_columns
    (a : ℕ → H →L[ℂ] H) (T : H →L[ℂ] H)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hT : ‖T‖ ≤ 1)
    (hc : ∀ k (x : E), ∀ᶠ n in atTop, a n (F.column k x) = T (F.column k x))
    (x : H) : Tendsto (fun n => a n x) atTop (𝓝 (T x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : ∀ᶠ s : Finset ℕ in atTop, dist (F.partialDiagonal s x) x < ε / 3 :=
    F.partialDiagonal_tendsto x (Metric.ball_mem_nhds x (by positivity))
  obtain ⟨s, hs⟩ := he.exists
  have heq : ∀ᶠ n in atTop, a n (F.partialDiagonal s x) = T (F.partialDiagonal s x) := by
    have hh : ∀ᶠ n in atTop, ∀ k ∈ s,
        a n (F.column k (E.orthogonalProjectionOnto (F.entry 0 k x))) =
          T (F.column k (E.orthogonalProjectionOnto (F.entry 0 k x))) :=
      (eventually_all_finset s).mpr fun k _ => hc k _
    filter_upwards [hh] with n hn
    simp only [partialDiagonal, sum_apply, map_sum, F.diagonal_apply]
    exact Finset.sum_congr rfl hn
  filter_upwards [heq] with n hn
  have hnorm : ‖x - F.partialDiagonal s x‖ < ε / 3 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hs
  rw [dist_eq_norm]
  calc
    ‖a n x - T x‖ = ‖a n (x - F.partialDiagonal s x) -
        T (x - F.partialDiagonal s x)‖ := by rw [map_sub, map_sub, hn]; congr 1; abel
    _ ≤ ‖a n (x - F.partialDiagonal s x)‖ + ‖T (x - F.partialDiagonal s x)‖ :=
      norm_sub_le _ _
    _ ≤ ‖x - F.partialDiagonal s x‖ + ‖x - F.partialDiagonal s x‖ :=
      add_le_add ((a n).le_opNorm _ |>.trans
        (mul_le_of_le_one_left (norm_nonneg _) (ha n)))
        (T.le_opNorm _ |>.trans (mul_le_of_le_one_left (norm_nonneg _) hT))
    _ < ε := by linarith

/-- The actual factorial-period approximation to one countable matrix unit. -/
def periodicEntryApprox (i j n : ℕ) : H →L[ℂ] H :=
  if h : i < (n + 1).factorial ∧ j < (n + 1).factorial then
    (F.periodicMatrixUnits (n + 1).factorial).entry ⟨i, h.1⟩ ⟨j, h.2⟩
  else 0

theorem norm_periodicEntryApprox_le_one (i j n : ℕ) :
    ‖F.periodicEntryApprox i j n‖ ≤ 1 := by
  unfold periodicEntryApprox
  split_ifs
  · exact matrixUnit_norm_le_one _ _ _
  · simp

theorem periodicEntryApprox_strong (i j : ℕ) (x : H) :
    Tendsto (fun n => F.periodicEntryApprox i j n x) atTop (𝓝 (F.entry i j x)) := by
  apply F.tendsto_apply_of_eventually_eq_columns _ _
    (F.norm_periodicEntryApprox_le_one i j) (F.entry_norm_le_one i j)
  intro k y
  filter_upwards [eventually_ge_atTop (max (max i j) k)] with n hn
  have hnF := Nat.self_le_factorial (n + 1)
  have hi : i < (n + 1).factorial := by omega
  have hj : j < (n + 1).factorial := by omega
  have hk : k < (n + 1).factorial := by omega
  rw [periodicEntryApprox, dite_eq_left ⟨hi, hj⟩]
  exact F.periodicMatrixUnits_agree_on_column _ i j k hi hj hk y

end FullMatrixCorner

end

end KadisonKastler

end OAI
