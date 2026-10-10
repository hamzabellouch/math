import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace OAI

universe uY

/-!
# A common index for all compression levels

For nonnegative column weights of total mass at most one, an average bound
on the number of indices omitted by each column gives one index whose
omitted mass is at most the same bound. No level parameter enters the
selection, so this index can be used at every approximation level.
-/

namespace MetricEntropyDuality

open scoped BigOperators

/-- The mass lost by retaining a filter is exactly the mass of its complement. -/
theorem sum_sub_sum_filter_eq {Y : Type uY} (s : Finset Y)
    (p : Y → Prop) [DecidablePred p] (μ : Y → ℝ) :
    (∑ y ∈ s, μ y) - (∑ y ∈ s.filter p, μ y) =
      ∑ y ∈ s.filter (fun y => ¬ p y), μ y := by
  apply sub_eq_iff_eq_add.mpr
  exact (Finset.sum_filter_not_add_sum_filter s p μ).symm

/-- Count weighted omissions by indices or by columns. -/
theorem sum_omitted_mass {Y : Type uY} [Fintype Y] {u : ℕ}
    (T : Y → Finset (Fin u)) (μ : Y → ℝ) :
    (∑ i : Fin u, ∑ y ∈ Finset.univ.filter (fun y => i ∉ T y), μ y) =
      ∑ y, μ y * ((Finset.univ \ T y).card : ℝ) := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [← Finset.sum_filter]
  have hfilter : Finset.univ.filter (fun i : Fin u => i ∉ T y) =
      Finset.univ \ T y := by
    ext i
    simp
  rw [hfilter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- One index has omitted mass at most `θ`; it is chosen before all levels. -/
theorem exists_common_index {Y : Type uY} [Fintype Y] {u : ℕ}
    (hu : 0 < u) (T : Y → Finset (Fin u)) (μ : Y → ℝ)
    (hμ : ∀ y, 0 ≤ μ y) (hmass : ∑ y, μ y ≤ 1)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hcomp : ∀ y, ((Finset.univ \ T y).card : ℝ) ≤ θ * (u : ℝ)) :
    ∃ i : Fin u, (∑ y ∈ Finset.univ.filter (fun y => i ∉ T y), μ y) ≤ θ := by
  classical
  have hsum :
      (∑ i : Fin u, ∑ y ∈ Finset.univ.filter (fun y => i ∉ T y), μ y) ≤
        ∑ _i : Fin u, θ := by
    calc
      _ = ∑ y, μ y * ((Finset.univ \ T y).card : ℝ) := sum_omitted_mass T μ
      _ ≤ ∑ y, μ y * (θ * (u : ℝ)) := by
        exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hcomp y) (hμ y)
      _ = (∑ y, μ y) * (θ * (u : ℝ)) := by rw [Finset.sum_mul]
      _ ≤ 1 * (θ * (u : ℝ)) :=
        mul_le_mul_of_nonneg_right hmass (mul_nonneg hθ (Nat.cast_nonneg u))
      _ = ∑ _i : Fin u, θ := by simp [nsmul_eq_mul, mul_comm]
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le
    (show (Finset.univ : Finset (Fin u)).Nonempty from
      ⟨⟨0, hu⟩, Finset.mem_univ _⟩) hsum
  exact ⟨i, hi⟩

end MetricEntropyDuality

end OAI
