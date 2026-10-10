import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

private theorem finite_coordinate_expansion {m : ℕ}
    (L : (Fin m → ℝ) →L[ℝ] ℝ) (z : Fin m → ℝ) :
    L z = ∑ i : Fin m, L (Pi.single i 1) * z i := by
  calc
    L z = L (∑ i : Fin m, Pi.single i (z i)) :=
      congrArg L (Finset.univ_sum_single z).symm
    _ = ∑ i : Fin m, L (Pi.single i (z i)) := map_sum L _ _
    _ = ∑ i : Fin m, L (Pi.single i 1) * z i := by
      apply Finset.sum_congr rfl
      intro i _
      have hi : (Pi.single i (z i) : Fin m → ℝ) =
          z i • (Pi.single i (1 : ℝ) : Fin m → ℝ) := by
        simpa only [smul_eq_mul, mul_one] using Pi.single_smul' i (z i) (1 : ℝ)
      rw [hi, L.map_smul, smul_eq_mul, mul_comm]

universe u

variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem finite_goldstine
    (v : StrongDual ℝ (StrongDual ℝ Y)) (hv : ‖v‖ ≤ 1)
    {m : ℕ} (f : Fin m → (Y →L[ℝ] ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y : Y, ‖y‖ ≤ 1 ∧ ∀ i, |f i y - v (f i)| < ε := by
  classical
  let T : Y →ₗ[ℝ] (Fin m → ℝ) :=
    { toFun := fun y i => f i y
      map_add' := by
        intro y z
        funext i
        exact (f i).map_add y z
      map_smul' := by
        intro c y
        funext i
        exact (f i).map_smul c y }
  let a : Fin m → ℝ := fun i => v (f i)
  have hconv : Convex ℝ (T '' Metric.closedBall (0 : Y) 1) :=
    (convex_closedBall (0 : Y) (1 : ℝ)).linear_image T
  have ha : a ∈ closure (T '' Metric.closedBall (0 : Y) 1) := by
    by_contra hnot
    obtain ⟨L, c, hLc, hca⟩ :=
      geometric_hahn_banach_closed_point hconv.closure isClosed_closure hnot
    let F : Y →L[ℝ] ℝ := ∑ i : Fin m, L (Pi.single i 1) • f i
    have hFy (y : Y) : F y = L (T y) := by
      calc
        F y = ∑ i : Fin m, L (Pi.single i 1) * f i y := by
          simp only [F, sum_apply,
            smul_apply, smul_eq_mul]
        _ = L (T y) := (finite_coordinate_expansion L (T y)).symm
    have hFa : L a = v F := by
      calc
        L a = ∑ i : Fin m, L (Pi.single i 1) * v (f i) :=
          finite_coordinate_expansion L a
        _ = v F := by simp only [F, map_sum, map_smul, smul_eq_mul]
    have hFlt (y : Y) (hy : ‖y‖ ≤ 1) : F y < c := by
      rw [hFy]
      apply hLc
      apply subset_closure
      refine ⟨y, ?_, rfl⟩
      simpa only [Metric.mem_closedBall, dist_zero_right] using hy
    have hc : 0 < c := by
      simpa only [map_zero] using hFlt 0 (by simp)
    have hFnorm : ‖F‖ ≤ c := by
      apply ContinuousLinearMap.opNorm_le_of_unit_norm hc.le
      intro y hy
      have hu : F y < c := hFlt y hy.le
      have hl : -F y < c := by
        simpa only [map_neg] using
          hFlt (-y) (by simpa only [norm_neg] using hy.le)
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith only [hl], hu.le⟩
    have hvF : v F ≤ ‖F‖ := by
      apply (le_abs_self (v F)).trans
      simpa only [Real.norm_eq_abs, one_mul] using v.le_of_opNorm_le hv F
    have hcF : c < v F := by simpa only [hFa] using hca
    exact (not_lt_of_ge (hvF.trans hFnorm)) hcF
  obtain ⟨z, hz, haz⟩ := Metric.mem_closure_iff.mp ha ε hε
  rcases hz with ⟨y, hy, rfl⟩
  refine ⟨y, ?_, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hy
  · intro i
    have hnorm : ‖a - T y‖ < ε := by
      simpa only [dist_eq_norm] using haz
    have hi : ‖(a - T y) i‖ < ε :=
      lt_of_le_of_lt (norm_le_pi_norm (a - T y) i) hnorm
    have hi' : |v (f i) - f i y| < ε := by
      change ‖v (f i) - f i y‖ < ε at hi
      simpa only [Real.norm_eq_abs] using hi
    simpa only [abs_sub_comm] using hi'

end MarkovSuperreflexivity

end

end OAI
