import OAI.NumberTheory.Ostmann.Dirichlet.ZetaLocalPreparation
import OAI.NumberTheory.Ostmann.Dirichlet.ZetaLogDerivative

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet
open scoped BigOperators

theorem uniform_zeta_local_zero_estimates :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ∃ S : Finset ℂ,
      (∀ rho, rho ∈ S ↔ ‖rho‖ ≤ 19 / 20 ∧ regularZeta (zetaDiskPoint t rho) = 0) ∧
      (∀ rho ∈ S, rho.re < -4 / 5) ∧
      (∑ rho ∈ S, ((analyticOrderAt (normalizedZeta t) rho).toNat : ℝ)) ≤
        C * Real.log (|t| + 6) ∧
      ∀ w : ℂ, ‖w‖ ≤ 17 / 20 → regularZeta (zetaDiskPoint t w) ≠ 0 →
        ‖(5 / 4 : ℂ) * (deriv regularZeta (zetaDiskPoint t w) /
            regularZeta (zetaDiskPoint t w)) -
          ∑ rho ∈ S, (analyticOrderAt (normalizedZeta t) rho).toNat / (w - rho)‖ ≤
            C * Real.log (|t| + 6) := by
  classical
  obtain ⟨C, hC, hlocal⟩ := Erdos970.Erdos970Dependency.SiegelWalfisz.exists_local_zero_log_derivative_constant
  obtain ⟨K, hK, hbound⟩ := exists_normalizedZeta_bound
  let D : ℝ := Real.log ((39 / 40 : ℝ) / (19 / 20))
  have hD : 0 < D := Real.log_pos (by norm_num)
  let A : ℝ := Real.log K + 2
  have hA : 0 < A := by dsimp [A]; have := Real.log_nonneg hK; linarith
  refine ⟨C * A + A / D, by positivity, ?_⟩
  intro t
  have hn := regularZeta_ne_zero_of_one_le_re (s := zetaCenter t) (by simp)
  have hzeros (rho : ℂ) : normalizedZeta t rho = 0 ↔ regularZeta (zetaDiskPoint t rho) = 0 := by
    unfold normalizedZeta
    exact div_eq_zero_iff.trans (or_iff_left hn)
  obtain ⟨S, hS, hb⟩ := hlocal (K * (|t| + 6) ^ 2) (zeta_envelope_gt_one hK t)
    (normalizedZeta t) (fun w _ => normalizedZeta_analytic t w) (normalizedZeta_zero t)
    (fun w hw => hbound t w (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw))
  have ht : 0 ≤ Real.log (|t| + 6) := zero_le_one.trans (zeta_height_ge_one t)
  have hj := entire_sum_analyticOrder_le_jensen (normalizedZeta t) (normalizedZeta_analytic t) S
    (c := 0) (r := 19 / 20) (R := 39 / 40) (M := K * (|t| + 6) ^ 2)
    (by norm_num) (by norm_num) (zeta_envelope_gt_one hK t).le
    (by rw [normalizedZeta_zero]; norm_num)
    (fun rho hr => by simpa only [Metric.mem_closedBall, dist_zero_right] using ((hS rho).mp hr).1)
    (fun w hw => hbound t w (by
      have he : ‖w‖ = 39 / 40 := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
      rw [he]; norm_num))
  rw [normalizedZeta_zero, norm_one, div_one] at hj
  have hlog := log_zeta_envelope_bound hK t
  refine ⟨S, fun rho => (hS rho).trans (and_congr_right fun _ => hzeros rho),
    fun rho hr => normalizedZeta_zero_re_lt t ((hS rho).mp hr).2, ?_, ?_⟩
  · have hh := div_le_div_of_nonneg_right hlog hD.le
    change _ ≤ Real.log (K * (|t| + 6) ^ 2) / D at hj
    calc
      _ ≤ ((Real.log K + 2) * Real.log (|t| + 6)) / D := hj.trans hh
      _ = (A / D) * Real.log (|t| + 6) := by dsimp only [A]; ring
      _ ≤ (C * A + A / D) * Real.log (|t| + 6) :=
        mul_le_mul_of_nonneg_right (by nlinarith [mul_pos hC hA]) ht
  · intro w hw hne
    have h := hb w hw (fun hz => hne ((hzeros w).mp hz))
    rw [normalizedZeta_log_derivative t w hne] at h
    have hh := mul_le_mul_of_nonneg_left hlog hC.le
    dsimp only [A] at *
    nlinarith [mul_nonneg (div_pos hA hD).le ht]

end Ostmann.Dirichlet

end OAI
