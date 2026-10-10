import OAI.NumberTheory.Ostmann.Dirichlet.EntireJensen
import OAI.NumberTheory.Ostmann.Dirichlet.WideLocalZero
import OAI.NumberTheory.Ostmann.Dirichlet.WideNormalizedDisk

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet
open scoped BigOperators

theorem wideNormalizedDirichlet_log_derivative {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (t : ℝ) (w : ℂ)
    (hw : DirichletCharacter.LFunction chi (wideDirichletDiskPoint t w) ≠ 0) :
    deriv (wideNormalizedDirichlet chi t) w / wideNormalizedDirichlet chi t w =
      (29/10:ℂ) * (deriv (DirichletCharacter.LFunction chi) (wideDirichletDiskPoint t w) /
        DirichletCharacter.LFunction chi (wideDirichletDiskPoint t w)) := by
  have hn := LFunction_ne_zero_right chi (s := dirichletCenter t) (by simp)
  have hp : HasDerivAt (wideDirichletDiskPoint t) (29/10:ℂ) w := by
    simpa only [wideDirichletDiskPoint, id_eq, mul_one] using! (((hasDerivAt_id w).const_mul (29/10:ℂ)).const_add (dirichletCenter t))
  have hd := (((DirichletCharacter.differentiable_LFunction hchi).differentiableAt.hasDerivAt).comp w hp).div_const
    (DirichletCharacter.LFunction chi (dirichletCenter t))
  change HasDerivAt (wideNormalizedDirichlet chi t)
    ((deriv (DirichletCharacter.LFunction chi) (wideDirichletDiskPoint t w) * (29/10:ℂ)) /
      DirichletCharacter.LFunction chi (dirichletCenter t)) w at hd
  rw [hd.deriv]
  unfold wideNormalizedDirichlet
  field_simp

theorem uniform_wide_local_zero_estimates :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi ≠ 1 → ∀ t : ℝ, ∃ S : Finset ℂ,
        (∀ rho, rho ∈ S ↔ ‖rho‖ ≤ 49/50 ∧
          DirichletCharacter.LFunction chi (wideDirichletDiskPoint t rho) = 0) ∧
        (∑ rho ∈ S, ((analyticOrderAt (wideNormalizedDirichlet chi t) rho).toNat:ℝ) ≤
          C * q * (|t|+6)) ∧
        ∀ w : ℂ, ‖w‖ ≤ 19/20 →
          DirichletCharacter.LFunction chi (wideDirichletDiskPoint t w) ≠ 0 →
          ‖(29/10:ℂ)*(deriv (DirichletCharacter.LFunction chi) (wideDirichletDiskPoint t w) /
            DirichletCharacter.LFunction chi (wideDirichletDiskPoint t w)) -
            ∑ rho ∈ S, (analyticOrderAt (wideNormalizedDirichlet chi t) rho).toNat/(w-rho)‖ ≤
            C * q * (|t|+6) := by
  classical
  obtain ⟨C0, hC0, hlocal⟩ := exists_wide_local_zero_log_derivative_constant
  let D : ℝ := Real.log ((99/100:ℝ)/(49/50))
  have hD : 0 < D := Real.log_pos (by norm_num)
  let C : ℝ := max (C0 * (10 * absoluteZetaTwo)) ((10 * absoluteZetaTwo) / D)
  have hZ : 0 < absoluteZetaTwo := zero_lt_one.trans_le one_le_absoluteZetaTwo
  have hC : 0 < C := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro q _ chi hchi t
  have hn := LFunction_ne_zero_right chi (s := dirichletCenter t) (by simp)
  obtain ⟨S,hS,hb⟩ := hlocal (wideDirichletDiskEnvelope q t)
    (wideDirichletDiskEnvelope_gt_one q t) (wideNormalizedDirichlet chi t)
    (fun w _ => wideNormalizedDirichlet_analytic chi hchi t w)
    (wideNormalizedDirichlet_zero chi t)
    (fun w hw => wideNormalizedDirichlet_bound chi hchi t
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw))
  have hzeros (rho : ℂ) : wideNormalizedDirichlet chi t rho = 0 ↔
      DirichletCharacter.LFunction chi (wideDirichletDiskPoint t rho) = 0 := by
    unfold wideNormalizedDirichlet
    exact div_eq_zero_iff.trans (or_iff_left hn)
  have hlog : Real.log (wideDirichletDiskEnvelope q t) ≤ wideDirichletDiskEnvelope q t :=
    (Real.log_le_sub_one_of_pos (zero_lt_one.trans
      (wideDirichletDiskEnvelope_gt_one q t))).trans (by linarith)
  have h0 := wideNormalizedDirichlet_zero chi t
  have hmass := entire_sum_analyticOrder_le_jensen (wideNormalizedDirichlet chi t)
    (fun w => wideNormalizedDirichlet_analytic chi hchi t w) S
    (c := 0) (r := 49/50) (R := 99/100)
    (M := wideDirichletDiskEnvelope q t) (by norm_num) (by norm_num)
    (wideDirichletDiskEnvelope_gt_one q t).le (by rw [h0]; norm_num)
    (fun rho hr => by simpa only [Metric.mem_closedBall, dist_zero_right] using ((hS rho).mp hr).1)
    (fun w hw => wideNormalizedDirichlet_bound chi hchi t (by
      have he : ‖w‖ = 99/100 := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
      rw [he]; norm_num))
  rw [h0,norm_one,div_one] at hmass
  refine ⟨S,fun rho => (hS rho).trans (and_congr_right fun _ => hzeros rho),?_,?_⟩
  · calc
      _ ≤ Real.log (wideDirichletDiskEnvelope q t) / D := hmass
      _ ≤ wideDirichletDiskEnvelope q t / D := div_le_div_of_nonneg_right hlog hD.le
      _ = ((10*absoluteZetaTwo)/D) * q * (|t|+6) := by unfold wideDirichletDiskEnvelope; ring
      _ ≤ C * q * (|t|+6) := by gcongr; exact le_max_right _ _
  · intro w hw hne
    have h := hb w hw (fun hz => hne ((hzeros w).mp hz))
    rw [wideNormalizedDirichlet_log_derivative chi hchi t w hne] at h
    calc
      _ ≤ C0 * Real.log (wideDirichletDiskEnvelope q t) := h
      _ ≤ C0 * wideDirichletDiskEnvelope q t := mul_le_mul_of_nonneg_left hlog hC0.le
      _ = (C0*(10*absoluteZetaTwo)) * q * (|t|+6) := by unfold wideDirichletDiskEnvelope; ring
      _ ≤ C * q * (|t|+6) := by gcongr; exact le_max_left _ _

end Ostmann.Dirichlet

end OAI
