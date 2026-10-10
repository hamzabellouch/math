import OAI.Probability.InvariantIsing.Cavity.CavityFiniteDeficit
import OAI.Probability.InvariantIsing.Cavity.CavityFieldIncrement

namespace OAI

/-! Identification of the root and all positive-level field covariance
increments for the finite trial quantile used in the cavity argument. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem finite_overlap_field_increment (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {n : ℕ} (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (i : Fin n) :
    (∫ r in q i.castSucc..q i.succ, deriv (finiteR rho lam hrho hsum) (deficit p r)) =
      (finiteR rho lam hrho hsum (deficit p (q i.castSucc)) -
        finiteR rho lam hrho hsum (deficit p (q i.succ))) / cut i.castSucc.succ := by
  have hmass := finite_overlap_cumulative_mass p cut hcut hfirst hlast q hq hp i.castSucc
  have hc : 0 < cut i.castSucc.succ := by
    rw [← hfirst]
    apply hcut
    exact Fin.succ_pos _
  have hm : pathMeasure.real {s | p s ≤ q i.castSucc} ≠ 0 := by
    rw [hmass]
    exact hc.ne'
  have h := integral_finiteR_deriv_deficit_gap rho lam hrho hsum p
    (hq (Fin.castSucc_lt_succ (i := i)))
    (finite_overlap_value_gap p cut hfirst hlast q hq.monotone hp i)
    (finite_overlap_deficit_pos p cut hfirst hlast q hq.monotone hp htop
      (hq.monotone (Fin.le_last _))) hm
  rwa [hmass] at h

theorem finite_overlap_field_root (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {n : ℕ} (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j) :
    (∫ r in 0..q 0, deriv (finiteR rho lam hrho hsum) (deficit p r)) =
      q 0 * deriv (finiteR rho lam hrho hsum) (deficit p (q 0)) := by
  have hbound := (finite_overlap_ae_bounds p cut hfirst hlast q hq hp).mono (fun _ h => h.1)
  have hq0 := (finite_overlap_value_mem_unit p cut hcut q hp 0).1
  calc
    _ = ∫ _r in 0..q 0, deriv (finiteR rho lam hrho hsum) (deficit p (q 0)) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hq0
      intro r hr
      dsimp only
      rw [deficit_constant_below_ae_lower p hbound hr.2.le]
    _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]

end InvariantIsing

end

end OAI
