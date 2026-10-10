import OAI.NumberTheory.Jacobsthal.Probability.SourceThresholdCoupling
import OAI.NumberTheory.Jacobsthal.Sieve.ExponentialMesh

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ThresholdMeshRate
open _root_.Filter SourceThresholdCoupling ExponentialMesh
open scoped Topology

theorem thresholdPerturbation_le {h : ℝ} (hh : 0 ≤ h) (N : ℕ)
    (hsmall : 4*((N:ℝ)+1)*h ≤ 1) : thresholdPerturbation h N ≤ 39*((N:ℝ)+1)*h := by
  have hexp := exp_increment (show 0 ≤ 4*((N:ℝ)+1)*h by positivity) hsmall
  unfold thresholdPerturbation
  nlinarith [mul_nonneg (Nat.cast_nonneg N) hh]

theorem threshold_mesh_controls {A C κ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hκ : 0 < κ)
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ w : ℝ in atTop,∀ N : ℕ,(N:ℝ) ≤ A*(Real.log w)^3 →
      Real.exp (4*((N:ℝ)+1)*mesh κ w) ≤ 4/3 ∧
        C*((N:ℝ)+1)*thresholdPerturbation (mesh κ w) N ≤ eta := by
  have hlog : 0 < Real.log (4/3:ℝ) := Real.log_pos (by norm_num)
  have hmin : 0 < min 1 (Real.log (4/3:ℝ)) := lt_min (by norm_num) hlog
  filter_upwards [(log_power_exp_tendsto (4*(A+1)) 3 hκ).eventually (eventually_le_nhds hmin),
    (log_power_exp_tendsto (39*C*(A+1)^2) 6 hκ).eventually (eventually_le_nhds heta),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with w harg herr hL
  intro N hN
  have hm : 0 ≤ mesh κ w := (mesh_pos κ w).le
  have hL3 : 1 ≤ (Real.log w)^3 := one_le_pow₀ hL
  have hNp : (N:ℝ)+1 ≤ (A+1)*(Real.log w)^3 := by nlinarith
  have harg' : 4*((N:ℝ)+1)*mesh κ w ≤ min 1 (Real.log (4/3:ℝ)) := by
    calc
      _ ≤ (4*(A+1)*(Real.log w)^3)*Real.exp (-κ*Real.sqrt (Real.log w)) :=
        mul_le_mul (by nlinarith) (mesh_upper κ w) hm (by positivity)
      _ ≤ _ := harg
  refine ⟨?_,?_⟩
  · have hh := Real.exp_le_exp.mpr (harg'.trans (min_le_right _ _))
    simpa only [Real.exp_log (by norm_num : (0:ℝ)<4/3)] using hh
  · have hpert := thresholdPerturbation_le hm N (harg'.trans (min_le_left _ _))
    have hsq : ((N:ℝ)+1)^2 ≤ (A+1)^2*(Real.log w)^6 := by
      have hh := sq_le_sq₀ (show 0 ≤ (N:ℝ)+1 by positivity) (show 0 ≤ (A+1)*(Real.log w)^3 by positivity) |>.mpr hNp
      nlinarith
    calc
      _ ≤ 39*C*((N:ℝ)+1)^2*mesh κ w := by
        have hh := mul_le_mul_of_nonneg_left hpert (show 0 ≤ C*((N:ℝ)+1) by positivity)
        nlinarith
      _ ≤ (39*C*(A+1)^2*(Real.log w)^6)*Real.exp (-κ*Real.sqrt (Real.log w)) :=
        mul_le_mul (by nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ 39*C by positivity)])
          (mesh_upper κ w) hm (by positivity)
      _ ≤ _ := herr
end NumberTheoryLean.ThresholdMeshRate


end Erdos970

end OAI
