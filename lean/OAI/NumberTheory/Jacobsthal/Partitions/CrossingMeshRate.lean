import OAI.NumberTheory.Jacobsthal.Sieve.ExponentialMesh

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.CrossingMeshRate
open _root_.Filter ExponentialMesh
open scoped Topology

theorem crossing_mesh_control {A κ : ℝ} (hA : 0 ≤ A) (hκ : 0 < κ) :
    ∀ᶠ w : ℝ in atTop,∀ N : ℕ,(N:ℝ) ≤ A*(Real.log w)^3 →
      Real.exp (4*(N:ℝ)*mesh κ w) ≤ 11/10 := by
  have hp : 0 < Real.log (11/10:ℝ) := Real.log_pos (by norm_num)
  filter_upwards [(log_power_exp_tendsto (4*A) 3 hκ).eventually (eventually_le_nhds hp),
    Real.tendsto_log_atTop.eventually_ge_atTop 0] with w hh hlog
  intro N hN
  have hb : 4*(N:ℝ)*mesh κ w ≤ Real.log (11/10:ℝ) := by
    calc
      _ ≤ (4*A*(Real.log w)^3)*Real.exp (-κ*Real.sqrt (Real.log w)) :=
        mul_le_mul (by nlinarith) (mesh_upper κ w) (mesh_pos κ w).le (by positivity)
      _ ≤ _ := hh
  exact (Real.exp_le_exp.mpr hb).trans_eq (Real.exp_log (by norm_num))
end NumberTheoryLean.CrossingMeshRate


end Erdos970

end OAI
