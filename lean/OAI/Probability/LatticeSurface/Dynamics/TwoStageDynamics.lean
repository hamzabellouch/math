import Mathlib
import OAI.Probability.LatticeSurface.Convexity.ClusterDynamics

namespace OAI

namespace ClusterDisplacement

variable {V : Type*} [Fintype V]

theorem two_stage_displacement (u : ℕ → V → ℝ)
    (hstep : ∀n,∃ A B : Kernel V,Firm A ∧ Firm B ∧ u (n+1)=B.apply (A.apply (u n)))
    (N k : ℕ) (hk : k≤N) (x : V) :
    |u k x-u 0 x|≤5*(Fintype.card V+1:ℝ)*Real.sqrt (energy (u 0)-energy (u N)) := by
  classical
  choose A B hA hB hu using hstep
  let K : ℕ → Kernel V := fun n => if n%2=0 then A (n/2) else B (n/2)
  have hke (n : ℕ) : K (2*n)=A n := by simp [K]
  have hko (n : ℕ) : K (2*n+1)=B n := by simp [K,Nat.add_div]
  have hfirm (n) : Firm (K n) := by dsimp [K];split_ifs;exact hA _;exact hB _
  have htraj (n : ℕ) : trajectory K (u 0) (2*n)=u n := by
    induction n with
    | zero => simpa only [mul_zero] using trajectory_zero K (u 0)
    | succ n ih =>
      rw [show 2*(n+1)=2*n+1+1 by omega,trajectory_succ,trajectory_succ,hke,hko,ih]
      exact (hu n).symm
  have h := finite_cluster_displacement K hfirm (u 0) (2*N) (2*k) (by omega) x
  simpa only [htraj] using h

end ClusterDisplacement

end OAI
