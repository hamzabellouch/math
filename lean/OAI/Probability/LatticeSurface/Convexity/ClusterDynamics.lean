import Mathlib
import OAI.Probability.LatticeSurface.Convexity.ClusterDynamicsDefs
import OAI.Probability.LatticeSurface.Convexity.FiniteLevelBarrier

namespace OAI

namespace ClusterDisplacement

variable {V : Type*} [Fintype V]

lemma trajectory_zero (K : ℕ → Kernel V) (u₀ : V → ℝ) : trajectory K u₀ 0=u₀ := Kernel.identity_apply u₀

lemma trajectory_succ (K : ℕ → Kernel V) (u₀ : V → ℝ) (n : ℕ) :
    trajectory K u₀ (n+1)=(K n).apply (trajectory K u₀ n) := Kernel.comp_apply _ _ _

lemma energy_antitone (K : ℕ → Kernel V) (u₀ : V → ℝ) : Antitone (fun n => energy (trajectory K u₀ n)) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [trajectory_succ]
  exact (K n).energy_bound _

lemma trajectory_energy_le (K : ℕ → Kernel V) (u₀ : V → ℝ) (n : ℕ) :
    energy (trajectory K u₀ n)≤energy u₀ := by
  simpa only [trajectory_zero] using energy_antitone K u₀ (Nat.zero_le n)

lemma trajectory_jump (K : ℕ → Kernel V) (hfirm : ∀n,Firm (K n)) (u₀ : V → ℝ) (N n : ℕ) (hn : n<N) (x : V) :
    |trajectory K u₀ (n+1) x-trajectory K u₀ n x|≤Real.sqrt (energy u₀-energy (trajectory K u₀ N)) := by
  classical
  have hsq : (trajectory K u₀ n x-trajectory K u₀ (n+1) x)^2≤energy u₀-energy (trajectory K u₀ N) := by
    calc
      _ ≤ energy (fun y => trajectory K u₀ n y-trajectory K u₀ (n+1) y) :=
        Finset.single_le_sum (fun y _ => sq_nonneg _) (Finset.mem_univ x)
      _ ≤ energy (trajectory K u₀ n)-energy (trajectory K u₀ (n+1)) := by
        rw [trajectory_succ]
        exact hfirm n _
      _ ≤ _ := sub_le_sub (trajectory_energy_le K u₀ n) (energy_antitone K u₀ hn)
  have hD := sub_nonneg.mpr (trajectory_energy_le K u₀ N)
  have hs := Real.sq_sqrt hD
  have hr := Real.sqrt_nonneg (energy u₀-energy (trajectory K u₀ N))
  rw [abs_sub_comm]
  nlinarith [sq_abs (trajectory K u₀ n x-trajectory K u₀ (n+1) x)]

end ClusterDisplacement

namespace ClusterDisplacement

variable {V : Type*} [Fintype V]

theorem finite_cluster_displacement (K : ℕ → Kernel V) (hfirm : ∀n,Firm (K n))
    (u₀ : V → ℝ) (N k : ℕ) (hk : k≤N) (x : V) :
    |trajectory K u₀ k x-u₀ x|≤5*(Fintype.card V+1:ℝ)*
      Real.sqrt (energy u₀-energy (trajectory K u₀ N)) := by
  have hnear : ∀n≤k,∃i : V ⊕ Unit,|trajectory K u₀ n x-(Sum.elim u₀ (fun _ => 0)) i|≤
      Real.sqrt (energy u₀-energy (trajectory K u₀ N)) := by
    intro n hn
    exact (products K n).near_initial_level u₀ x _ (sub_le_sub_left (energy_antitone K u₀ (hn.trans hk)) _)
  have hbound := finite_level_barrier (Sum.elim u₀ (fun _ => 0)) (fun n => trajectory K u₀ n x) k
    (Real.sqrt (energy u₀-energy (trajectory K u₀ N))) (Real.sqrt_nonneg _) hnear
    (fun n hn => trajectory_jump K hfirm u₀ N n (hn.trans_le hk) x)
  simpa only [trajectory_zero,Fintype.card_sum,Fintype.card_unit,Nat.cast_add,Nat.cast_one] using hbound

end ClusterDisplacement

end OAI
