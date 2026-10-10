import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodSupport

namespace OAI

namespace ConvexSkorokhod

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem walk_driver_stability (B : Body E) (x₀ y₀ : E)
    (hx₀ : x₀∈B.carrier) (hy₀ : y₀∈B.carrier) (w v : ℕ → E) (N : ℕ) (ε : ℝ) (hε : 0≤ε)
    (hw : ∀n≤N,‖(x₀+(w n-w 0))-(y₀+(v n-v 0))‖≤ε) :
    ‖walk B x₀ w N-walk B y₀ v N‖≤ε+Real.sqrt (2*ε*
      (variation (regulator B x₀ w) N+variation (regulator B y₀ v) N)) := by
  let k := regulator B x₀ w
  let l := regulator B y₀ v
  let d : ℕ → E := fun n => k n-l n
  let z : ℕ → E := fun n => (x₀+(w n-w 0))-(y₀+(v n-v 0))
  have hd₀ : d 0=0 := by simp [d,k,l,regulator_zero]
  have he (n) : walk B x₀ w n-walk B y₀ v n=z n+d n := by dsimp [z,d,k,l,regulator];abel
  have hi (n) : d (n+1)-d n=(k (n+1)-k n)-(l (n+1)-l n) := by dsimp [d];abel
  have hstep (n : ℕ) (hn : n<N) :
      inner ℝ (d (n+1)-d n) (d (n+1))≤ε*(‖k (n+1)-k n‖+‖l (n+1)-l n‖) := by
    have h₀ := regulator_normal B x₀ w n (walk B y₀ v (n+1)) (walk_mem B y₀ hy₀ v (n+1))
    have h₁ := regulator_normal B y₀ v n (walk B x₀ w (n+1)) (walk_mem B x₀ hx₀ w (n+1))
    have ho : inner ℝ (d (n+1)-d n) (walk B x₀ w (n+1)-walk B y₀ v (n+1))≤0 := by
      rw [hi,inner_sub_left]
      have hrev : walk B y₀ v (n+1)-walk B x₀ w (n+1)=-(walk B x₀ w (n+1)-walk B y₀ v (n+1)) := by abel
      rw [hrev,inner_neg_right] at h₀
      change 0≤-(inner ℝ (k (n+1)-k n) (walk B x₀ w (n+1)-walk B y₀ v (n+1))) at h₀
      change 0≤ inner ℝ (l (n+1)-l n) (walk B x₀ w (n+1)-walk B y₀ v (n+1)) at h₁
      linarith
    rw [he,inner_add_right] at ho
    have hnorm : ‖d (n+1)-d n‖≤‖k (n+1)-k n‖+‖l (n+1)-l n‖ := by rw [hi];exact norm_sub_le _ _
    have habs := (abs_le.mp (abs_real_inner_le_norm (d (n+1)-d n) (z (n+1)))).1
    have hw' : ‖z (n+1)‖≤ε := hw (n+1) hn
    have hprod := mul_le_mul_of_nonneg_left hw' (norm_nonneg (d (n+1)-d n))
    have heps := mul_le_mul_of_nonneg_right hnorm hε
    nlinarith
  have hs := Finset.sum_le_sum (fun n (hn : n∈Finset.range N) => hstep n (Finset.mem_range.mp hn))
  rw [← Finset.mul_sum,Finset.sum_add_distrib] at hs
  change (∑i∈Finset.range N,inner ℝ (d (i+1)-d i) (d (i+1)))≤ε*(variation k N+variation l N) at hs
  have henergy := sum_inner_energy d N
  rw [hd₀,norm_zero,zero_pow (by norm_num : 2≠0),sub_zero] at henergy
  have hsqsum : 0≤∑i∈Finset.range N,‖d (i+1)-d i‖^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsq : ‖d N‖^2≤2*ε*(variation k N+variation l N) := by
    nlinarith
  have hvar (f : ℕ → E) : 0≤variation f N := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hnon : 0≤2*ε*(variation k N+variation l N) := mul_nonneg (by positivity) (add_nonneg (hvar k) (hvar l))
  have hd : ‖d N‖≤Real.sqrt (2*ε*(variation k N+variation l N)) := by
    nlinarith [Real.sq_sqrt hnon,Real.sqrt_nonneg (2*ε*(variation k N+variation l N)),norm_nonneg (d N)]
  rw [he N]
  exact (norm_add_le _ _).trans (add_le_add (hw N le_rfl) hd)

end ConvexSkorokhod

end OAI
