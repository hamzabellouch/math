import OAI.MeasureTheory.Falconer.Recursion.ScalarBranchAccounting

namespace OAI

/-! The prefix left by the greedy ledger is short because every occupied
 prefix obeys the original scalar nonconcentration bound. -/
namespace Falconer.Regularization

 theorem scalar_bunched_prefix_length {B M T lo P : ℕ}
    (L : Finset (CellPath 1)) (hL : L ⊆ cubePaths 1 (B*M)) (hne : L.Nonempty)
    (k n : ℕ → ℕ)
    (hlevel : ∀ i < M, ScalarBranchingLevel L (B*i) (B*(i+1)) (k i) (n i))
    (e : ℕ → ℕ) (he : StrictMono e) (he0 : e 0 = 0) (heT : e T ≤ M) (hlo : lo ≤ T)
    (hprefix : (∑ i ∈ Finset.range lo, (scalarCompressedBranch e k i:ℝ)) ≤
      2*(P:ℝ)*(lo:ℝ))
    {K κ : ℝ} (hK : 0 < K) (hκ : 0 ≤ κ)
    (hball : ∀ u t : ℝ, (1/2:ℝ)^(B*M) ≤ t → t ≤ 1 →
      scalarBallMass (L.image scalarPathCenter) u t ≤
        K*t^κ*((L.image scalarPathCenter).card:ℝ)) :
    (κ*(B:ℝ)-2*(P:ℝ))*(lo:ℝ)*Real.log 2 ≤ Real.log K := by
  have hd : Monotone (fun j : ℕ => B*e j) := fun _ _ hij => Nat.mul_le_mul_left B (he.monotone hij)
  have helo : e lo ≤ M := (he.monotone hlo).trans heT
  have hcard : ∀ i < T, ∀ p ∈ L.image (List.take (B*e i)),
      (prefixChildren L (B*e i) (B*e (i+1)) p).card = 2^(scalarCompressedBranch e k i) := by
    intro i hi p hp
    exact scalar_grouped_children_card L (fun j => B*j) k
      (fun _ _ hij => Nat.mul_le_mul_left B hij) M (fun j hj => (hlevel j hj).children_card)
      (he.monotone (Nat.le_succ i)) ((he.monotone (show i+1 ≤ T by omega)).trans heT) p hp
  have hc := scalar_prefix_nonconcentration L hL hne (Nat.mul_le_mul_left B helo) hball
  rw [scalar_uniform_prefix_card L hne (fun j => B*e j) (scalarCompressedBranch e k) hd
    (by rw [he0,Nat.mul_zero]) hcard hlo,Nat.cast_pow,Nat.cast_ofNat] at hc
  have hidx : lo ≤ e lo := by
    have hh := he.add_le_nat lo 0
    simpa only [he0,Nat.add_zero] using hh
  apply scalar_stopped_prefix_length hK hκ hc (Nat.mul_le_mul_left B hidx)
  simpa only [Nat.cast_sum] using hprefix

 theorem scalar_bunched_prefix_short {B P T lo : ℕ} {K κ : ℝ}
    (hP : 0 < P) (hbudget : 800*(P:ℝ) ≤ κ*(B:ℝ))
    (hprefix : (κ*(B:ℝ)-2*(P:ℝ))*(lo:ℝ)*Real.log 2 ≤ Real.log K)
    (hscale : 10*Real.log K ≤ (κ*(B:ℝ)-2*(P:ℝ))*(T:ℝ)*Real.log 2) :
    10*lo ≤ T := by
  have hPR : (0:ℝ) < (P:ℝ) := by exact_mod_cast hP
  have hc : 0 < (κ*(B:ℝ)-2*(P:ℝ))*Real.log 2 :=
    mul_pos (by linarith) (Real.log_pos (by norm_num))
  have hh : (10*(lo:ℝ))*((κ*(B:ℝ)-2*(P:ℝ))*Real.log 2) ≤
      (T:ℝ)*((κ*(B:ℝ)-2*(P:ℝ))*Real.log 2) := by nlinarith
  have hh' := le_of_mul_le_mul_right hh hc
  exact_mod_cast hh'

end Falconer.Regularization

end OAI
