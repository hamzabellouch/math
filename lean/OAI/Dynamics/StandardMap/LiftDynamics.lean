import OAI.Dynamics.StandardMap.ObservationTransport

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
noncomputable def liftStep (k : ℝ) : Equiv.Perm (ℝ × ℝ) where
  toFun z := (phi k z.1-z.2,z.1)
  invFun z := (z.2,phi k z.2-z.1)
  left_inv := by intro z; ext <;> simp
  right_inv := by intro z; ext <;> simp
@[simp] lemma liftStep_apply (k : ℝ) (z : ℝ × ℝ) :
    liftStep k z=(phi k z.1-z.2,z.1) := rfl
@[simp] lemma liftStep_symm_apply (k : ℝ) (z : ℝ × ℝ) :
    (liftStep k).symm z=(z.2,phi k z.2-z.1) := rfl
noncomputable def liftIter (k : ℝ) (i : ℤ) : ℝ × ℝ → ℝ × ℝ := ((liftStep k)^i : Equiv.Perm (ℝ × ℝ))
lemma liftIter_add (k : ℝ) (i j : ℤ) (z : ℝ × ℝ) :
    liftIter k (i+j) z=liftIter k i (liftIter k j z) := by
  simp only [liftIter,zpow_add,Equiv.Perm.coe_mul,Function.comp_apply]
@[simp] lemma liftIter_zero (k : ℝ) (z : ℝ × ℝ) : liftIter k 0 z=z := by simp [liftIter]
lemma liftIter_nat (k : ℝ) (n : ℕ) (z : ℝ × ℝ) :
    liftIter k n z=(liftedOrbit k z.2 z.1 (n+1),liftedOrbit k z.2 z.1 n) := by
  induction n with
  | zero => simp [liftIter,liftedOrbit]
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,add_comm,liftIter_add,ih]
    simp only [liftIter,zpow_one]
    change (phi k (liftedOrbit k z.2 z.1 (n+1))-liftedOrbit k z.2 z.1 n,
      liftedOrbit k z.2 z.1 (n+1))=_
    rfl
lemma phi_lipschitz (k : ℝ) (hk : 0 ≤ k) :
    LipschitzWith (⟨growthBase k-1,by have := growthBase_ge_four k hk; linarith⟩ : NNReal) (phi k) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (hasDerivAt_phi k x).differentiableAt
  · intro x
    change |deriv (phi k) x| ≤ growthBase k-1
    rw [(hasDerivAt_phi k x).deriv]
    linarith [potential_bound k x hk]
lemma liftStep_lipschitz (k : ℝ) (hk : 0 ≤ k) :
    LipschitzWith (⟨growthBase k,by have := growthBase_ge_four k hk; linarith⟩ : NNReal) (liftStep k) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [Prod.dist_eq, liftStep_apply,liftStep_apply]
  change max (dist (phi k z.1-z.2) (phi k w.1-w.2)) (dist z.1 w.1) ≤ _
  have hM : 1 ≤ growthBase k := by have := growthBase_ge_four k hk; linarith
  have h1 : dist z.1 w.1 ≤ dist z w := by rw [Prod.dist_eq]; exact le_max_left _ _
  have h2 : dist z.2 w.2 ≤ dist z w := by rw [Prod.dist_eq]; exact le_max_right _ _
  refine max_le ?_ ?_
  · calc
      _ ≤ dist (phi k z.1) (phi k w.1)+dist z.2 w.2 := dist_sub_sub_le _ _ _ _
      _ ≤ (growthBase k-1)*dist z.1 w.1+dist z.2 w.2 := add_le_add ((phi_lipschitz k hk).dist_le_mul _ _) le_rfl
      _ ≤ (growthBase k-1)*dist z w+dist z w := add_le_add (mul_le_mul_of_nonneg_left h1 (by linarith)) h2
      _ = _ := by change _ = growthBase k*dist z w; ring
  · exact h1.trans (le_mul_of_one_le_left (dist_nonneg) hM)
lemma liftStep_symm_lipschitz (k : ℝ) (hk : 0 ≤ k) :
    LipschitzWith (⟨growthBase k,by have := growthBase_ge_four k hk; linarith⟩ : NNReal) (liftStep k).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hh := (liftStep_lipschitz k hk).dist_le_mul z.swap w.swap
  change dist (liftStep k z.swap) (liftStep k w.swap) ≤ growthBase k*dist z.swap w.swap at hh
  change dist ((liftStep k).symm z) ((liftStep k).symm w) ≤ growthBase k*dist z w
  simpa only [liftStep_apply,liftStep_symm_apply,Prod.dist_eq,Prod.fst_swap,Prod.snd_swap,
    max_comm] using hh
lemma liftIter_lipschitz (k : ℝ) (hk : 0 ≤ k) (i : ℤ) (z w : ℝ × ℝ) :
    dist (liftIter k i z) (liftIter k i w) ≤ growthBase k^i.natAbs*dist z w := by
  cases i with
  | ofNat n =>
    have hh := ((liftStep_lipschitz k hk).iterate n).dist_le_mul z w
    change dist ((⇑(liftStep k))^[n] z) ((⇑(liftStep k))^[n] w) ≤ growthBase k^n*dist z w at hh
    change dist (liftIter k (n:ℤ) z) (liftIter k (n:ℤ) w) ≤ growthBase k^n*dist z w
    simpa only [liftIter,zpow_natCast,Equiv.Perm.coe_pow] using hh
  | negSucc n =>
    have hh := ((liftStep_symm_lipschitz k hk).iterate (n+1)).dist_le_mul z w
    change dist ((⇑(liftStep k).symm)^[n+1] z) ((⇑(liftStep k).symm)^[n+1] w) ≤ growthBase k^(n+1)*dist z w at hh
    change dist (liftIter k (Int.negSucc n) z) (liftIter k (Int.negSucc n) w) ≤ growthBase k^(n+1)*dist z w
    simpa only [liftIter,zpow_negSucc,← inv_pow,Equiv.Perm.inv_def,Equiv.Perm.coe_pow] using hh
end StandardMapEntropy

end OAI
