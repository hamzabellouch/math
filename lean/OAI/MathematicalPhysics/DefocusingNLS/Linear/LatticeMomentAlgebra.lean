import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingMultiplication

namespace OAI

/-! # Polynomial Fourier moments form a uniform convolution algebra -/

namespace DefocusingNLS

noncomputable def latticeMomentWeight (L : ℝ) (N : ℕ) (n : frequencyLattice) : ℝ :=
  (1 + ‖n‖ / L) ^ N

noncomputable def latticeMomentMass (L : ℝ) (N : ℕ)
    (c : frequencyLattice → ℂ) (n : frequencyLattice) : ℝ := latticeMomentWeight L N n * ‖c n‖

theorem latticeMomentWeight_one_le (L : ℝ) (hL : 1 ≤ L) (N : ℕ) (n : frequencyLattice) :
    1 ≤ latticeMomentWeight L N n := by
  apply one_le_pow₀
  have : 0 ≤ ‖n‖ / L := div_nonneg (norm_nonneg _) (by linarith)
  linarith

theorem latticeMomentWeight_add_le (L : ℝ) (hL : 1 ≤ L) (N : ℕ) (m n : frequencyLattice) :
    latticeMomentWeight L N (m + n) ≤ latticeMomentWeight L N m * latticeMomentWeight L N n := by
  have hLp : 0 < L := by linarith
  have ht := div_le_div_of_nonneg_right (norm_add_le m n) hLp.le
  have hn : 0 ≤ (‖m‖ / L) * (‖n‖ / L) := by positivity
  unfold latticeMomentWeight
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  rw [add_div] at ht
  nlinarith

private theorem positiveLatticeConvolution (A B : frequencyLattice → ℝ)
    (hA : ∀ n, 0 ≤ A n) (hB : ∀ n, 0 ≤ B n) (hsA : Summable A) (hsB : Summable B) :
    (∀ n, Summable (fun m => A m * B (n - m))) ∧
      Summable (fun n => ∑' m, A m * B (n - m)) ∧
      (∑' n, ∑' m, A m * B (n - m)) = (∑' m, A m) * ∑' n, B n := by
  have hs (m : frequencyLattice) : Summable (fun n => A m * B (n - m)) :=
    ((Equiv.subRight m).summable_iff.mpr hsB).mul_left _
  have he (m : frequencyLattice) : (∑' n, A m * B (n - m)) = A m * ∑' n, B n := by
    rw [tsum_mul_left]
    congr 1
    exact (Equiv.subRight m).tsum_eq B
  have hp : Summable (fun p : frequencyLattice × frequencyLattice => A p.1 * B (p.2 - p.1)) := by
    apply (summable_prod_of_nonneg (fun p => mul_nonneg (hA _) (hB _))).mpr
    exact ⟨hs, by simpa only [he] using hsA.mul_right (∑' n, B n)⟩
  have hswap := (summable_prod_of_nonneg (fun p : frequencyLattice × frequencyLattice =>
    mul_nonneg (hA p.2) (hB (p.1 - p.2)))).mp hp.prod_symm
  refine ⟨hswap.1, hswap.2, ?_⟩
  rw [hp.tsum_comm, show (∑' m, ∑' n, A m * B (n - m)) =
    ∑' m, A m * ∑' n, B n from tsum_congr he, tsum_mul_right]

theorem latticeMoment_convolution (L : ℝ) (hL : 1 ≤ L) (N : ℕ)
    (c d : frequencyLattice → ℂ)
    (hc : Summable (latticeMomentMass L N c)) (hd : Summable (latticeMomentMass L N d)) :
    Summable (latticeMomentMass L N (fun n => ∑' m, c m * d (n - m))) ∧
      (∑' n, latticeMomentMass L N (fun n => ∑' m, c m * d (n - m)) n) ≤
        (∑' n, latticeMomentMass L N c n) * ∑' n, latticeMomentMass L N d n := by
  let A := latticeMomentMass L N c
  let B := latticeMomentMass L N d
  have hA (n) : 0 ≤ A n := mul_nonneg (le_trans zero_le_one (latticeMomentWeight_one_le L hL N n)) (norm_nonneg _)
  have hB (n) : 0 ≤ B n := mul_nonneg (le_trans zero_le_one (latticeMomentWeight_one_le L hL N n)) (norm_nonneg _)
  obtain ⟨hrow, hsum, heq⟩ := positiveLatticeConvolution A B hA hB hc hd
  have hnorm (n m : frequencyLattice) : ‖c m * d (n - m)‖ ≤ A m * B (n - m) := by
    rw [norm_mul]
    have hcm : ‖c m‖ ≤ A m := le_mul_of_one_le_left (norm_nonneg _) (latticeMomentWeight_one_le L hL N m)
    have hdm : ‖d (n - m)‖ ≤ B (n - m) := le_mul_of_one_le_left (norm_nonneg _) (latticeMomentWeight_one_le L hL N (n - m))
    exact mul_le_mul hcm hdm (norm_nonneg _) (hA m)
  have hweighted (n m : frequencyLattice) :
      latticeMomentWeight L N n * ‖c m * d (n - m)‖ ≤ A m * B (n - m) := by
    have hw := latticeMomentWeight_add_le L hL N m (n - m)
    rw [add_sub_cancel] at hw
    rw [norm_mul]
    calc
      _ ≤ (latticeMomentWeight L N m * latticeMomentWeight L N (n - m)) * (‖c m‖ * ‖d (n - m)‖) :=
        mul_le_mul_of_nonneg_right hw (by positivity)
      _ = _ := by dsimp only [A, B, latticeMomentMass]; ring
  have hbound (n : frequencyLattice) :
      latticeMomentMass L N (fun n => ∑' m, c m * d (n - m)) n ≤ ∑' m, A m * B (n - m) := by
    have hns := Summable.of_nonneg_of_le (fun m => norm_nonneg (c m * d (n - m))) (hnorm n) (hrow n)
    calc
      _ ≤ latticeMomentWeight L N n * ∑' m, ‖c m * d (n - m)‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hns)
          (le_trans zero_le_one (latticeMomentWeight_one_le L hL N n))
      _ = ∑' m, latticeMomentWeight L N n * ‖c m * d (n - m)‖ := tsum_mul_left.symm
      _ ≤ _ := (hns.mul_left _).tsum_le_tsum (hweighted n) (hrow n)
  have hs := Summable.of_nonneg_of_le
    (fun n => mul_nonneg (le_trans zero_le_one (latticeMomentWeight_one_le L hL N n)) (norm_nonneg _)) hbound hsum
  exact ⟨hs, (hs.tsum_le_tsum hbound hsum).trans_eq heq⟩

end DefocusingNLS

end OAI
