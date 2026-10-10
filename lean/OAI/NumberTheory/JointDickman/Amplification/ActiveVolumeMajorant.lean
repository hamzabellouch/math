import OAI.NumberTheory.JointDickman.Amplification.ActiveFirstForm
import OAI.NumberTheory.JointDickman.Counting.ScaledPeriodicMeans
import OAI.NumberTheory.JointDickman.Amplification.IndependentRegularityLoss

namespace OAI

/-! # A periodic majorant for the active Cauchy volume -/

namespace JointDickman
open Finset

noncomputable def activeVolumeMajorant (B T N : ℕ) : ℝ :=
  ∑ D ∈ (auxiliaryPrimes B).powerset,
    coefficientWeight B (∏ p ∈ D, p) *
      ((∑ m ∈ range (N/(T*(∏ p ∈ D, p))+1), baseArithmeticResidueWeight B m)/(N : ℝ))

theorem baseArithmeticResidueWeight_nonneg (B n : ℕ) : 0 ≤ baseArithmeticResidueWeight B n := by
  unfold baseArithmeticResidueWeight residueBaseWeight
  exact mul_nonneg (Real.rpow_nonneg (by unfold auxiliaryRatio; positivity) _) (by positivity)

theorem arithmeticResidueWeight_le_base (B L : ℕ) (τ C : ℝ) (n : ℕ) :
    arithmeticResidueWeight B L τ C n ≤ baseArithmeticResidueWeight B n := by
  unfold arithmeticResidueWeight regularResidueWeight baseArithmeticResidueWeight
  split_ifs
  · rfl
  · exact baseArithmeticResidueWeight_nonneg B n

theorem active_residue_prefix_le (B L : ℕ) (τ C : ℝ) {d : ℕ} (hd : 0 < d) (N : ℕ) :
    (∑ m ∈ range N, if d*m < N then arithmeticResidueWeight B L τ C m else 0) ≤
      ∑ m ∈ range (N/d+1), baseArithmeticResidueWeight B m := by
  classical
  have hs : (range N).filter (fun m => d*m < N) ⊆ range (N/d+1) := by
    intro m hm
    have hmul : m*d ≤ N := by simpa only [mul_comm] using (mem_filter.mp hm).2.le
    have hdiv := (Nat.le_div_iff_mul_le hd).mpr hmul
    exact mem_range.mpr (by omega)
  rw [← sum_filter]
  calc
    _ ≤ ∑ m ∈ (range N).filter (fun m => d*m < N), baseArithmeticResidueWeight B m :=
      sum_le_sum (fun m _ => arithmeticResidueWeight_le_base B L τ C m)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hs (fun m _ _ => baseArithmeticResidueWeight_nonneg B m)

theorem activeFirstFormVolume_le_majorant (B L : ℕ) (τ C : ℝ) (u : ℕ → ℝ)
    {T : ℕ} (hT : 0 < T) (N : ℕ) (hu : ∀ c, u c ∈ Set.Icc (0 : ℝ) 1) :
    activeFirstFormVolume B L τ C u T N ≤ activeVolumeMajorant B T N := by
  classical
  unfold activeFirstFormVolume activeVolumeMajorant
  rw [sum_product, sum_div]
  apply sum_le_sum
  intro D hD
  let c := ∏ p ∈ D, p
  have hcpos : 0 < c := prod_pos (fun p hp =>
    (auxiliaryPrimes_prime B p (mem_powerset.mp hD hp)).pos)
  have hs := active_residue_prefix_le B L τ C (Nat.mul_pos hT hcpos) N
  have hc : u c * regularCoefficientWeight B L τ C c ≤ coefficientWeight B c :=
    (mul_le_of_le_one_left (regularCoefficientWeight_nonneg B L τ C c) (hu c).2).trans
      (regularCoefficientWeight_le B L τ C c)
  have he : (∑ m ∈ range N, activeFirstFormWeight B L τ C u T N D m) =
      (u c * regularCoefficientWeight B L τ C c) *
        ∑ m ∈ range N, if T*c*m < N then arithmeticResidueWeight B L τ C m else 0 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro m _
    unfold activeFirstFormWeight firstFormWeight
    dsimp only [c]
    split_ifs <;> simp only [mul_zero]
  rw [he, mul_div_assoc]
  apply mul_le_mul hc (div_le_div_of_nonneg_right hs (Nat.cast_nonneg N))
  · apply div_nonneg _ (Nat.cast_nonneg N)
    apply sum_nonneg
    intro m _
    split_ifs
    · exact regularResidueWeight_nonneg B L τ C _
    · rfl
  · exact coefficientWeight_nonneg B c

end JointDickman

end OAI
