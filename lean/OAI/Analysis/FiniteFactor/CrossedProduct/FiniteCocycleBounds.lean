import OAI.Analysis.FiniteFactor.CrossedProduct.StageOperator
import OAI.Analysis.FiniteFactor.CrossedProduct.ConvolutionCocycle

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
noncomputable section

theorem SourceAngles.le_one {θ : SourceCoordinate → ℝ} (hθ : SourceAngles θ) (i : SourceCoordinate) :
    θ i ≤ 1 := by
  apply (hθ i).2.trans
  apply (div_le_one (mul_pos (sourceBlockSize_pos i.1) (sourceCutoff_pos i.1))).mpr
  change (2 : ℝ) ≤ (sourceBlockSize i.1 : ℝ) * (sourceStageState i.1).K
  have hm : (100 : ℝ) ≤ sourceBlockSize i.1 := by exact_mod_cast (sourceStage i.1).m_ge_100
  have hK : (1 : ℝ) ≤ (sourceStageState i.1).K := by exact_mod_cast (sourceStageState i.1).K_ge
  nlinarith

/-- Earlier coordinates contribute at most K+1 in absolute floor value. -/
theorem sourceCoordinateFloor_abs_le (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (K : ℕ) (k : ℤ) (hk : |(k : ℝ)| ≤ K) (x : SourceCoordinate → ℝ)
    (hx : ∀ i, x i ∈ Set.Ico 0 1) (i : SourceCoordinate) :
    |(coordinateFloor θ k x i : ℝ)| ≤ (K : ℝ)+1 := by
  have hm : |(k : ℝ)*θ i| ≤ K := by
    rw [abs_mul,abs_of_nonneg (hθ.nonneg i)]
    exact (mul_le_mul_of_nonneg_left (hθ.le_one i) (abs_nonneg _)).trans_eq (mul_one _)
      |>.trans hk
  have hlow := (abs_le.mp hm).1
  have hhigh := (abs_le.mp hm).2
  have hfl := Int.floor_le (x i+(k : ℝ)*θ i)
  have hfu := Int.lt_floor_add_one (x i+(k : ℝ)*θ i)
  change |(Int.floor (x i+(k : ℝ)*θ i) : ℝ)| ≤ _
  apply abs_le.mpr
  constructor <;> linarith [(hx i).1,(hx i).2]

theorem sourcePrefix_logWeight_sum (j : ℕ) :
    (∑ i ∈ CouplingParameters.blockPrefix sourceBlockSize j, sourceLogWeight i) = (sourceStageState j).B := by
  rw [CouplingParameters.blockPrefix,Finset.sum_sigma,sourceStage_previous_weight]
  change (∑ s ∈ Finset.range j, ∑ _i : Fin (sourceBlockSize s), (sourceStage s).C) = _
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro s _
  exact mul_comm _ _

/-- If later floors vanish, the actual full source logarithm is bounded by
the recursively recorded earlier-block sum. -/
theorem sourceLog_finite_bound (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (j : ℕ) (k : ℤ) (hk : |(k : ℝ)| ≤ (sourceStageState j).K)
    (x : SourceCoordinate → ℝ) (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hzero : ∀ i : SourceCoordinate, j ≤ i.1 → coordinateFloor θ k x i = 0) :
    |sourceLog θ sourceLogWeight k x| ≤ (((sourceStageState j).K : ℝ)+1)*(sourceStageState j).B := by
  have he : sourceLog θ sourceLogWeight k x =
      ∑ i ∈ CouplingParameters.blockPrefix sourceBlockSize j,
        sourceLogWeight i*(coordinateFloor θ k x i : ℝ) := by
    apply tsum_eq_sum
    intro i hi
    have hh : j ≤ i.1 := by
      have := (CouplingParameters.mem_blockPrefix sourceBlockSize j i).not.mp hi
      omega
    rw [hzero i hh,Int.cast_zero,mul_zero]
  rw [he,← sourcePrefix_logWeight_sum,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul,abs_of_nonneg (sourceLogWeight_nonneg i),mul_comm (((sourceStageState j).K : ℝ)+1)]
  exact mul_le_mul_of_nonneg_left (sourceCoordinateFloor_abs_le θ hθ _ k hk x hx i) (sourceLogWeight_nonneg i)

end
end FiniteFactor

end OAI
