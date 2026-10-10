import OAI.Analysis.FiniteFactor.CrossedProduct.Stages
import OAI.Analysis.FiniteFactor.CrossedProduct.Powers
import OAI.Analysis.FiniteFactor.Coupling.BlockLimit

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Topology ENNReal
noncomputable section

def sourceBlockSize (s : ℕ) : ℕ := (sourceStage s).m
abbrev SourceCoordinate := CouplingParameters.BlockCoordinate sourceBlockSize

def sourceLogWeight (i : SourceCoordinate) : ℝ := (sourceStage i.1).C

def SourceAngles (θ : SourceCoordinate → ℝ) : Prop :=
  let realGroup : GroupWithZero ℝ :=
    (@DivisionRing.toDivisionSemiring ℝ Real.instField.toDivisionRing).toGroupWithZero
  let realOrder : LE ℝ := @Preorder.toLE ℝ Real.partialOrder.toPreorder
  ∀ i : SourceCoordinate,
    let block : ℝ := @Nat.cast ℝ Real.instNatCast (sourceBlockSize i.1)
    let cutoff : ℝ := @Nat.cast ℝ Real.instNatCast (sourceStageState i.1).K
    let denominator : ℝ := @Mul.mul ℝ Real.instMul block cutoff
    let lower : ℝ :=
      @Div.div ℝ realGroup.toDiv (@One.one ℝ Real.instOne) denominator
    let upper : ℝ :=
      @Div.div ℝ realGroup.toDiv (@Nat.cast ℝ Real.instNatCast 2) denominator
    @LE.le ℝ realOrder lower (θ i) ∧ @LE.le ℝ realOrder (θ i) upper

theorem sourceBlockSize_pos (s : ℕ) : (0 : ℝ) < sourceBlockSize s := by
  exact_mod_cast (show 0 < (sourceStage s).m by have := (sourceStage s).m_ge_100; omega)

theorem sourceCutoff_pos (s : ℕ) : (0 : ℝ) < (sourceStageState s).K := by
  exact_mod_cast (show 0 < (sourceStageState s).K by have := (sourceStageState s).K_ge; omega)

theorem sourceCutoff_ge_pow (s : ℕ) : 2^s ≤ (sourceStageState s).K := by
  induction s with
  | zero => exact (sourceStageState 0).K_ge
  | succ s ih =>
    rw [pow_succ]
    have hh : 2^s*2 ≤ 2*(sourceStageState s).K := by simpa [mul_comm] using Nat.mul_le_mul_left 2 ih
    exact hh.trans (sourceStage_cutoff_growth s).le

theorem sourceCutoff_reciprocal_summable : Summable (fun s => 1/((sourceStageState s).K : ℝ)) := by
  apply (summable_geometric_of_lt_one (r := (1/2 : ℝ)) (by norm_num) (by norm_num)).of_nonneg_of_le
  · intro s; positivity
  · intro s
    have hpow : (2 : ℝ)^s ≤ (sourceStageState s).K := by exact_mod_cast sourceCutoff_ge_pow s
    have hh := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (2 : ℝ)^s) hpow
    simpa [one_div_pow] using hh

theorem SourceAngles.nonneg {θ : SourceCoordinate → ℝ} (hθ : SourceAngles θ)
    (i : SourceCoordinate) :
    @LE.le ℝ (@Preorder.toLE ℝ Real.partialOrder.toPreorder)
      (@Zero.zero ℝ Real.instZero) (θ i) :=
  let realGroup : GroupWithZero ℝ :=
    (@DivisionRing.toDivisionSemiring ℝ Real.instField.toDivisionRing).toGroupWithZero
  let realOrder : Preorder ℝ := Real.partialOrder.toPreorder
  let realStrict : @PosMulStrictMono ℝ Real.instMul Real.instZero realOrder :=
    @IsStrictOrderedRing.toPosMulStrictMono ℝ Real.semiring Real.partialOrder
      Real.instIsStrictOrderedRing
  let realReflect : @PosMulReflectLT ℝ Real.instMul Real.instZero realOrder :=
    @PosMulMono.toPosMulReflectLT ℝ Real.instMul Real.instZero Real.linearOrder
      (@IsOrderedRing.toPosMulMono ℝ Real.semiring Real.partialOrder
        Real.instIsOrderedRing)
  let block : ℝ := @Nat.cast ℝ Real.instNatCast (sourceBlockSize i.1)
  let cutoff : ℝ := @Nat.cast ℝ Real.instNatCast (sourceStageState i.1).K
  let denominator : ℝ := @Mul.mul ℝ Real.instMul block cutoff
  let lower : ℝ :=
    @Div.div ℝ realGroup.toDiv (@One.one ℝ Real.instOne) denominator
  let upper : ℝ :=
    @Div.div ℝ realGroup.toDiv (@Nat.cast ℝ Real.instNatCast 2) denominator
  let zeroReal : ℝ := @Zero.zero ℝ Real.instZero
  @le_trans ℝ realOrder zeroReal lower (θ i)
    (@le_of_lt ℝ realOrder zeroReal lower
      ((@one_div_pos ℝ realGroup Real.partialOrder realReflect denominator).mpr
        (@mul_pos ℝ realGroup.toMulZeroClass (a := block) (b := cutoff)
          realOrder realStrict (sourceBlockSize_pos i.1) (sourceCutoff_pos i.1))))
    (@And.left
      (@LE.le ℝ realOrder.toLE lower (θ i))
      (@LE.le ℝ realOrder.toLE (θ i) upper)
      (hθ i))

theorem sourceLogWeight_nonneg (i : SourceCoordinate) : 0 ≤ sourceLogWeight i :=
  le_max_of_le_right (sq_nonneg _)

theorem exists_sourceAngles : ∃ θ : SourceCoordinate → ℝ, SourceAngles θ := by
  refine ⟨fun i => 1/((sourceBlockSize i.1 : ℝ)*(sourceStageState i.1).K), ?_⟩
  intro i
  exact ⟨le_rfl, div_le_div_of_nonneg_right (by norm_num)
    (mul_pos (sourceBlockSize_pos i.1) (sourceCutoff_pos i.1)).le⟩

/-- The source interval bounds imply actual angle summability for every
realization, with the recursively constructed sizes and cutoffs. -/
theorem SourceAngles.summable {θ : SourceCoordinate → ℝ} (hθ : SourceAngles θ) :
    Summable (fun i => |θ i|) := by
  have hs : Summable θ := by
    rw [summable_sigma_of_nonneg hθ.nonneg]
    refine ⟨fun s => (hasSum_fintype (fun t => θ ⟨s,t⟩)).summable, ?_⟩
    apply (sourceCutoff_reciprocal_summable.mul_left 2).of_nonneg_of_le
    · intro s; exact tsum_nonneg (fun t => hθ.nonneg ⟨s,t⟩)
    · intro s
      rw [tsum_fintype]
      have hh := Finset.sum_le_sum (fun (i : Fin (sourceBlockSize s)) (_ : i ∈ Finset.univ) => (hθ ⟨s,i⟩).2)
      have he : (∑ _i : Fin (sourceBlockSize s), 2/((sourceBlockSize s : ℝ)*(sourceStageState s).K)) =
          2*(1/((sourceStageState s).K : ℝ)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp [(sourceBlockSize_pos s).ne', (sourceCutoff_pos s).ne']
      exact hh.trans_eq he
  simpa only [abs_of_nonneg (hθ.nonneg _)] using hs

/-- Each source block contributes at least one to the weighted-angle sum,
using C_s >= K_s^2 and the exact lower endpoint 1/(m_s*K_s). -/
theorem SourceAngles.block_weight_lower {θ : SourceCoordinate → ℝ} (hθ : SourceAngles θ) (s : ℕ) :
    1 ≤ ∑ t : Fin (sourceBlockSize s), sourceLogWeight ⟨s,t⟩*θ ⟨s,t⟩ := by
  have hc : ((sourceStageState s).K : ℝ)^2 ≤ (sourceStage s).C := le_max_right _ _
  have hK : (1 : ℝ) ≤ (sourceStageState s).K := by exact_mod_cast (sourceStageState s).K_ge
  have hlo : 1 ≤ (sourceStage s).C/((sourceStageState s).K : ℝ) := by
    apply (le_div_iff₀ (sourceCutoff_pos s)).mpr
    nlinarith
  have hh : (∑ t : Fin (sourceBlockSize s), sourceLogWeight ⟨s,t⟩ *
      (1/((sourceBlockSize s : ℝ)*(sourceStageState s).K))) ≤
      ∑ t : Fin (sourceBlockSize s), sourceLogWeight ⟨s,t⟩*θ ⟨s,t⟩ :=
    Finset.sum_le_sum (fun (t : Fin (sourceBlockSize s)) (_ : t ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hθ ⟨s,t⟩).1 (sourceLogWeight_nonneg ⟨s,t⟩))
  have he : (∑ t : Fin (sourceBlockSize s), sourceLogWeight ⟨s,t⟩ *
      (1/((sourceBlockSize s : ℝ)*(sourceStageState s).K))) =
      (sourceStage s).C/((sourceStageState s).K : ℝ) := by
    simp only [sourceLogWeight, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [(sourceBlockSize_pos s).ne', (sourceCutoff_pos s).ne']
  rw [he] at hh
  exact hlo.trans hh

theorem SourceAngles.weighted_prefix_diverges {θ : SourceCoordinate → ℝ} (hθ : SourceAngles θ) :
    Tendsto (fun q => ∑ i ∈ CouplingParameters.blockPrefix sourceBlockSize q, sourceLogWeight i*θ i)
      atTop atTop := by
  apply tendsto_atTop_mono (f := fun q : ℕ => (q : ℝ)) _ tendsto_natCast_atTop_atTop
  intro q
  rw [CouplingParameters.blockPrefix, Finset.sum_sigma]
  calc
    (q : ℝ) = ∑ _s ∈ Finset.range q, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun s _ => hθ.block_weight_lower s)

/-- The recursively staged concrete source operator is nonzero, injective,
bounded by one, and norm-quasinilpotent for every admissible angle realization.
No factor, ergodicity, sampling, or invariant-projection conclusion is asserted. -/
theorem staged_sourceOperator_properties (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ) :
    let T := sourceOperator θ sourceLogWeight hθ.nonneg sourceLogWeight_nonneg
    T ≠ 0 ∧ Function.Injective T ∧ ‖T‖ ≤ 1 ∧
      Tendsto (fun n : ℕ => ‖T^n‖^(1/(n : ℝ))) atTop (𝓝 0) := by
  refine ⟨sourceOperator_ne_zero _ _ _ _, sourceOperator_injective _ _ _ _,
    sourceOperator_norm_le_one _ _ _ _, ?_⟩
  exact sourceOperator_norm_quasinilpotent _ _ _ _ hθ.summable
    (CouplingParameters.blockPrefix sourceBlockSize) hθ.weighted_prefix_diverges

end
end FiniteFactor

end OAI
