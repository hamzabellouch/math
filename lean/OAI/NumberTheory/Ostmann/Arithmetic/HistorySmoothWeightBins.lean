import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightCutoff
import OAI.NumberTheory.Ostmann.Construction.History

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic
open Construction
open scoped ContDiff

def sourceBulkHalf (b : ℕ) (h : Bool) (q : SmallSlot) : Prop :=
  q.role = .bulk ∧ if h then b ≤ q.origin ∧ q.origin < 2 * b else q.origin < b

def sourceSpectatorHalf (s : ℕ) (h : Bool) (i : ℕ) : Prop :=
  if h then s ≤ i ∧ i < 2 * s else i < s

instance sourceBulkHalfDecidable (b : ℕ) (h : Bool) (q : SmallSlot) : Decidable (sourceBulkHalf b h q) := by
  unfold sourceBulkHalf
  infer_instance

instance sourceSpectatorHalfDecidable (s : ℕ) (h : Bool) (i : ℕ) : Decidable (sourceSpectatorHalf s h i) := by
  unfold sourceSpectatorHalf
  infer_instance

def realStateBins (b s : ℕ) (tb td : ℝ) (a : State) (outside : List ℕ)
    (y : Fin a.small.length → ℝ) (z : Fin outside.length → ℝ) : ℝ := by
  classical
  exact ∏ h : Bool,
    smoothPartition ((∑ i, if sourceBulkHalf b h (a.small.get i) then Real.log (y i) else 0) - tb) *
    smoothPartition ((∑ i, if sourceSpectatorHalf s h i.val then Real.log (z i) else 0) - td)

def sourceStateBins (b s : ℕ) (tb td : ℝ) (outside : List ℕ) (a : State) : ℝ :=
  realStateBins b s tb td a outside (fun i => (a.small.get i).value) (fun i => outside.get i)

theorem realStateBins_bounds (b s : ℕ) (tb td : ℝ) (a : State) (outside : List ℕ)
    (y : Fin a.small.length → ℝ) (z : Fin outside.length → ℝ) :
    0 ≤ realStateBins b s tb td a outside y z ∧ realStateBins b s tb td a outside y z ≤ 1 := by
  classical
  unfold realStateBins
  constructor
  · exact Finset.prod_nonneg (fun h _ => mul_nonneg (smoothPartition_nonneg _) (smoothPartition_nonneg _))
  · apply Finset.prod_le_one₀
    · exact fun h _ => mul_nonneg (smoothPartition_nonneg _) (smoothPartition_nonneg _)
    · intro h _
      exact (mul_le_mul (smoothPartition_le_one _) (smoothPartition_le_one _)
        (smoothPartition_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem realStateBins_support (b s : ℕ) (tb td : ℝ) (a : State) (outside : List ℕ)
    (y : Fin a.small.length → ℝ) (z : Fin outside.length → ℝ)
    (hb : realStateBins b s tb td a outside y z ≠ 0) :
    ∀ h : Bool,
      |(∑ i, if sourceBulkHalf b h (a.small.get i) then Real.log (y i) else 0) - tb| ≤ 1 ∧
      |(∑ i, if sourceSpectatorHalf s h i.val then Real.log (z i) else 0) - td| ≤ 1 := by
  classical
  intro h
  have hterm := (Finset.prod_ne_zero_iff.mp hb) h (Finset.mem_univ h)
  have hφ (t : ℝ) (ht : smoothPartition t ≠ 0) : |t| ≤ 1 := by
    have ht' := smoothPartition_support_subset ht
    exact abs_le.mpr ⟨ht'.1.le,ht'.2.le⟩
  exact ⟨hφ _ (mul_ne_zero_iff.mp hterm).1,hφ _ (mul_ne_zero_iff.mp hterm).2⟩

theorem realStateBins_contDiffAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b s : ℕ) (tb td : ℝ) (a : State) (outside : List ℕ)
    (y : E → Fin a.small.length → ℝ) (z : E → Fin outside.length → ℝ) (x : E)
    (hy : ∀ i, ContDiffAt ℝ ∞ (fun t => y t i) x)
    (hz : ∀ i, ContDiffAt ℝ ∞ (fun t => z t i) x)
    (hyp : ∀ i, 0 < y x i) (hzp : ∀ i, 0 < z x i) :
    ContDiffAt ℝ ∞ (fun t => realStateBins b s tb td a outside (y t) (z t)) x := by
  classical
  unfold realStateBins
  apply contDiffAt_prod
  intro h _
  apply ContDiffAt.mul
  · apply smoothPartition_contDiff.contDiffAt.comp x
    apply ContDiffAt.sub _ contDiffAt_const
    apply ContDiffAt.sum
    intro i _
    by_cases hi : sourceBulkHalf b h (a.small.get i)
    · simpa only [ite_eq_left hi] using (hy i).log (hyp i).ne'
    · simp only [ite_eq_right hi]
      exact contDiffAt_const
  · apply smoothPartition_contDiff.contDiffAt.comp x
    apply ContDiffAt.sub _ contDiffAt_const
    apply ContDiffAt.sum
    intro i _
    by_cases hi : sourceSpectatorHalf s h i.val
    · simpa only [ite_eq_left hi] using (hz i).log (hzp i).ne'
    · simp only [ite_eq_right hi]
      exact contDiffAt_const

end Ostmann.Arithmetic

end

end OAI
