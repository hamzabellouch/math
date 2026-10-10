import OAI.NumberTheory.Ostmann.Arithmetic.BulkLogContinuity
import OAI.NumberTheory.Ostmann.Arithmetic.BulkIntegrands
import OAI.NumberTheory.Ostmann.Arithmetic.RealNodeSupport
import OAI.NumberTheory.Ostmann.Arithmetic.MovingKernelPair

namespace OAI

/-! # The full original kernel on real bulk coordinates -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap ComplexConjugate

noncomputable def realValueFullSupport {σ : Type*} (value : σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (X lo hi L R : ℝ) : Prop :=
  realValueNodeSupport value childBound pivotBound T L R ∧
    ∀ j, T.realValueLeafModuli value L R j / X ∈ Set.Icc lo hi

noncomputable def realValueSupportFlag {σ : Type*} (value : σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (X lo hi L R : ℝ) : ℂ :=
  if realValueFullSupport value childBound pivotBound T X lo hi L R then 1 else 0

noncomputable def realValueKernel {σ : Type*} (value : σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) : ℂ :=
  realValueSupportFlag value childBound pivotBound T X lo hi L R *
    realValueSmoothWeight value T ψ X lo hi hlo hhi φ G L R

theorem realValueSupportFlag_norm {σ : Type*} (value : σ → ℝ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (X lo hi L R : ℝ) : ‖realValueSupportFlag value childBound pivotBound T X lo hi L R‖ ≤ 1 := by
  unfold realValueSupportFlag
  split_ifs <;> norm_num

/-- The real extension has precisely the old arithmetic gates and windows. -/
theorem realValueSupportFlag_nat {σ : Type*} (value : σ → ℕ) (hv : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (X lo hi L R : ℝ) :
    realValueSupportFlag (fun i => (value i : ℝ)) childBound pivotBound T X lo hi L R =
      movingRealGateWeight value T
        (T.formulaNodes value hv childBound pivotBound hf (.prime false) (.prime true))
        X lo hi (topGiantReal L R) := by
  have hn := realValueNodeSupport_nat value hv childBound pivotBound T hf
    (.prime false) (.prime true) (topGiantReal L R)
  simp only [HistoryFormula.realEval_prime, topGiantReal, Bool.false_eq_true, ite_false, ite_true] at hn
  simp only [realValueSupportFlag, realValueFullSupport, movingRealGateWeight,
    movingArchimedeanFlag, movingRealWindowFlag, MovingSlotData.realValueLeafModuli_nat,
    topGiantReal, Bool.false_eq_true, ite_false, ite_true]
  rw [hn]
  split_ifs <;> simp_all

theorem realValueKernel_nat {σ : Type*} (value : σ → ℕ) (hv : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hf : T.Frequencies (· ≠ 0)) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) :
    realValueKernel (fun i => (value i : ℝ)) childBound pivotBound T ψ X lo hi hlo hhi φ G L R =
      movingRealKernel value T
        (T.formulaNodes value hv childBound pivotBound hf (.prime false) (.prime true))
        ψ X lo hi hlo hhi φ G L R := by
  rw [realValueKernel, realValueSupportFlag_nat value hv childBound pivotBound T hf,
    realValueSmoothWeight_nat]
  rfl

theorem MovingSlotReversal.continuous_bulkLogComposite {σ : Type*}
    (base : σ → ℝ) (S : Finset σ) (s : MovingSlotReversal σ)
    (L R : (σ → ℝ) → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => s.realCompositePivot (bulkLogValues base S x) (L x) (R x)) := by
  unfold realCompositePivot
  exact (((continuous_const.mul
    (continuous_realSlotProduct _ (continuous_bulkLogValues base S) s.rightSlots)).mul hR).sub
    ((continuous_const.mul
    (continuous_realSlotProduct _ (continuous_bulkLogValues base S) s.leftSlots)).mul hL)).div_const _

theorem isClosed_bulkLogNodeSupport {σ : Type*} (base : σ → ℝ) (S : Finset σ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hT : ∀ i ∈ S, T.CompensationAbsent i) (L R : (σ → ℝ) → ℝ)
    (hL : Continuous L) (hR : Continuous R) :
    IsClosed {x | realValueNodeSupport (bulkLogValues base S x) childBound pivotBound T (L x) (R x)} := by
  induction T generalizing L R with
  | leaf => simpa only [realValueNodeSupport, Set.ofPred_true] using isClosed_univ
  | @node n s CL CR u left right ihL ihR =>
    let step := MovingSlotData.step s CL CR u left right false
    have hQ := step.continuous_bulkLogComposite base S L R hL hR
    have hp := step.continuous_bulkLogPivot base S (fun i hi => (hT i hi).1) L R hL hR
    have hgap := hR.mul (continuous_realSlotProduct _ (continuous_bulkLogValues base S) CR)
    exact (isClosed_le continuous_const hQ).inter
      ((isClosed_le hQ continuous_const).inter ((isClosed_le continuous_const hgap).inter
        ((ihL (fun i hi => (hT i hi).2.1) _ L hp hL).inter
          (ihR (fun i hi => (hT i hi).2.2) _ R hp hR))))

theorem isClosed_bulkLogFullSupport {σ : Type*} (base : σ → ℝ) (S : Finset σ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hT : ∀ i ∈ S, T.CompensationAbsent i) (X lo hi : ℝ) (L R : (σ → ℝ) → ℝ)
    (hL : Continuous L) (hR : Continuous R) :
    IsClosed {x | realValueFullSupport (bulkLogValues base S x) childBound pivotBound T X lo hi (L x) (R x)} := by
  have hw : IsClosed {x | ∀ j, T.realValueLeafModuli (bulkLogValues base S x) (L x) (R x) j / X ∈ Set.Icc lo hi} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro j
    exact isClosed_Icc.preimage ((T.continuous_bulkLogLeafModuli base S hT L R hL hR j).div_const X)
  exact (isClosed_bulkLogNodeSupport base S childBound pivotBound T hT L R hL hR).inter hw

theorem measurable_bulkLogKernel {σ : Type*} [Fintype σ] (base : σ → ℝ) (S : Finset σ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n)
    (hT : ∀ i ∈ S, T.CompensationAbsent i) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (L R : ℝ) : Measurable (fun x => realValueKernel (bulkLogValues base S x)
      childBound pivotBound T ψ X lo hi hlo hhi φ G L R) := by
  have hg : Measurable (fun x => realValueSupportFlag (bulkLogValues base S x)
      childBound pivotBound T X lo hi L R) := by
    unfold realValueSupportFlag
    exact Measurable.ite
      (isClosed_bulkLogFullSupport base S childBound pivotBound T hT X lo hi
        (fun _ => L) (fun _ => R) continuous_const continuous_const).measurableSet
      measurable_const measurable_const
  exact hg.mul (continuous_bulkLogSmoothWeight base S T hT ψ X lo hi hlo hhi φ G B D hB hD
    hφ hlip hout (fun _ => L) (fun _ => R) continuous_const continuous_const).measurable

theorem realValueKernel_norm {σ : Type*} (value : σ → ℝ) (i : σ)
    (childBound pivotBound : ℕ → ℕ) {n : ℕ} (T : MovingSlotData σ n) (hT : T.CompensationAbsent i)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : T.Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L R : ℝ) :
    ‖realValueKernel value childBound pivotBound T ψ X lo hi hlo hhi φ G L R‖ ≤
      movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1) := by
  rw [realValueKernel, norm_mul]
  have hb := realValueSmoothWeight_norm value i T hT ψ X lo hi V hlo hhi hV
    φ G B D hB hD hφ hlip hout L R
  exact (mul_le_mul_of_nonneg_right (realValueSupportFlag_norm _ _ _ _ _ _ _ _ _) (norm_nonneg _)).trans
    (by simpa only [one_mul] using hb)

noncomputable def bulkLogKernelIntegrand {σ : Type*} [Fintype σ]
    (base : σ → ℝ) (S : Finset σ) (childBound pivotBound : ℕ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (hT : ∀ i ∈ S, T.CompensationAbsent i)
    (i : σ) (hiS : i ∈ S) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (hV : T.Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L R : ℝ) : BulkIntegrand σ where
  toFun x := realValueKernel (bulkLogValues base S x) childBound pivotBound T ψ X lo hi hlo hhi φ G L R
  measurable := measurable_bulkLogKernel base S childBound pivotBound T hT ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout L R
  bounded := by
    let C := movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)
    have hb (x : σ → ℝ) := realValueKernel_norm (bulkLogValues base S x) i childBound pivotBound
      T (hT i hiS) ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout L R
    exact ⟨C, (norm_nonneg _).trans (hb base), hb⟩

end Ostmann

end OAI
