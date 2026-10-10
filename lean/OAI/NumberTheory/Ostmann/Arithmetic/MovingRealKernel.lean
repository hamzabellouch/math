import Mathlib.MeasureTheory.Integral.Prod
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRealSmooth

namespace OAI

/-! # Measurability and uniform bounds for the original two-giant kernel -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate SchwartzMap
open MeasureTheory

theorem HistoryFormula.continuous_realEval {σ : Type*} (F : HistoryFormula σ) :
    Continuous F.realEval := by
  unfold realEval
  simp only [MvPolynomial.eval₂_eq_eval_map]
  exact (MvPolynomial.continuous_eval _).div_const _

theorem WordTransferGuard.isClosed_archimedeanAt {σ : Type*} (g : WordTransferGuard σ) :
    IsClosed {x | g.archimedeanAt x} :=
  (isClosed_le continuous_const g.pivot.continuous_realEval).inter
    ((isClosed_le g.pivot.continuous_realEval continuous_const).inter
      (isClosed_le continuous_const g.rightProduct.continuous_realEval))

theorem isClosed_movingArchimedeanGate (nodes : List MovingFormulaNode) :
    IsClosed {x | movingArchimedeanGate nodes x} := by
  induction nodes with
  | nil => simpa only [movingArchimedeanGate, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, Set.ofPred_true] using isClosed_univ
  | cons f nodes ih =>
    simpa only [movingArchimedeanGate, List.forall_mem_cons, Set.ofPred_and] using
      f.guard.isClosed_archimedeanAt.inter ih

theorem continuous_topGiantReal : Continuous (fun x : ℝ × ℝ => topGiantReal x.1 x.2) := by
  apply continuous_pi
  intro b
  cases b
  · exact continuous_fst
  · exact continuous_snd

theorem measurable_movingRealGateWeight {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (X lo hi : ℝ) :
    Measurable (fun x : ℝ × ℝ => movingRealGateWeight value T nodes X lo hi (topGiantReal x.1 x.2)) := by
  have ha : Measurable (fun x : ℝ × ℝ => movingArchimedeanFlag nodes (topGiantReal x.1 x.2)) := by
    apply Measurable.ite _ measurable_const measurable_const
    exact ((isClosed_movingArchimedeanGate nodes).preimage continuous_topGiantReal).measurableSet
  have hw : Measurable (fun x : ℝ × ℝ => movingRealWindowFlag value T X lo hi x.1 x.2) := by
    apply Measurable.ite _ measurable_const measurable_const
    have hc : IsClosed {x : ℝ × ℝ | ∀ i, T.realLeafModuli value x.1 x.2 i / X ∈ Set.Icc lo hi} := by
      simpa only [Set.ofPred_forall, Set.preimage] using isClosed_iInter (fun i : TreeLeafIndex n =>
        isClosed_Icc.preimage ((T.continuous_realLeafModuli value Prod.fst Prod.snd
          continuous_fst continuous_snd i).div_const X))
    exact hc.measurableSet
  exact ha.mul hw

theorem movingRealFourierWeight_norm {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (L R : ℝ) :
    ‖movingRealFourierWeight value T ψ X lo hi hlo hhi L R‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) := by
  have he : (SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) =
      ∏ _i : TreeLeafIndex n, SchwartzMap.seminorm ℝ 0 0 ψ := by
    simp only [Finset.prod_const, Finset.card_univ, card_treeLeafIndex]
  rw [he, movingRealFourierWeight, norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro i _
  have hb := (fourierPolynomialFactor Polynomial.X ψ (T.leafFrequencies i) lo hi hlo hhi).norm_value
    (T.realLeafModuli value L R i / X)
  change ‖(fourierPolynomialFactor Polynomial.X ψ (T.leafFrequencies i) lo hi hlo hhi).value
    (T.realLeafModuli value L R i / X)‖ ≤ SchwartzMap.seminorm ℝ 0 0 ψ at hb
  split_ifs
  · simpa only [Complex.norm_conj] using hb
  · exact hb

theorem movingRealNodeCutoff_norm {σ : Type*} (value : σ → ℕ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hφ : ∀ x, |φ x| ≤ B)
    {n : ℕ} (T : MovingSlotData σ n) (L R : ℝ) :
    ‖movingRealNodeCutoff value φ G T L R‖ ≤ B ^ (2 ^ n - 1) := by
  have hb (G x : ℝ) : ‖(positiveLogCutoff φ G x : ℂ)‖ ≤ B := by
    unfold positiveLogCutoff
    split_ifs
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using hφ _
    · simpa only [Complex.ofReal_zero, norm_zero] using hB
  induction T generalizing L R with
  | leaf => simp [movingRealNodeCutoff]
  | @node n s CL CR u left right ihL ihR =>
    simp only [movingRealNodeCutoff, norm_mul]
    calc
      _ ≤ (B * B ^ (2 ^ n - 1)) * B ^ (2 ^ n - 1) := by
        apply mul_le_mul _ (ihR _ _) (norm_nonneg _) (mul_nonneg hB (pow_nonneg hB _))
        exact mul_le_mul (hb _ _) (ihL _ _) (norm_nonneg _) hB
      _ = B ^ (2 ^ (n + 1) - 1) := by
        rw [← pow_succ', ← pow_add]
        congr 1
        have := Nat.one_le_two_pow (n := n)
        rw [pow_succ]
        omega

theorem movingRealSmoothWeight_norm {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hφ : ∀ x, |φ x| ≤ B) (L R : ℝ) :
    ‖movingRealSmoothWeight value T ψ X lo hi hlo hhi φ G L R‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) * B ^ (2 ^ n - 1) := by
  rw [movingRealSmoothWeight, norm_mul]
  exact mul_le_mul (movingRealFourierWeight_norm value T ψ X lo hi hlo hhi L R)
    (movingRealNodeCutoff_norm value φ G B hB hφ T L R) (norm_nonneg _)
    (pow_nonneg ((norm_nonneg (ψ 0)).trans (ψ.norm_le_seminorm ℝ 0)) _)

noncomputable def movingRealKernel {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) : ℂ :=
  movingRealGateWeight value T nodes X lo hi (topGiantReal L R) *
    movingRealSmoothWeight value T ψ X lo hi hlo hhi φ G L R

theorem measurable_movingRealKernel {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (hout : ∀ x, 1 ≤ |x| → φ x = 0) :
    Measurable (fun x : ℝ × ℝ => movingRealKernel value T nodes ψ X lo hi hlo hhi φ G x.1 x.2) :=
  (measurable_movingRealGateWeight value T nodes X lo hi).mul
    (continuous_movingRealSmoothWeight value T ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
      Prod.fst Prod.snd continuous_fst continuous_snd).measurable

theorem movingRealKernel_norm {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hφ : ∀ x, |φ x| ≤ B) (L R : ℝ) :
    ‖movingRealKernel value T nodes ψ X lo hi hlo hhi φ G L R‖ ≤
      (SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) * B ^ (2 ^ n - 1) := by
  rw [movingRealKernel, norm_mul]
  exact (mul_le_mul_of_nonneg_right (movingRealGateWeight_norm value T nodes X lo hi _)
    (norm_nonneg _)).trans (by simpa only [one_mul] using
      movingRealSmoothWeight_norm value T ψ X lo hi hlo hhi φ G B hB hφ L R)

theorem integrable_movingRealKernel {σ A : Type*} [MeasurableSpace A]
    (value : σ → ℕ) {n : ℕ} (T : MovingSlotData σ n) (nodes : List MovingFormulaNode)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (μ : Measure A) [IsFiniteMeasure μ]
    (L R : A → ℝ) (hL : Measurable L) (hR : Measurable R) :
    Integrable (fun x => movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (L x) (R x)) μ := by
  refine ⟨((measurable_movingRealKernel value T nodes ψ X lo hi hlo hhi φ G B D hB hD
    hφ hlip hout).comp (hL.prodMk hR)).aestronglyMeasurable, ?_⟩
  exact HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall fun x =>
    movingRealKernel_norm value T nodes ψ X lo hi hlo hhi φ G B hB hφ (L x) (R x))

/-- The literal recursive coefficient, including all zero terms, is the
fixed residue coefficient times the single bounded real kernel. -/
theorem moving_recursive_real_kernel {σ I : Type*} (q : I → ℕ)
    [∀ i, Fact (q i).Prime] (value : σ → ℕ) (hvalue : ∀ i, value i ≠ 0)
    (childBound pivotBound : ℕ → ℕ)
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    (g : ∀ i, ZMod (q i) → ℂ) (hg : ∀ i, g i 0 = 0) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset I)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {n : ℕ} (T : MovingSlotData σ n) (t : FrequencyTree ℤ n) (hT : T.Follows t)
    (hf : T.Frequencies (· ≠ 0)) (XL XR a b M : ℕ)
    (hM : movingTopPeriod value hvalue childBound pivotBound T hf ∣ M)
    (hMq : ∀ i ∈ S, (q i : ℤ) * movingSpectatorDenominator value T ∣ (M : ℤ))
    (hL : (XL : ℤ) ≡ (a : ℤ) [ZMOD M]) (hR : (XR : ℤ) ≡ (b : ℤ) [ZMOD M]) :
    let nodes := T.formulaNodes value hvalue childBound pivotBound hf (.prime false) (.prime true)
    recursiveTransferWeight (movingSlotSystem value childBound pivotBound)
        (fun x s => (movingWindowLeaf value X lo hi (movingDataLeaf F) x s *
          movingFourierLeaf value ψ X x s) *
            ∏ i ∈ S, spectatorHistoryLeaf (movingSlotModulus value) (g i) (Dq i) x s)
        (movingSlotCutoff value childBound pivotBound
          (movingPhiExtra value childBound pivotBound (movingDataExtra E) φ G)) n ⟨n, T, XL, XR⟩ t =
      movingResidueCoefficient q value F E g Dq S T nodes a b *
        movingRealKernel value T nodes ψ X lo hi hlo hhi φ G XL XR := by
  dsimp only
  rw [moving_complete_coefficient_factor q value hvalue childBound pivotBound F E g hg Dq S
    ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout T t hT hf XL XR,
    moving_original_canonical_coefficient q value hvalue childBound pivotBound F E X lo hi
      g Dq S T hf XL XR a b M hM hMq hL hR,
    movingSmoothPolynomialFactors_real value T Polynomial.X (Polynomial.C XR) ψ X lo hi hlo hhi
      φ G B D hB hD hφ hlip hout]
  simp only [Polynomial.eval_X, Polynomial.eval_C, movingRealKernel, mul_assoc]

end Ostmann

end OAI
