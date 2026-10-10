import Mathlib.Topology.ContinuousMap.Bounded.Normed
import OAI.NumberTheory.Ostmann.Arithmetic.BulkSmoothFactors

namespace OAI

/-! # The smooth tree as a continuous function of the bulk logarithms -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap ComplexConjugate BoundedContinuousFunction

noncomputable def bulkLogValues {σ : Type*} (base : σ → ℝ) (S : Finset σ)
    (x : σ → ℝ) (i : σ) : ℝ := if i ∈ S then Real.exp (x i) else base i

theorem bulkLogValues_update {σ : Type*} (base : σ → ℝ) (S : Finset σ)
    (x : σ → ℝ) (i : σ) (hi : i ∈ S) (t : ℝ) :
    bulkLogValues base S (Function.update x i t) =
      Function.update (bulkLogValues base S x) i (Real.exp t) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [bulkLogValues, hi, ite_true, Function.update_self]
  · simp only [bulkLogValues, Function.update_of_ne hj]

theorem bulkLogValues_nat {σ : Type*} (base sample : σ → ℕ) (S : Finset σ)
    (hp : ∀ i ∈ S, 0 < sample i) :
    bulkLogValues (fun i => (base i : ℝ)) S (fun i => Real.log (sample i)) =
      (fun i => ((if i ∈ S then sample i else base i : ℕ) : ℝ)) := by
  funext i
  by_cases hi : i ∈ S
  · simp only [bulkLogValues, hi, ite_true]
    exact Real.exp_log (by exact_mod_cast hp i hi)
  · simp only [bulkLogValues, hi, ite_false]

/-- At every original prime tuple this real extension is exactly the original
moving-tree weight, including points where one of the node cutoffs vanishes. -/
theorem realValueSmoothWeight_bulkLog_nat {σ : Type*}
    (base sample : σ → ℕ) (S : Finset σ) (hp : ∀ i ∈ S, 0 < sample i)
    {n : ℕ} (T : MovingSlotData σ n) (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ) (L R : ℝ) :
    realValueSmoothWeight (bulkLogValues (fun i => (base i : ℝ)) S
      (fun i => Real.log (sample i))) T ψ X lo hi hlo hhi φ G L R =
        movingRealSmoothWeight (fun i => if i ∈ S then sample i else base i)
          T ψ X lo hi hlo hhi φ G L R := by
  rw [bulkLogValues_nat base sample S hp, realValueSmoothWeight_nat]

theorem continuous_bulkLogValues {σ : Type*} (base : σ → ℝ) (S : Finset σ) (i : σ) :
    Continuous (fun x => bulkLogValues base S x i) := by
  unfold bulkLogValues
  split_ifs
  · exact Real.continuous_exp.comp (continuous_apply i)
  · exact continuous_const

theorem continuous_realSlotProduct {σ A : Type*} [TopologicalSpace A]
    (value : A → σ → ℝ) (hv : ∀ i, Continuous (fun x => value x i)) (l : List σ) :
    Continuous (fun x => realSlotProduct (value x) l) := by
  induction l with
  | nil => exact continuous_const
  | cons i l ih => exact (hv i).mul ih

theorem realSlotProduct_bulkLogValues {σ : Type*} (base : σ → ℝ) (S : Finset σ)
    (l : List σ) (hl : ∀ i ∈ l, i ∉ S) (x : σ → ℝ) :
    realSlotProduct (bulkLogValues base S x) l = realSlotProduct base l := by
  unfold realSlotProduct
  congr 1
  apply List.map_congr_left
  intro i hi
  exact ite_eq_right (hl i hi)

theorem MovingSlotReversal.continuous_bulkLogPivot {σ : Type*}
    (base : σ → ℝ) (S : Finset σ) (s : MovingSlotReversal σ)
    (hs : ∀ i ∈ S, i ∉ s.compensationSlots)
    (L R : (σ → ℝ) → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => s.realValuePivot (bulkLogValues base S x) (L x) (R x)) := by
  have hc (x : σ → ℝ) : realSlotProduct (bulkLogValues base S x) s.compensationSlots =
      realSlotProduct base s.compensationSlots :=
    realSlotProduct_bulkLogValues base S _ (fun i hi hS => hs i hS hi) x
  simp_rw [realValuePivot, hc]
  exact (((continuous_const.mul
    (continuous_realSlotProduct _ (continuous_bulkLogValues base S) s.rightSlots)).mul hR).sub
    ((continuous_const.mul
    (continuous_realSlotProduct _ (continuous_bulkLogValues base S) s.leftSlots)).mul hL)).div_const _

theorem MovingSlotData.continuous_bulkLogLeafModuli {σ : Type*}
    (base : σ → ℝ) (S : Finset σ) {n : ℕ} (T : MovingSlotData σ n)
    (hT : ∀ i ∈ S, T.CompensationAbsent i)
    (L R : (σ → ℝ) → ℝ) (hL : Continuous L) (hR : Continuous R) (j : TreeLeafIndex n) :
    Continuous (fun x => T.realValueLeafModuli (bulkLogValues base S x) (L x) (R x) j) := by
  induction T generalizing L R with
  | leaf s regular =>
    exact (hL.mul hR).mul (continuous_realSlotProduct _ (continuous_bulkLogValues base S) regular)
  | node s CL CR u left right ihL ihR =>
    have hp := (MovingSlotData.step s CL CR u left right false).continuous_bulkLogPivot
      base S (fun i hi => (hT i hi).1) L R hL hR
    cases j with
    | inl j => exact ihL (fun i hi => (hT i hi).2.1) _ L hp hL j
    | inr j => exact ihR (fun i hi => (hT i hi).2.2) _ R hp hR j

theorem continuous_bulkLogFourierWeight {σ : Type*} (base : σ → ℝ) (S : Finset σ)
    {n : ℕ} (T : MovingSlotData σ n) (hT : ∀ i ∈ S, T.CompensationAbsent i)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (L R : (σ → ℝ) → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => realValueFourierWeight (bulkLogValues base S x) T ψ X lo hi hlo hhi
      (L x) (R x)) := by
  apply continuous_finsetProd
  intro j _
  have hc := (fourierPolynomialFactor Polynomial.X ψ (T.leafFrequencies j) lo hi hlo hhi).continuous_value.comp
    ((T.continuous_bulkLogLeafModuli base S hT L R hL hR j).div_const X)
  dsimp only
  split_ifs
  · exact Complex.continuous_conj.comp hc
  · exact hc

theorem continuous_bulkLogNodeCutoff {σ : Type*} (base : σ → ℝ) (S : Finset σ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    {n : ℕ} (T : MovingSlotData σ n) (hT : ∀ i ∈ S, T.CompensationAbsent i)
    (L R : (σ → ℝ) → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => realValueNodeCutoff (bulkLogValues base S x) φ G T (L x) (R x)) := by
  have hp (g : ℝ) : Continuous (fun x => (positiveLogCutoff φ g x : ℂ)) := by
    have he (x : ℝ) := logCutoffPolynomialFactor_value Polynomial.X φ g B D hB hD hφ hlip hout x
    simp only [Polynomial.eval_X] at he
    exact ((logCutoffPolynomialFactor Polynomial.X φ g B D hB hD hφ hlip).continuous_value).congr he
  induction T generalizing L R with
  | leaf => exact continuous_const
  | @node n s CL CR u left right ihL ihR =>
    have hc := (MovingSlotData.step s CL CR u left right false).continuous_bulkLogPivot
      base S (fun i hi => (hT i hi).1) L R hL hR
    exact (((hp (G (n + 1))).comp hc).mul
      (ihL (fun i hi => (hT i hi).2.1) _ L hc hL)).mul
      (ihR (fun i hi => (hT i hi).2.2) _ R hc hR)

theorem continuous_bulkLogSmoothWeight {σ : Type*} (base : σ → ℝ) (S : Finset σ)
    {n : ℕ} (T : MovingSlotData σ n) (hT : ∀ i ∈ S, T.CompensationAbsent i)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (L R : (σ → ℝ) → ℝ) (hL : Continuous L) (hR : Continuous R) :
    Continuous (fun x => realValueSmoothWeight (bulkLogValues base S x) T ψ X lo hi hlo hhi
      φ G (L x) (R x)) :=
  (continuous_bulkLogFourierWeight base S T hT ψ X lo hi hlo hhi L R hL hR).mul
    (continuous_bulkLogNodeCutoff base S φ G B D hB hD hφ hlip hout T hT L R hL hR)

/-- The bound is uniform in all real bulk variables and both giant arguments. -/
theorem realValueSmoothWeight_norm {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (hT : T.CompensationAbsent i)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hV : T.Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L R : ℝ) :
    ‖realValueSmoothWeight value T ψ X lo hi hlo hhi φ G L R‖ ≤
      movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1) := by
  have he := bulkSmoothFactors_value value i T hT (Polynomial.C L) (Polynomial.C R)
    ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout (value i)
  simp only [Function.update_eq_self, Polynomial.eval_C] at he
  rw [← he]
  exact (smoothPolynomialWeight_norm _ _).trans
    (bulkSmoothFactors_budget value i T _ _ ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip)

noncomputable def bulkLogSmoothFunction {σ : Type*} (base : σ → ℝ) (S : Finset σ)
    {n : ℕ} (T : MovingSlotData σ n) (hT : ∀ i ∈ S, T.CompensationAbsent i)
    (i : σ) (hiS : i ∈ S) (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ)
    (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (hV : T.Frequencies (fun s => |(s : ℝ)| ≤ V))
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L R : ℝ) : (σ → ℝ) →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup _
    (continuous_bulkLogSmoothWeight base S T hT ψ X lo hi hlo hhi φ G B D hB hD hφ hlip hout
      (fun _ => L) (fun _ => R) continuous_const continuous_const)
    (movingFourierVariationBudget ψ V lo hi n * (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1))
    (fun x => realValueSmoothWeight_norm (bulkLogValues base S x) i T (hT i hiS)
      ψ X lo hi V hlo hhi hV φ G B D hB hD hφ hlip hout L R)

end Ostmann

end OAI
