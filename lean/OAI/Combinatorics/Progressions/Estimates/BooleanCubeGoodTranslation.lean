import OAI.Combinatorics.Progressions.Dynamics.JointBooleanWeightBudget
import OAI.Combinatorics.Progressions.Sampling.BooleanSamplerDivergence

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

theorem booleanCubeGoodWeight_divergence_bound {B O J α : Type*}
    [Fintype B] [Fintype O] [Fintype J] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : J → B → ℝ) (sets : O → Finset α) (block : J → O → B)
    (hblock : ∀ j, Function.Injective (block j)) {h : ℕ}
    (v : Fin h) (sel : J → O → Option α) (hcard : ∀ o, (sets o).card ≤ h)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ j o, |c j (block j o)| ≤ C)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (A T : ℝ≥0)
    (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (r : B × Fin h → ℝ) (hr : ∀ i, 0 < r i) (κ : J → ℝ) (hκ : ∀ i, 0 < κ i)
    (j : J) (o : O) :
    let n := Fintype.card (BlockParameter B (Fin h) α)
    let G := productMinorDeterminantDerivativeBound n (Fintype.card O) (Fintype.card α) h C 1
    let S := (∑ i, ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) * ((Fintype.card α : ℝ) + 1) ^ 2 * T / r i) +
      (n : ℝ) * ∑ i, ((A : ℝ) / κ i) * G
    let K := productMinorInverseBound (Fintype.card O) (Fintype.card α) h C 1 (κ j)
    let H := productMinorDerivativeBound n (Fintype.card O) (Fintype.card α) h C 1
    (∫ a, |coordinateDivergence
      (fun z a => booleanCubeGoodWeight c sets block v sel ψ r κ a *
        selectedInverseField (booleanSamplerMap (c j) sets)
          (booleanSelectedInjection (block j) v (sel j)) o z a) a|) ≤
      K * S + (n : ℝ) * (K ^ 2 * H) := by
  let w := booleanCubeGoodWeight c sets block v sel ψ r κ
  have hs := booleanCubeGoodWeight_spec c sets block v sel ψ hψ hrange hzero r hr κ hκ
  have hbase := boolean_sampler_divergence_bound (c j) sets (block j) (hblock j) v (sel j)
    hcard hC (show (1 : ℝ) ≤ 1 from le_rfl) (hc j) (hκ j) w hs.1 hs.2.1
    (fun a ha => (hs.2.2.2.2 a ha).1)
    (fun a ha => (hs.2.2.2.2 a ha).2 j) o
  have hS := booleanCubeGoodWeight_derivative_budget c sets block v sel hcard hC hc
    ψ hψ hrange A T hLip hTransition r hr κ hκ
  have hK := productMinorInverseBound_nonneg (Fintype.card O) (Fintype.card α) h
    hC zero_le_one (hκ j).le
  have hH := productMinorDerivativeBound_nonneg (Fintype.card (BlockParameter B (Fin h) α))
    (Fintype.card O) (Fintype.card α) h hC zero_le_one
  apply hbase.trans
  exact add_le_add (mul_le_mul_of_nonneg_left hS hK)
    (mul_le_of_le_one_right (by positivity) hs.2.2.2.1)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

theorem booleanCubeGoodWeight_translation_bound {B O J α : Type*}
    [Fintype B] [Fintype O] [Fintype J] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : J → B → ℝ) (sets : O → Finset α) (block : J → O → B)
    (hblock : ∀ j, Function.Injective (block j)) {h : ℕ}
    (v : Fin h) (sel : J → O → Option α) (hcard : ∀ o, (sets o).card ≤ h)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ j o, |c j (block j o)| ≤ C)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (A T : ℝ≥0)
    (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (r : B × Fin h → ℝ) (hr : ∀ i, 0 < r i) (κ : J → ℝ) (hκ : ∀ i, 0 < κ i) (j : J) :
    let n := Fintype.card (BlockParameter B (Fin h) α)
    let G := productMinorDeterminantDerivativeBound n (Fintype.card O) (Fintype.card α) h C 1
    let S := (∑ i, ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) * ((Fintype.card α : ℝ) + 1) ^ 2 * T / r i) +
      (n : ℝ) * ∑ i, ((A : ℝ) / κ i) * G
    let K := productMinorInverseBound (Fintype.card O) (Fintype.card α) h C 1 (κ j)
    let H := productMinorDerivativeBound n (Fintype.card O) (Fintype.card α) h C 1
    ∃ L : ℝ≥0, (L : ℝ) = (Fintype.card O : ℝ) * (K * S + (n : ℝ) * (K ^ 2 * H)) ∧
      ImageTranslationBound (realDensityMeasure volume (booleanCubeGoodWeight c sets block v sel ψ r κ))
        (booleanSamplerMap (c j) sets) L := by
  let n := Fintype.card (BlockParameter B (Fin h) α)
  let G := productMinorDeterminantDerivativeBound n (Fintype.card O) (Fintype.card α) h C 1
  let S := (∑ i, ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) * ((Fintype.card α : ℝ) + 1) ^ 2 * T / r i) +
    (n : ℝ) * ∑ i, ((A : ℝ) / κ i) * G
  let K := productMinorInverseBound (Fintype.card O) (Fintype.card α) h C 1 (κ j)
  let H := productMinorDerivativeBound n (Fintype.card O) (Fintype.card α) h C 1
  have hG : 0 ≤ G := productMinorDeterminantDerivativeBound_nonneg _ _ _ _ hC zero_le_one
  have hS : 0 ≤ S := by
    dsimp only [S]
    exact add_nonneg (Finset.sum_nonneg (fun i _ => div_nonneg (by positivity) (hr i).le))
      (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun i _ =>
        mul_nonneg (div_nonneg A.coe_nonneg (hκ i).le) hG)))
  have hK : 0 ≤ K := productMinorInverseBound_nonneg _ _ _ hC zero_le_one (hκ j).le
  have hH : 0 ≤ H := productMinorDerivativeBound_nonneg _ _ _ _ hC zero_le_one
  let Q : ℝ≥0 := ⟨K * S + (n : ℝ) * (K ^ 2 * H), by positivity⟩
  refine ⟨∑ _ : O, Q, ?_, ?_⟩
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast]
    rfl
  · have hs := booleanCubeGoodWeight_spec c sets block v sel ψ hψ hrange hzero r hr κ hκ
    apply imageTranslationBound_of_selected_inverse (booleanSamplerMap (c j) sets)
      ((booleanSamplerMap_contDiff (c j) sets).of_le (by norm_num))
      (booleanSelectedInjection (block j) v (sel j)) _ hs.1 hs.2.1 hs.2.2.1
      (fun a ha => (boolean_selected_inverse_bound (c j) sets (block j) v (sel j) hcard a
        hC zero_le_one (hc j) (hs.2.2.2.2 a ha).1 (hκ j) ((hs.2.2.2.2 a ha).2 j)).1)
      (fun _ => Q)
    intro o
    exact booleanCubeGoodWeight_divergence_bound c sets block hblock v sel hcard hC hc
      ψ hψ hrange hzero A T hLip hTransition r hr κ hκ j o

end Erdos3

end

end OAI
