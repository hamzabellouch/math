import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictionShrink
import OAI.Analysis.LipschitzHilbert.Trees.HierarchyNormalization

namespace OAI

/-! The balanced branch of §9 for actual mass-normalized child amplitudes.
The one-sided denominator comparison is derived from scaled amplitude
motion, and the numerator uses the original child-mass error budget. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics

theorem source_normalized_numerator_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n c : ℝ} (hn : 0 < n) (hc : 0 < c) (μ : ℝ) (lam : ℂ) (A : E) :
    (((c/n)^(1-μ):ℝ):ℂ) • (lam • (c^(μ-1) • A)) =
      ((n^(μ-1):ℝ):ℂ) • (lam • A) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ),smul_smul,smul_smul,smul_smul]
  congr 1
  have hscalar := congrArg (fun r : ℝ => (r : ℂ))
    (child_normalization_coefficient (μ := μ) hn hc)
  push_cast at hscalar
  calc
    _ = (↑((c/n)^(1-μ)) * ↑(c^(μ-1))) * lam := mul_right_comm _ _ _
    _ = _ := by rw [hscalar]

variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem source_normalized_modulated_numerator_eq
    {n c : ℝ} (hn : 0 < n) (hc : 0 < c) (μ : ℝ) (lam : ℂ)
    (frequency : κ → ℝ) (b : ℝ) (A : EuclideanSpace ℂ κ) :
    (((c/n)^(1-μ):ℝ):ℂ) •
      (lam • diagonalModulation frequency (c^(μ-1) • A) b) =
      ((n^(μ-1):ℝ):ℂ) • (lam • diagonalModulation frequency A b) := by
  have hcomm : diagonalModulation frequency (c^(μ-1) • A) b =
      c^(μ-1) • diagonalModulation frequency A b :=
    (diagonalModulationRealIsometry frequency b).map_smul _ _
  rw [hcomm,source_normalized_numerator_eq hn hc]

/-- Each child's actual radial shrink gives the summed denominator
ordering, without an additional denominator hypothesis. -/
theorem source_prediction_denominator_sum_shrink
    {n n' p μ ε : ℝ} (hn : 0 < n) (hn' : 0 < n')
    (c c' : ι → ℝ) (hc : ∀ i, 0 < c i) (hc' : ∀ i, 0 < c' i)
    (hp : 0 < p) (hε : 0 ≤ ε)
    (frequency : ι → κ → ℝ) (b : ℝ)
    (A A' : ι → EuclideanSpace ℂ κ)
    (hscaled : ∀ i,
      ‖massPowerScale n' (c' i) (-(1/p)) (μ-1+1/p) • A' i-
        diagonalModulation (frequency i)
          (massPowerScale n (c i) (-(1/p)) (μ-1+1/p) • A i) b‖ ≤
        ε*(c i/n)^(1/p)*(c i)^μ) :
    1+∑ i, (c i/n)*‖(c i)^(μ-1) • radialShrink (2*ε*c i) (A i)‖^p ≤
      1+∑ i, (c' i/n')*‖(c' i)^(μ-1) • A' i‖^p := by
  apply add_le_add_right
  exact Finset.sum_le_sum fun i _ =>
    source_prediction_denominator_shrink hn hn' (hc i) (hc' i) hp hε
      (diagonalModulationRealIsometry (frequency i) b) (A i) (A' i) (hscaled i)

/-- In the balanced branch the normalized moving prediction is controlled
by the actual shrunken snapshot, with an error proportional to `u`. -/
theorem source_balanced_prediction_comparison
    {n n' p μ ε K u : ℝ} (hn : 0 < n) (hn' : 0 < n')
    (c c' : ι → ℝ) (hc : ∀ i, 0 < c i) (hc' : ∀ i, 0 < c' i)
    (hp : 1 ≤ p) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hpower : n^μ ≤ K)
    (hu : 1/2 ≤ u) (hsum : ∑ i, c i/n ≤ 1)
    (frequency : ι → κ → ℝ) (b : ℝ)
    (A A' : ι → EuclideanSpace ℂ κ) (lam lam' : ι → ℂ)
    (hlam : ∀ i, ‖lam i‖ ≤ 1)
    (hscaled : ∀ i,
      ‖massPowerScale n' (c' i) (-(1/p)) (μ-1+1/p) • A' i-
        diagonalModulation (frequency i)
          (massPowerScale n (c i) (-(1/p)) (μ-1+1/p) • A i) b‖ ≤
        ε*(c i/n)^(1/p)*(c i)^μ)
    (hnumerator : ∀ i,
      ‖((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i)-
        ((n^(μ-1):ℝ):ℂ) • (lam i • diagonalModulation (frequency i) (A i) b)‖ ≤
        ε*K*(c i/n)) :
    let X := fun i => (c i)^(μ-1) • radialShrink (2*ε*c i) (A i)
    let X' := fun i => (c' i)^(μ-1) • A' i
    let actual := energyRatio p (1+∑ i, (c' i/n')*‖X' i‖^p)
      (∑ i, ((((c' i/n')^(1-μ):ℝ):ℂ) • (lam' i • X' i)))
    let model := energyRatio p (1+∑ i, (c i/n)*‖X i‖^p)
      (∑ i, ((((c i/n)^(1-μ):ℝ):ℂ) •
        (lam i • diagonalModulation (frequency i) (X i) b)))
    Real.log actual-Real.log model ≤ 6*p*ε*K*u ∧
      actual ≤ Real.exp (6*p*ε*K*u)*model := by
  dsimp only
  let actualTerm := fun i => ((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i)
  let modelTerm := fun i => ((n^(μ-1):ℝ):ℂ) •
    (lam i • diagonalModulation (frequency i) (radialShrink (2*ε*c i) (A i)) b)
  have hden := source_prediction_denominator_sum_shrink hn hn' c c' hc hc'
    (by linarith : 0 < p) hε frequency b A A' hscaled
  have hdModel : 0 < 1+∑ i, (c i/n)*
      ‖(c i)^(μ-1) • radialShrink (2*ε*c i) (A i)‖^p := by
    have hs : 0 ≤ ∑ i, (c i/n)*
        ‖(c i)^(μ-1) • radialShrink (2*ε*c i) (A i)‖^p :=
      Finset.sum_nonneg fun i _ => mul_nonneg (div_pos (hc i) hn).le
        (Real.rpow_nonneg (norm_nonneg _) _)
    linarith
  have hterms (i : ι) : ‖actualTerm i-modelTerm i‖ ≤ (3*ε)*K*(c i/n) := by
    have hb := source_prediction_shrunk_numerator hn (hc i).le hε hpower
      (diagonalModulationIsometry (frequency i) b) (A i) (actualTerm i) (lam i)
      (hlam i) (hnumerator i)
    simpa only [modelTerm,diagonalModulationIsometry_apply,mul_assoc] using hb
  have hlog := balanced_prediction_log_comparison hp hdModel hden
    (show 0 ≤ 3*ε by positivity) hK hu (fun i => c i/n) hsum actualTerm modelTerm hterms
  have hactual (i : ι) :
      ((((c' i/n')^(1-μ):ℝ):ℂ) • (lam' i • ((c' i)^(μ-1) • A' i))) =
      actualTerm i := source_normalized_numerator_eq hn' (hc' i) μ (lam' i) (A' i)
  have hmodel (i : ι) :
      ((((c i/n)^(1-μ):ℝ):ℂ) •
        (lam i • diagonalModulation (frequency i)
          ((c i)^(μ-1) • radialShrink (2*ε*c i) (A i)) b)) = modelTerm i :=
    source_normalized_modulated_numerator_eq hn (hc i) μ (lam i) (frequency i) b _
  simp_rw [hactual,hmodel]
  have hlog' : Real.log (energyRatio p (1+∑ i, (c' i/n')*‖(c' i)^(μ-1) • A' i‖^p)
      (∑ i, actualTerm i))-
      Real.log (energyRatio p (1+∑ i, (c i/n)*
        ‖(c i)^(μ-1) • radialShrink (2*ε*c i) (A i)‖^p) (∑ i, modelTerm i)) ≤
      6*p*ε*K*u := by nlinarith [hlog]
  refine ⟨hlog', ?_⟩
  have hposActual := energyRatio_pos (p := p) (hdModel.trans_le hden) (∑ i, actualTerm i)
  have hposModel := energyRatio_pos (p := p) hdModel (∑ i, modelTerm i)
  have hexp := Real.exp_le_exp.mpr (show
    Real.log (energyRatio p (1+∑ i, (c' i/n')*‖(c' i)^(μ-1) • A' i‖^p)
      (∑ i, actualTerm i)) ≤ 6*p*ε*K*u+
    Real.log (energyRatio p (1+∑ i, (c i/n)*
      ‖(c i)^(μ-1) • radialShrink (2*ε*c i) (A i)‖^p) (∑ i, modelTerm i)) by linarith)
  simpa only [Real.exp_add,Real.exp_log hposActual,Real.exp_log hposModel] using hexp

end LipschitzHilbert

end

end OAI
