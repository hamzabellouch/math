import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationTerminalDataBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateSupportRemoval TemplateOneSidedBudget Arithmetic
open TemplateOneSidedRelabel ParityActions HistoryFrequencyLabels HistoryFrequencyBudget
attribute [local instance] Classical.propDecidable

theorem terminalCorePairAmplitude_eq_data {a bulk H : ℝ}
    (ha : 0 ≤ a) (hbulk : 1 ≤ bulk)
    (k n : ℕ) (width : Role → ℕ) (m : ℕ) (hm : m ≤ width .word)
    (B : ℕ → ℤ) (T : ℕ → ℝ) (J s v : ℤ)
    (σ π : Reassignments k n m) (t u : HistoryReconstruction.Tree (n+1))
    (ht : RangeSupported (ranges a bulk (n+1)) (n+1) [] s t)
    (hu : RangeSupported (ranges a bulk (n+1)) (n+1) [] v u)
    (i : (schedule k (n+1)).Constituent width) (x : Other i → ℤ)
    (gate : Bool) (r q : ℕ)
    {X Δ Wp Wl : ℝ} (hX : 1 ≤ X) (hH : Real.log 2 ≤ H)
    (hfreq : linearEnvelope a (n+1)*bulk ≤ H)
    (N : ℕ) (hw : ∀z,width z ≤ N)
    (hvars : ∀z,|((insertCoordinate i x
      ((historyPairResidueModulus k (n+1) s (paritySampledExpressions k n width m hm σ) t
        v (paritySampledExpressions k n width m hm π) u*q+r:ℕ):ℤ) z : ℤ):ℝ)| ≤ Real.exp H) :
    let e := paritySampledExpressions k n width m hm σ
    let f := paritySampledExpressions k n width m hm π
    let Q := historyPairResidueModulus k (n+1) s e t v f u
    let D := obstructionSizeFactor k (n+1)*(2*(N+1)+1)
    (canonicalSourcePairData k B (fun l=>(bound a bulk l:ℤ)) T J (n+1) true false s v
      e f t u i x (r:ℤ) gate X Δ Wp Wl H D).weight
      (𝓕 SchwartzCutoff.psi) ((Q*q+r:ℕ):ℝ) =
      terminalCorePairAmplitude k n width m hm B (fun l=>(bound a bulk l:ℤ)) T J s v
        σ π t u gate X Δ Wp Wl (insertCoordinate i x ((Q*q+r:ℕ):ℤ)) := by
  dsimp only
  have hH0 : 0 ≤ H := (Real.log_nonneg (by norm_num : (1:ℝ)≤2)).trans hH
  have he := terminal_initial_expression_parameters k n width m hm σ N hw hH0
  have hf := terminal_initial_expression_parameters k n width m hm π N hw hH0
  have hh := canonicalSourcePairData_weight_actual ha hbulk k (n+1) B T J true false s v
    (paritySampledExpressions k n width m hm σ) (paritySampledExpressions k n width m hm π)
    t u ht hu i x gate r q he.1 hf.1 (Δ:=Δ) (Wp:=Wp) (Wl:=Wl) hX hH hfreq
    (2*(N+1)) he.2.1 hf.2.1 he.2.2 hf.2.2 hvars
  dsimp only at hh
  rw [paritySampledExpressions_integer_eval k n width m hm σ,
    paritySampledExpressions_integer_eval k n width m hm π] at hh
  simpa only [terminalCorePairAmplitude,conjugateBy,Bool.false_eq_true,ite_false,ite_true] using hh

theorem terminalPairData_ranges_degree (k n : ℕ) (width : Role → ℕ) (m : ℕ)
    (hm : m ≤ width .word) (B V : ℕ → ℤ) (T : ℕ → ℝ) (J s v : ℤ)
    (σ π : Reassignments k n m) (t u : HistoryReconstruction.Tree (n+1))
    (i : (schedule k (n+1)).Constituent width) (x : Other i → ℤ) (r : ℤ) (gate : Bool)
    {X Δ Wp Wl H : ℝ} (hX : 0 < X) (N : ℕ) (hw : ∀z,width z ≤ N) (ρ : 𝓢(ℝ,ℂ)) :
    let D := obstructionSizeFactor k (n+1)*(2*(N+1)+1)
    let data := canonicalSourcePairData k B V T J (n+1) true false s v
      (paritySampledExpressions k n width m hm σ) (paritySampledExpressions k n width m hm π)
      t u i x r gate X Δ Wp Wl H D
    data.Ranges ρ (fun _=>coarseLower D H Δ Wl) (fun _=>-Δ+Wl)
      (Real.exp ((-Δ+Wl)/2)*leafProfileBound ρ) ∧
    data.degreeCost ≤ 2*sourceDegreeFactor k (n+1)*(2*(N+1)+1)+1 := by
  dsimp only
  have he := terminal_initial_expression_parameters k n width m hm σ N hw (le_refl (0:ℝ))
  have hf := terminal_initial_expression_parameters k n width m hm π N hw (le_refl (0:ℝ))
  constructor
  · exact canonicalSourcePairData_ranges k B V T J (n+1) true false s v _ _ t u i x r gate
      hX _ he.1 hf.1 ρ
  · exact canonicalSourcePairData_degreeCost k B V T J (n+1) true false s v _ _ t u i x r gate
      X Δ Wp Wl H _ (2*(N+1)) he.2.1 hf.2.1

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
