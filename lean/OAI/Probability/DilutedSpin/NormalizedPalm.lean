import OAI.Probability.DilutedSpin.DictionaryPalm
import OAI.Probability.DilutedSpin.ExternalCovariance

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω J Z X Y : Type} [Fintype Ω]
    [Countable J] [MeasurableSpace J] [MeasurableSingletonClass J] [DecidableEq J]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}
    {A : J × Z → Type} [∀ i, Fintype (A i)]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure J) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (r s : ℝ≥0) (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : J × Z) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (fixed D E : (i : J × Z) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (j : J) (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)

 
theorem normalized_dictionary_palm
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (ht : |t| ≤ 1/4) (hu : |u| ≤ 1/4)
    (hA : ∀ i x y, 1/2 ≤ selectedFactor (fun i => decide (i.1 = j)) fixed D E t u i x y)
    (hc : 0 < ν.real {j}) (hs : 0 < s) :
    |externalCovariance ξ μ (ν.prod τ) (τ.map (fun q => (j,q))) r s S a T Q m base
      (selectedFactor (fun i => decide (i.1 = j)) fixed D E t u) D E f t u| ≤
      B * fullSelectedError ξ μ (ν.prod τ) r s T Q (fun l => m l.succ) base
        (fun i => decide (i.1 = j)) fixed D E t u / (ν.real {j}*(s:ℝ)) := by
  have haff (i x y) : 1/2 ≤ 1+t*D i x y+u*E i x y := by
    have hd := mul_le_mul ht (hD i x y) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/4)
    have he := mul_le_mul hu (hE i x y) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/4)
    rw [← abs_mul] at hd he
    linarith [(abs_le.mp hd).1,(abs_le.mp he).1]
  have hh := fullRoot_palm_error ξ μ (ν.prod τ) r s S a T Q (fun l => m l.succ) base
    (fun i => decide (i.1 = j)) fixed D E t u f hb hB hf hD hE ht hu hA hs
  rw [fullInserted_select_type ξ μ ν τ r s S a T Q m base fixed D E j t u f hb hB hf hE haff,
    fullInserted_select_type ξ μ ν τ r s S a T Q m base fixed D E j t u (fun _ => 1) hb
      (by norm_num : (0:ℝ) ≤ 1) (by intro _; norm_num) hE haff] at hh
  change |ν.real {j} * _ - oldTreeAverage ξ μ (ν.prod τ) r s S T Q (fun l => m l.succ) base
    (selectedFactor (fun i => decide (i.1 = j)) fixed D E t u) f * (ν.real {j} * _)| ≤ _ at hh
  rw [mul_left_comm _ (ν.real {j}), ← mul_sub,abs_mul,abs_of_pos hc] at hh
  unfold externalCovariance
  have hh' := (le_div_iff₀ hc).mpr (by simpa only [mul_comm (ν.real {j})] using hh)
  simpa only [div_div, mul_comm (s:ℝ)] using hh'

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
