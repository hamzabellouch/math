import OAI.Probability.DilutedSpin.NormalizedPalm
import OAI.Probability.DilutedSpin.SingletonRoot

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
variable {Ω J Z X Y : Type} [Fintype Ω]
    [Countable J] [MeasurableSpace J] [MeasurableSingletonClass J] [DecidableEq J]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}
    {A : J × Z → Type} [∀ i, Fintype (A i)]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure J) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (r s : ℝ≥0) (S : PrescribedTree L) (anchor : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : J × Z) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (a b t : J → ℝ) (D E : (i : J × Z) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (j : J) (u : J → ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)

/-- Actual parameter-score Palm inequality: all old factors are the literal
full dictionary factors at u, including the selected type. -/
theorem parameter_dictionary_palm
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hab : ∀ j, a j ≤ b j) (hI : ∀ j, Icc (a j) (b j) ⊆ Icc (-(1:ℝ)/4) (1/4))
    (ht : ∀ j, |t j| ≤ 1/4)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    (hc : 0 < ν.real {j}) (hs : 0 < s) :
    |externalCovariance ξ μ (ν.prod τ) (τ.map (fun q => (j,q))) r s S anchor T Q m base
      (parameterFactor Prod.fst a b t D E u) D E f (t j) (boundParameter (a j) (b j) (u j))| ≤
      B * (parameterError ξ μ (ν.prod τ) r s T Q (fun l => m l.succ) base
        Prod.fst a b t D E j u / (ν.real {j}*(s:ℝ))) := by
  have hu (j : J) : |boundParameter (a j) (b j) (u j)| ≤ 1/4 :=
    abs_le.mpr ⟨by linarith [(hI j (boundParameter_mem (hab j) (u j))).1],
      (hI j (boundParameter_mem (hab j) (u j))).2⟩
  have hA (i : J × Z) (x y) : 1/2 ≤ parameterFactor Prod.fst a b t D E u i x y :=
    affine_two_lower (hD i x y) (hE i x y) (ht i.1) (hu i.1)
  have he := selectedParameterFactor_eq Prod.fst a b t D E j u
  have hh := normalized_dictionary_palm ξ μ ν τ r s S anchor T Q m base
    (parameterFactor Prod.fst a b t D E u) D E j (t j) (boundParameter (a j) (b j) (u j)) f
    hb hB hf hD hE (ht j) (hu j) (by rw [he]; exact hA) hc hs
  rw [he] at hh
  simpa only [parameterError,mul_div_assoc] using hh

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
