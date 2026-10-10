import OAI.Probability.DilutedSpin.CommonFresh
import OAI.Probability.DilutedSpin.CompoundSuperposition
import OAI.Probability.DilutedSpin.ParameterPalm

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
variable {Ω K Z X Y : Type} [Fintype Ω]
    [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K] [DecidableEq K]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}
    {A : K → Type} [∀ i, Fintype (A i)]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure (K×ℕ)) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (r s : ℝ≥0) (S : PrescribedTree L) (anchor : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : K) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (D E : (i : K) → Z → FinitePath Ω L → FinitePath (A i) L → ℝ)

noncomputable def dictionaryFactor (u : K×ℕ → ℝ) :
    (i : (K×ℕ)×Z) → FinitePath Ω L → FinitePath (A i.1.1) L → ℝ :=
  parameterFactor Prod.fst (fun i => probeLow i.2) (fun i => probeHigh i.2)
    (fun i => extractionProbe i.2) (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) u

/-- A single old-reservoir analytic function is small at every prescribed probe.
The trace j occurs only in the independently inserted mark; it is not erased
from or changed inside the old ambient Poisson dictionary. -/
theorem dictionary_covariance_probe_bound
    (u : K×ℕ → ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ) (q : K) (j : ℕ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (hm : ∀ j : Fin L, m j.succ ≠ 0) (hmono : Monotone m) (hpos : ∀ j, 0 ≤ m j)
    (hroot : m 0 = 0) (hend : m (Fin.last L) = 1)
    {B : ℝ} (hB : 0 ≤ B) (hf : ∀ x, |f x| ≤ B)
    (hD : ∀ i v x y, |D i v x y| ≤ 1) (hE : ∀ i v x y, |E i v x y| ≤ 1)
    (hc : 0 < ν.real {(q,j)}) (hs : 0 < s) :
    |externalCovariance ξ μ (ν.prod τ) (τ.map (fun v => ((q,0),v))) r s S anchor T
      (fun i => Q i.1.1) m base (dictionaryFactor D E u)
      (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) f (extractionProbe j) 0| ≤
      4*(4+8*(S.leaves:ℝ))*B*extractionProbe j^(j+4) +
      B*(parameterError ξ μ (ν.prod τ) r s T (fun i => Q i.1.1) (fun l => m l.succ) base
        Prod.fst (fun i => probeLow i.2) (fun i => probeHigh i.2) (fun i => extractionProbe i.2)
        (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) (q,j) u / (ν.real {(q,j)}*(s:ℝ))) := by
  let v := boundParameter (probeLow j) (probeHigh j) (u (q,j))
  have hv := boundParameter_mem (probeLow_lt_high j).le (u (q,j))
  have hv0 : 0 ≤ v := (probeLow_pos j).le.trans hv.1
  have hv1 : v ≤ 1/4 := hv.2.trans (probeHigh_lt_quarter j).le
  have hp := parameter_dictionary_palm ξ μ ν τ r s S anchor T (fun i => Q i.1.1) m base
    (fun i => probeLow i.2) (fun i => probeHigh i.2) (fun i => extractionProbe i.2)
    (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) (q,j) u f hb hB hf
    (fun i => (probeLow_lt_high i.2).le) (fun i => probe_interval_quarter i.2)
    (fun i => extractionProbe_abs_le_quarter i.2) (fun i => hD i.1.1 i.2)
    (fun i => hE i.1.1 i.2) hc hs
  have hl := externalCovariance_sub_le ξ μ (ν.prod τ) (τ.map (fun v => ((q,j),v))) r s S anchor T
    (fun i => Q i.1.1) m base (dictionaryFactor D E u)
    (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) f hb hm hmono hpos hroot hend hB hf
    (fun i => hD i.1.1 i.2) (fun i => hE i.1.1 i.2) (extractionProbe_abs_le_quarter j) hv0 hv1
  have hA (i : K) (v : Z) (x y) : 1/2 ≤ 1+extractionProbe j*D i v x y+0*E i v x y :=
    affine_two_lower (hD i v x y) (hE i v x y) (extractionProbe_abs_le_quarter j) (by norm_num)
  rw [externalCovariance_probe ξ μ (ν.prod τ) τ r s S anchor T Q m base (dictionaryFactor D E u)
    D E f hb hf hE (extractionProbe j) 0
    hA q 0 j]
  have hcoef : 0 ≤ 2*(4+8*(S.leaves:ℝ))*B := by positivity
  have hl' := hl.trans (mul_le_mul_of_nonneg_left hv.2 hcoef)
  dsimp only [dictionaryFactor] at hl'
  -- |H(0)| ≤ |H(v)| + |H(v)-H(0)|, with the two estimates proved above.
  have htri (x y : ℝ) : |y| ≤ |x|+|x-y| := by
    have := abs_sub x (x-y)
    rw [show x-(x-y)=y by ring] at this
    exact this
  have hh := htri
    (externalCovariance ξ μ (ν.prod τ) (τ.map (fun v => ((q,j),v))) r s S anchor T
      (fun i => Q i.1.1) m base (dictionaryFactor D E u)
      (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) f (extractionProbe j) v)
    (externalCovariance ξ μ (ν.prod τ) (τ.map (fun v => ((q,j),v))) r s S anchor T
      (fun i => Q i.1.1) m base (dictionaryFactor D E u)
      (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) f (extractionProbe j) 0)
  dsimp only [dictionaryFactor,v,probeHigh,probeLow] at hp hh hl' ⊢
  exact hh.trans (by linarith)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
