import OAI.Probability.DilutedSpin.ExternalCovariance
import OAI.Probability.DilutedSpin.ExternalFreshLaw

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω K Z X Y : Type} [Fintype Ω]
    [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K]
    [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}
    {A : K → Type} [∀ i, Fintype (A i)]
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure ((K × ℕ) × Z)) [IsProbabilityMeasure ν]
    (τ : Measure Z) [IsProbabilityMeasure τ] (r s : ℝ≥0) (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : K) → Fin L → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (old : (i : (K × ℕ) × Z) → FinitePath Ω L → FinitePath (A i.1.1) L → ℝ)
    (D E : (i : K) → Z → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)

omit [Countable K] [MeasurableSpace K] [MeasurableSingletonClass K]
  [Countable Z] [MeasurableSpace Z] [MeasurableSingletonClass Z]
  [MeasurableSpace X] [MeasurableSpace Y] in
/-- Changing only the fresh probe label does not change its alphabet, prior,
or observable. All old labels, factors, and counts remain literally fixed. -/
lemma rootExternalTreeScore_probe (q : K) (j k : ℕ) (z : FullRootState Y X ((K×ℕ)×Z) M)
    (v : Z) (t u : ℝ) :
    rootExternalTreeScore S a T (fun i => Q i.1.1) (fun l => m l.succ) base old
      (fun i x y => 1+t*D i.1.1 i.2 x y+u*E i.1.1 i.2 x y)
      (fun i => E i.1.1 i.2) f z ((q,j),v) =
    rootExternalTreeScore S a T (fun i => Q i.1.1) (fun l => m l.succ) base old
      (fun i x y => 1+t*D i.1.1 i.2 x y+u*E i.1.1 i.2 x y)
      (fun i => E i.1.1 i.2) f z ((q,k),v) := rfl

lemma externalAverage_probe
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hf : ∀ x, |f x| ≤ B)
    (hE : ∀ i v x y, |E i v x y| ≤ 1) (t u : ℝ)
    (hA : ∀ i v x y, 1/2 ≤ 1+t*D i v x y+u*E i v x y) (q : K) (j k : ℕ) :
    externalAverage ξ μ ν (τ.map (fun v => ((q,j),v))) r s S a T (fun i => Q i.1.1) m base old
      (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) f t u =
    externalAverage ξ μ ν (τ.map (fun v => ((q,k),v))) r s S a T (fun i => Q i.1.1) m base old
      (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) f t u := by
  rw [externalAverage_fresh_label ξ μ ν τ r s S a T (fun i => Q i.1.1) m base old
        (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) f hb hf (fun i => hE i.1.1 i.2) t u
        (fun i => hA i.1.1 i.2) (fun v : Z => ((q,j),v)) (measurable_const.prodMk measurable_id),
    externalAverage_fresh_label ξ μ ν τ r s S a T (fun i => Q i.1.1) m base old
        (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) f hb hf (fun i => hE i.1.1 i.2) t u
        (fun i => hA i.1.1 i.2) (fun v : Z => ((q,k),v)) (measurable_const.prodMk measurable_id)]
  apply integral_congr_ae
  filter_upwards [] with z
  apply integral_congr_ae
  filter_upwards [] with v
  exact rootExternalTreeScore_probe S a T Q m base old D E f q j k z v t u

lemma externalCovariance_probe
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    {B : ℝ} (hf : ∀ x, |f x| ≤ B)
    (hE : ∀ i v x y, |E i v x y| ≤ 1) (t u : ℝ)
    (hA : ∀ i v x y, 1/2 ≤ 1+t*D i v x y+u*E i v x y) (q : K) (j k : ℕ) :
    externalCovariance ξ μ ν (τ.map (fun v => ((q,j),v))) r s S a T (fun i => Q i.1.1) m base old
      (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) f t u =
    externalCovariance ξ μ ν (τ.map (fun v => ((q,k),v))) r s S a T (fun i => Q i.1.1) m base old
      (fun i => D i.1.1 i.2) (fun i => E i.1.1 i.2) f t u := by
  unfold externalCovariance
  rw [externalAverage_probe ξ μ ν τ r s S a T Q m base old D E f hb hf hE t u hA q j k,
    externalAverage_probe ξ μ ν τ r s S a T Q m base old D E (fun _ => 1) hb
      (B := 1) (by intro; norm_num) hE t u hA q j k]

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
