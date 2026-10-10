import OAI.Probability.DilutedSpin.SelectedPalm

namespace OAI

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {Ω I Z : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [MeasurableSpace Z] {L n : ℕ}

lemma measurable_treeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : Z → FinitePath Ω L → ℝ) (roots : Fin n → I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) (q : Fin n)
    (hb : ∀ y, Measurable (fun z => base z y)) :
    Measurable (fun z => treeScore S a T Q m (base z) roots factor numerator f q) := by
  unfold treeScore
  refine PrescribedTree.measurable_tilt_sample_expect S (tower roots L T Q) m ?_ ?_
  · exact fun w => (hb _).add measurable_const
  · exact fun _ => measurable_const

lemma measurable_selectedTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : Z → FinitePath Ω L → ℝ) (roots : Fin n → I)
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (t u : ℝ) (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (hb : ∀ y, Measurable (fun z => base z y)) :
    Measurable (fun z => selectedTreeScore S a T Q m (base z) roots sel fixed D E t u f) := by
  unfold selectedTreeScore
  refine PrescribedTree.measurable_tilt_sample_expect S (tower roots L T Q) m ?_ ?_
  · exact fun w => (hb _).add measurable_const
  · exact fun _ => measurable_const

lemma measurable_insertedTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : Z → FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (hb : ∀ y, Measurable (fun z => base z y)) :
    Measurable (fun z => insertedTreeScore S a T Q m (base z) roots i factor numerator f) := by
  simpa only [treeScore_insertion] using measurable_treeScore S a T Q m base (Fin.cons i roots) factor numerator f 0 hb

lemma abs_insertedTreeScore_le (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I) (i : I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (hn : ∀ i x y, |numerator i x y| ≤ 1)
    (hA : ∀ i x y, 1/2 ≤ factor i x y) :
    |insertedTreeScore S a T Q m base roots i factor numerator f| ≤ 2*B := by
  rw [← treeScore_insertion]
  exact abs_treeScore_le S a T Q m base _ factor numerator f 0 hf hn hA

variable [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ν : Measure I) [IsProbabilityMeasure ν]

noncomputable def averagedInsertedTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) : ℝ :=
  ∫ i, insertedTreeScore S a T Q m base roots i factor numerator f ∂ν

omit [IsProbabilityMeasure ν] in
lemma measurable_averagedInsertedTreeScore (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : Z → FinitePath Ω L → ℝ) (roots : Fin n → I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ)
    (hb : ∀ y, Measurable (fun z => base z y)) :
    Measurable (fun z => averagedInsertedTreeScore ν S a T Q m (base z) roots factor numerator f) := by
  have hh : Measurable (fun z : Z × I => insertedTreeScore S a T Q m (base z.1) roots z.2 factor numerator f) := by
    apply measurable_from_prod_countable_left
    exact fun i => measurable_insertedTreeScore S a T Q m base roots i factor numerator f hb
  exact hh.stronglyMeasurable.integral_prod_right'.measurable

omit [Countable I] [MeasurableSingletonClass I] in
lemma abs_averagedInsertedTreeScore_le (S : PrescribedTree L) (a : S.Leaf)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ) (roots : Fin n → I)
    (factor numerator : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (f : (S.Leaf → FinitePath Ω L) → ℝ) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (hn : ∀ i x y, |numerator i x y| ≤ 1)
    (hA : ∀ i x y, 1/2 ≤ factor i x y) :
    |averagedInsertedTreeScore ν S a T Q m base roots factor numerator f| ≤ 2*B := by
  have hh := norm_integral_le_of_norm_le_const (μ := ν) (C := 2*B)
    (f := fun i => insertedTreeScore S a T Q m base roots i factor numerator f)
    (ae_of_all _ (fun i => by simpa only [Real.norm_eq_abs] using abs_insertedTreeScore_le S a T Q m base roots i factor numerator f hf hn hA))
  simpa only [averagedInsertedTreeScore,Real.norm_eq_abs,probReal_univ,mul_one] using hh

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
