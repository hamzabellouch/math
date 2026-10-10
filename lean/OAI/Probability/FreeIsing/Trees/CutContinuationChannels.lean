import OAI.Probability.FreeIsing.Trees.CutContinuations
import OAI.Probability.FreeIsing.Trees.CutLevelConcentration

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem367.CutContinuationChannels
open RootedBroadcast

variable {d : ℕ} {A : Type*} [MeasurableSpace A]

abbrev ConeSample (A : Type*) (v : TreeVertex d) :=
  (DescendantVertex v → IsingSpin) × (DescendantVertex v → A)

def globalCone (v : TreeVertex d)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) : ConeSample A v :=
  ((fun u => z.1 u.1), fun u => z.2 u.1)

def restrictCone {u v : TreeVertex d} (h : u.1 <+: v.1)
    (z : ConeSample A u) : ConeSample A v :=
  ((fun w => z.1 ⟨w.1, h.trans w.2⟩), fun w => z.2 ⟨w.1, h.trans w.2⟩)

theorem measurable_globalCone (v : TreeVertex d) : Measurable (globalCone (A := A) v) := by
  unfold globalCone
  fun_prop

theorem measurable_restrictCone {u v : TreeVertex d} (h : u.1 <+: v.1) :
    Measurable (restrictCone (A := A) h) := by
  unfold restrictCone
  fun_prop

def globalFactors (F : ∀ v : TreeVertex d, ConeSample A v → ℝ)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) (v : TreeVertex d) : ℝ :=
  F v (globalCone v z)

def continuationChannel (F : ∀ v : TreeVertex d, ConeSample A v → ℝ)
    {k L : ℕ} (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L)
    (z : ConeSample A p.1) : ℝ :=
  ∏ j ∈ Finset.range L,
    F (rootPathVertex (appendCutContinuation p w).1 (k + 1 + (j + 1)))
      (restrictCone (cutContinuation_vertex_descendant p w j) z)

theorem measurable_continuationChannel
    (F : ∀ v : TreeVertex d, ConeSample A v → ℝ) (hF : ∀ v, Measurable (F v))
    {k L : ℕ} (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L) :
    Measurable (continuationChannel F p w) := by
  apply Finset.measurable_fun_prod
  intro j hj
  exact (hF _).comp (measurable_restrictCone _)

omit [MeasurableSpace A] in
theorem continuationChannel_mem_Icc
    (F : ∀ v : TreeVertex d, ConeSample A v → ℝ)
    (hb : ∀ v z, 0 ≤ F v z ∧ F v z ≤ 1)
    {k L : ℕ} (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L)
    (z : ConeSample A p.1) : continuationChannel F p w z ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Finset.prod_nonneg (fun _ _ => (hb _ _).1),
    Finset.prod_le_one₀ (fun _ _ => (hb _ _).1) (fun _ _ => (hb _ _).2)⟩

omit [MeasurableSpace A] in
@[simp] theorem continuationChannel_globalCone
    (F : ∀ v : TreeVertex d, ConeSample A v → ℝ)
    {k L : ℕ} (p : TreeShell d (k + 1)) (w : ReducedTail (cutLastColor p) L)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) :
    continuationChannel F p w (globalCone p.1 z) =
      cutContinuationProduct (globalFactors F z) p w := rfl

def averageChannel (F : ∀ v : TreeVertex d, ConeSample A v → ℝ)
    {k : ℕ} (p : TreeShell d (k + 1)) (L : ℕ) (z : ConeSample A p.1) : ℝ :=
  (∑ w : ReducedTail (cutLastColor p) L, continuationChannel F p w z) /
    (Fintype.card (ReducedTail (cutLastColor p) L) : ℝ)

theorem measurable_averageChannel
    (F : ∀ v : TreeVertex d, ConeSample A v → ℝ) (hF : ∀ v, Measurable (F v))
    {k : ℕ} (p : TreeShell d (k + 1)) (L : ℕ) : Measurable (averageChannel F p L) :=
  (Finset.measurable_fun_sum _ (fun w _ => measurable_continuationChannel F hF p w)).div_const _

omit [MeasurableSpace A] in
theorem averageChannel_mem_Icc (hd : 2 ≤ d)
    (F : ∀ v : TreeVertex d, ConeSample A v → ℝ)
    (hb : ∀ v z, 0 ≤ F v z ∧ F v z ≤ 1)
    {k : ℕ} (p : TreeShell d (k + 1)) (L : ℕ) (z : ConeSample A p.1) :
    averageChannel F p L z ∈ Set.Icc (0 : ℝ) 1 := by
  have hc : (0 : ℝ) < Fintype.card (ReducedTail (cutLastColor p) L) := by
    rw [card_reducedTail]
    exact_mod_cast pow_pos (by omega : 0 < d - 1) L
  constructor
  · exact div_nonneg (Finset.sum_nonneg
      (fun w _ => (continuationChannel_mem_Icc F hb p w z).1)) hc.le
  · apply (div_le_iff₀ hc).mpr
    simpa using Finset.sum_le_sum
      (fun w (_ : w ∈ (Finset.univ : Finset (ReducedTail (cutLastColor p) L))) =>
        (continuationChannel_mem_Icc F hb p w z).2)

omit [MeasurableSpace A] in
@[simp] theorem averageChannel_globalCone
    (F : ∀ v : TreeVertex d, ConeSample A v → ℝ)
    {k : ℕ} (p : TreeShell d (k + 1)) (L : ℕ)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) :
    averageChannel F p L (globalCone p.1 z) =
      (∑ w : ReducedTail (cutLastColor p) L,
        cutContinuationProduct (globalFactors F z) p w) / (((d - 1) ^ L : ℕ) : ℝ) := by
  simp [averageChannel]

omit [MeasurableSpace A] in
theorem path_average_le_averageChannel
    (F : ∀ v : TreeVertex d, ConeSample A v → ℝ)
    (hb : ∀ v z, 0 ≤ F v z ∧ F v z ≤ 1)
    {k : ℕ} (I : Finset (TreeShell d (k + 1))) (L : ℕ)
    (z : (TreeVertex d → IsingSpin) × (TreeVertex d → A)) :
    (∑ v ∈ cutDescendants I L, rootPathProduct (globalFactors F z) v.1) /
        ((cutDescendants I L).card : ℝ) ≤
      (∑ p ∈ I, averageChannel F p L (globalCone p.1 z)) / (I.card : ℝ) := by
  simpa only [averageChannel_globalCone] using
    average_rootPathProduct_le_continuation_average (globalFactors F z)
      (fun v => hb v _) I L

theorem integral_averageChannel_le (hd : 2 ≤ d)
    (F : ∀ v : TreeVertex d, ConeSample A v → ℝ) (hF : ∀ v, Measurable (F v))
    (hb : ∀ v z, 0 ≤ F v z ∧ F v z ≤ 1)
    {k : ℕ} (p : TreeShell d (k + 1)) (L : ℕ)
    (P : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    [IsProbabilityMeasure P] {m : ℝ}
    (hmean : ∀ w : ReducedTail (cutLastColor p) L,
      (∫ z, cutContinuationProduct (globalFactors F z) p w ∂P) ≤ m) :
    (∫ z, averageChannel F p L (globalCone p.1 z) ∂P) ≤ m := by
  have hc : (0 : ℝ) < Fintype.card (ReducedTail (cutLastColor p) L) := by
    rw [card_reducedTail]
    exact_mod_cast pow_pos (by omega : 0 < d - 1) L
  have hi (w : ReducedTail (cutLastColor p) L) :
      Integrable (fun z => continuationChannel F p w (globalCone p.1 z)) P := by
    apply Integrable.of_bound
      ((measurable_continuationChannel F hF p w).comp (measurable_globalCone p.1)).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro z
    change ‖continuationChannel F p w (globalCone p.1 z)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (continuationChannel_mem_Icc F hb p w _).1]
    exact (continuationChannel_mem_Icc F hb p w _).2
  calc
    _ = (∑ w : ReducedTail (cutLastColor p) L,
          ∫ z, continuationChannel F p w (globalCone p.1 z) ∂P) /
        (Fintype.card (ReducedTail (cutLastColor p) L) : ℝ) := by
      unfold averageChannel
      rw [integral_div, integral_finsetSum _ (fun w _ => hi w)]
    _ ≤ (∑ _w : ReducedTail (cutLastColor p) L, m) /
        (Fintype.card (ReducedTail (cutLastColor p) L) : ℝ) := by
      apply div_le_div_of_nonneg_right _ hc.le
      exact Finset.sum_le_sum (fun w _ => hmean w)
    _ = m := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_div_cancel_left₀ m hc.ne'

theorem measure_path_average_ge_le [StandardBorelSpace A]
    {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (hd : 2 ≤ d)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (F : ∀ v : TreeVertex d, ConeSample A v → ℝ) (hF : ∀ v, Measurable (F v))
    (hb : ∀ v z, 0 ≤ F v z ∧ F v z ≤ 1)
    {k : ℕ} (I : Finset (TreeShell d (k + 1))) (hI : I.Nonempty) (L : ℕ)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (hmean : ∀ p ∈ I, ∀ w : ReducedTail (cutLastColor p) L,
      (∫ z, cutContinuationProduct (globalFactors F z) p w
        ∂μ.prod (Measure.infinitePi ν)) ≤ τ / 4) :
    (μ.prod (Measure.infinitePi ν))
      {z | τ ≤ (∑ v ∈ cutDescendants I L, rootPathProduct (globalFactors F z) v.1) /
        ((cutDescendants I L).card : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(I.card : ℝ) * τ ^ 2 / 2)) := by
  calc
    _ ≤ (μ.prod (Measure.infinitePi ν))
        {z | τ ≤ (∑ p ∈ I, averageChannel F p L (globalCone p.1 z)) / (I.card : ℝ)} := by
      apply measure_mono
      intro z hz
      exact hz.trans (path_average_le_averageChannel F hb I L z)
    _ ≤ _ := hμ.measure_cutLevel_average_ge_le h0 h1 (k + 1) ν
      (fun p => averageChannel F p L) (fun p => measurable_averageChannel F hF p L)
      (fun p z => averageChannel_mem_Icc hd F hb p L z) I hI hτ
      (fun p hp => integral_averageChannel_le hd F hF hb p L _ (hmean p hp))

theorem measure_restricted_path_average_ge_le_double_exp [StandardBorelSpace A]
    {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (hd : 2 ≤ d)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (F : ∀ v : TreeVertex d, ConeSample A v → ℝ) (hF : ∀ v, Measurable (F v))
    (hb : ∀ v z, 0 ≤ F v z ∧ F v z ≤ 1)
    (forbidden : Finset (Fin d)) (hforbidden : forbidden.card ≤ 1) (k L : ℕ)
    {q ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hq : q ≤ Real.log ((d : ℝ) - 1) / 8)
    (hlevel : ℓ / 2 - 1 ≤ (k + 1 : ℕ))
    (hmean : ∀ p ∈ avoidingTreeCut forbidden k, ∀ w : ReducedTail (cutLastColor p) L,
      (∫ z, cutContinuationProduct (globalFactors F z) p w
        ∂μ.prod (Measure.infinitePi ν)) ≤ Real.exp (-q * ℓ) / 4) :
    (μ.prod (Measure.infinitePi ν))
      {z | Real.exp (-q * ℓ) ≤
        (∑ v ∈ cutDescendants (avoidingTreeCut forbidden k) L,
          rootPathProduct (globalFactors F z) v.1) /
            ((cutDescendants (avoidingTreeCut forbidden k) L).card : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(((d : ℝ) - 1) ^ (ℓ / 4)) / (2 * ((d : ℝ) - 1)))) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  exact (measure_path_average_ge_le hμ h0 h1 hd ν F hF hb
    (avoidingTreeCut forbidden k) (avoidingTreeCut_nonempty hd forbidden hforbidden k)
    L (Real.exp_pos _).le hmean).trans
      (ENNReal.ofReal_le_ofReal (BoundedAverageConcentration.exponential_card_bound
        (by linarith) hℓ hq (rpow_le_card_avoidingTreeCut hd forbidden hforbidden k hlevel)))

end Problem367.CutContinuationChannels

end

end OAI
