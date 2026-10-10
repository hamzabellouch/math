import OAI.Analysis.LipschitzHilbert.Fourier.DyadicLineBad
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace OAI

/-! A jointly measurable count of the actual maximal dyadic occurrences. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.DyadicLineGrid

variable {X B : Type*} [MeasurableSpace X]

theorem measurableSet_bad (f : X × ℝ → ℝ) (hf : Measurable f)
    (q : ℤ) (β : ℝ) (k j : ℤ) :
    MeasurableSet {p | Bad q (fun x => f (p, x)) β k j} := by
  exact measurableSet_le measurable_const
    (hf.stronglyMeasurable.integral_prod_right'.measurable)

theorem measurableSet_maximalBad (q top : ℤ) (bad : X → ℤ → ℤ → Prop)
    (hbad : ∀ k j, MeasurableSet {p | bad p k j}) (k j : ℤ) :
    MeasurableSet {p | MaximalBad q top (bad p) k j} := by
  by_cases hk : k ≤ top
  · have hforall : MeasurableSet {p | ∀ l i, k < l → l ≤ top →
        cell q k j ⊆ cell q l i → ¬bad p l i} := by
      rw [Set.ofPred_forall]
      apply MeasurableSet.iInter
      intro l
      rw [Set.ofPred_forall]
      apply MeasurableSet.iInter
      intro i
      by_cases hkl : k < l
      · by_cases hlt : l ≤ top
        · by_cases hsub : cell q k j ⊆ cell q l i
          · simpa only [hkl, hlt, hsub, true_implies, ← compl_ofPred] using (hbad l i).compl
          · simpa only [hsub, false_implies, implies_true, ofPred_true] using MeasurableSet.univ (α := X)
        · simpa only [hlt, false_implies, implies_true, ofPred_true] using MeasurableSet.univ (α := X)
      · simpa only [hkl, false_implies, ofPred_true] using MeasurableSet.univ (α := X)
    simpa only [MaximalBad, hk, true_and, ofPred_and] using (hbad k j).inter hforall
  · simpa only [MaximalBad, hk, false_and, ofPred_false] using MeasurableSet.empty (α := X)

abbrev Occurrence (B : Type*) := ℤ × B × ℤ × ℤ

def selectedSet (f : B → X × ℝ → ℝ) (top : ℤ) (β : ℝ) (a : Occurrence B) :
    Set (X × ℝ) :=
  {p | a.1 ∈ ({0, 1} : Finset ℤ) ∧
    MaximalBad a.1 top (Bad a.1 (fun x => f a.2.1 (p.1, x)) β) a.2.2.1 a.2.2.2 ∧
    p.2 ∈ cell a.1 a.2.2.1 a.2.2.2}

def selectedCount (f : B → X × ℝ → ℝ) (top : ℤ) (β : ℝ) (p : X × ℝ) : ℝ≥0∞ :=
  ∑' a : Occurrence B, (selectedSet f top β a).indicator 1 p

theorem measurableSet_selectedSet (f : B → X × ℝ → ℝ)
    (hf : ∀ b, Measurable (f b)) (top : ℤ) (β : ℝ) (a : Occurrence B) :
    MeasurableSet (selectedSet f top β a) := by
  by_cases hq : a.1 ∈ ({0, 1} : Finset ℤ)
  · have hm := measurableSet_maximalBad a.1 top
      (fun p => Bad a.1 (fun x => f a.2.1 (p, x)) β)
      (measurableSet_bad (f a.2.1) (hf a.2.1) a.1 β) a.2.2.1 a.2.2.2
    convert
      (hm.preimage measurable_fst).inter ((cell_measurable a.1 a.2.2.1 a.2.2.2).preimage measurable_snd)
      using 1
    ext p
    simp only [selectedSet, hq, true_and, mem_ofPred_eq, mem_inter_iff, mem_preimage]
  · simpa only [selectedSet, hq, false_and, ofPred_false] using MeasurableSet.empty (α := X × ℝ)

theorem measurable_selectedCount [Countable B] (f : B → X × ℝ → ℝ)
    (hf : ∀ b, Measurable (f b)) (top : ℤ) (β : ℝ) :
    Measurable (selectedCount f top β) := by
  apply Measurable.tsum
  intro a
  exact measurable_const.indicator (measurableSet_selectedSet f hf top β a)

/- Distinct popular bins contribute distinct occurrences to the one fixed
measurable count, even though their witnessing intervals are arbitrary. -/
omit [MeasurableSpace X] in
theorem card_le_selectedCount (f : B → X × ℝ → ℝ) (top : ℤ) (β : ℝ)
    (p : X × ℝ) (bins : Finset B)
    (hwitness : ∀ b ∈ bins, ∃ a : Occurrence B, a.2.1 = b ∧ p ∈ selectedSet f top β a) :
    (bins.card : ℝ≥0∞) ≤ selectedCount f top β p := by
  classical
  choose a ha using fun b : bins => hwitness b b.property
  have hinj : Function.Injective a := by
    intro b c hac
    apply Subtype.ext
    exact (ha b).1.symm.trans ((congrArg (fun z : Occurrence B => z.2.1) hac).trans (ha c).1)
  have hcomp := ENNReal.tsum_comp_le_tsum_of_injective hinj
    (fun z : Occurrence B => (selectedSet f top β z).indicator (1 : X × ℝ → ℝ≥0∞) p)
  have hval : ∀ b : bins, (selectedSet f top β (a b)).indicator (1 : X × ℝ → ℝ≥0∞) p = 1 :=
    fun b => Set.indicator_of_mem (ha b).2 _
  simpa only [hval, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    nsmul_eq_mul, mul_one, selectedCount] using hcomp

/-- The one count dominates every finite family of distinct popular bins.
The intervals may be chosen separately for each bin and point. -/
theorem popular_bins_card_le_selectedCount (f : B → X × ℝ → ℝ)
    (hf : ∀ b, Measurable (f b))
    (hbound : ∀ b p, 0 ≤ f b p ∧ f b p ≤ 1)
    {θ H : ℝ} {top : ℤ} (hθ : 0 ≤ θ) (htop : 6 * H ≤ scale top)
    (p : X × ℝ) (bins : Finset B)
    (hpopular : ∀ b ∈ bins, ∃ a c : ℝ, a < c ∧ c - a ≤ H ∧ p.2 ∈ Icc a c ∧
      θ * (c - a) ≤ ∫ x in Icc a c, f b (p.1, x)) :
    (bins.card : ℝ≥0∞) ≤ selectedCount f top (θ / 6) p := by
  apply card_le_selectedCount
  intro b hb
  obtain ⟨a, c, hac, hlen, hx, havg⟩ := hpopular b hb
  have hmeas : Measurable (fun x => f b (p.1, x)) :=
    (hf b).comp (measurable_const.prodMk measurable_id)
  obtain ⟨q, hq, k, j, hmax, hcell⟩ := popular_interval_has_maximalBad hmeas
    (fun x => hbound b (p.1, x)) hac hθ hlen htop hx havg
  exact ⟨(q, b, k, j), rfl, hq, hmax, hcell⟩

end LipschitzHilbert.DyadicLineGrid

end

end OAI
