import Mathlib
import OAI.Probability.Ballisticity.Model

namespace OAI

section

open MeasureTheory Filter
open scoped Topology ENNReal
namespace TailCuts

def score (L U : ℤ → ℝ) (R j : ℤ) : ℝ := min (L j) (U (j + R))

lemma maximizing_cuts_escape {L U : ℤ → ℝ}
    (hL : StrictMono L) (hU : StrictAnti U)
    (hL0 : ∀ j, 0 < L j) (hU0 : ∀ j, 0 < U j)
    (hLm : Tendsto L atBot (𝓝 0)) (hUm : Tendsto U atTop (𝓝 0))
    (j : ℕ → ℤ) (hmax : ∀ (n : ℕ) (k : ℤ), score L U (n : ℤ) k ≤ score L U (n : ℤ) (j n)) :
    Tendsto j atTop atBot ∧ Tendsto (fun n => j n + (n : ℤ)) atTop atTop := by
  constructor
  · apply tendsto_atBot.2
    intro b
    have hshift : Tendsto (fun n : ℕ => b - 1 + (n : ℤ)) atTop atTop :=
      tendsto_atTop.2 fun z => by
        filter_upwards [(tendsto_natCast_atTop_atTop (R := ℤ)).eventually (eventually_ge_atTop (z - (b - 1)))] with n hn
        omega
    have ht : ∀ᶠ n : ℕ in atTop, U (b - 1 + (n : ℤ)) < L (b - 1) :=
      (hUm.comp hshift).eventually (gt_mem_nhds (hL0 _))
    filter_upwards [ht] with n hn
    by_contra hj
    have hb : b ≤ j n := le_of_lt (lt_of_not_ge hj)
    have hleft : U (j n + (n : ℤ)) < L (j n - 1) :=
      lt_of_le_of_lt (hU.antitone (by omega)) (lt_of_lt_of_le hn (hL.monotone (by omega)))
    have hright : U (j n + (n : ℤ)) < U (j n - 1 + (n : ℤ)) := hU (by omega)
    have hs : score L U (n : ℤ) (j n) < score L U (n : ℤ) (j n - 1) := by
      unfold score
      exact lt_of_le_of_lt (min_le_right _ _) (lt_min hleft hright)
    exact (not_lt_of_ge (hmax n (j n - 1))) hs
  · apply tendsto_atTop.2
    intro b
    have hshift : Tendsto (fun n : ℕ => b + 1 - (n : ℤ)) atTop atBot :=
      tendsto_atBot.2 fun z => by
        filter_upwards [(tendsto_natCast_atTop_atTop (R := ℤ)).eventually (eventually_ge_atTop (b + 1 - z))] with n hn
        omega
    have ht : ∀ᶠ n : ℕ in atTop, L (b + 1 - (n : ℤ)) < U (b + 1) :=
      (hLm.comp hshift).eventually (gt_mem_nhds (hU0 _))
    filter_upwards [ht] with n hn
    by_contra hj
    have hb : j n + (n : ℤ) ≤ b := le_of_lt (lt_of_not_ge hj)
    have hright : L (j n) < U (j n + 1 + (n : ℤ)) :=
      lt_of_le_of_lt (hL.monotone (by omega)) (lt_of_lt_of_le hn (hU.antitone (by omega)))
    have hleft : L (j n) < L (j n + 1) := hL (by omega)
    have hs : score L U (n : ℤ) (j n) < score L U (n : ℤ) (j n + 1) := by
      unfold score
      exact lt_of_le_of_lt (min_le_left _ _) (lt_min hleft hright)
    exact (not_lt_of_ge (hmax n (j n + 1))) hs

end TailCuts

namespace TailCuts

lemma exists_maximizing_cut {L U : ℤ → ℝ}
    (hL0 : ∀ j, 0 < L j) (hU0 : ∀ j, 0 < U j)
    (hLm : Tendsto L atBot (𝓝 0)) (hUm : Tendsto U atTop (𝓝 0)) (R : ℤ) :
    ∃ j : ℤ, ∀ k, score L U R k ≤ score L U R j := by
  have ht : 0 < score L U R 0 := lt_min (hL0 _) (hU0 _)
  obtain ⟨a, ha⟩ := eventually_atBot.mp (hLm.eventually (gt_mem_nhds ht))
  obtain ⟨b, hb⟩ := eventually_atTop.mp (hUm.eventually (gt_mem_nhds ht))
  let S := Finset.Icc (min a 0) (max (b - R) 0)
  have h0 : (0 : ℤ) ∈ S := Finset.mem_Icc.mpr ⟨min_le_right _ _, le_max_right _ _⟩
  obtain ⟨j, hj, hmax⟩ := S.exists_max_image (score L U R) ⟨0, h0⟩
  refine ⟨j, fun k => ?_⟩
  by_cases hk : k ∈ S
  · exact hmax k hk
  · have hout : k < min a 0 ∨ max (b - R) 0 < k := by
      simpa only [S, Finset.mem_Icc, not_and_or, not_le] using hk
    apply le_trans _ (hmax 0 h0)
    rcases hout with hk | hk
    · exact (min_le_left _ _).trans (ha k (by omega)).le
    · exact (min_le_right _ _).trans (hb (k + R) (by omega)).le

noncomputable def lower (μ : Measure ℤ) (j : ℤ) : ℝ := μ.real (Set.Iic j)
noncomputable def upper (μ : Measure ℤ) (j : ℤ) : ℝ := μ.real (Set.Ici j)

lemma lower_pos (μ : Measure ℤ) [IsFiniteMeasure μ]
    (hμ : ∀ j, 0 < μ.real {j}) (j : ℤ) : 0 < lower μ j := by
  exact (hμ j).trans_le (measureReal_mono (by intro x hx; have hx' : x = j := hx; subst x; exact (show (j : ℤ) ≤ j from le_rfl)))

lemma upper_pos (μ : Measure ℤ) [IsFiniteMeasure μ]
    (hμ : ∀ j, 0 < μ.real {j}) (j : ℤ) : 0 < upper μ j := by
  exact (hμ j).trans_le (measureReal_mono (by intro x hx; have hx' : x = j := hx; subst x; exact (show (j : ℤ) ≤ j from le_rfl)))

lemma lower_strictMono (μ : Measure ℤ) [IsFiniteMeasure μ]
    (hμ : ∀ j, 0 < μ.real {j}) : StrictMono (lower μ) := by
  intro i j hij
  have hd : Disjoint (Set.Iic i) {j} := Set.disjoint_left.mpr (by
    intro x hx hxj
    simp only [Set.mem_singleton_iff] at hxj
    subst x
    exact (not_le_of_gt hij) hx)
  have hu := measureReal_union (μ := μ) hd (measurableSet_singleton j)
  have hs : Set.Iic i ∪ {j} ⊆ Set.Iic j := by
    intro x hx
    rcases hx with hx | hx
    · exact hx.trans hij.le
    · have hx' : x = j := hx
      subst x
      exact (show (j : ℤ) ≤ j from le_rfl)
  have hm := measureReal_mono (μ := μ) hs
  dsimp [lower]
  linarith [hμ j]

lemma upper_strictAnti (μ : Measure ℤ) [IsFiniteMeasure μ]
    (hμ : ∀ j, 0 < μ.real {j}) : StrictAnti (upper μ) := by
  intro i j hij
  have hd : Disjoint (Set.Ici j) {i} := Set.disjoint_left.mpr (by
    intro x hx hxi
    simp only [Set.mem_singleton_iff] at hxi
    subst x
    exact (not_le_of_gt hij) hx)
  have hu := measureReal_union (μ := μ) hd (measurableSet_singleton i)
  have hs : Set.Ici j ∪ {i} ⊆ Set.Ici i := by
    intro x hx
    rcases hx with hx | hx
    · exact hij.le.trans hx
    · have hx' : x = i := hx
      subst x
      exact (show (i : ℤ) ≤ i from le_rfl)
  have hm := measureReal_mono (μ := μ) hs
  dsimp [upper]
  linarith [hμ i]

lemma lower_tendsto (μ : Measure ℤ) [IsFiniteMeasure μ] :
    Tendsto (lower μ) atBot (𝓝 0) := by
  have ht := tendsto_measure_iInter_atBot (μ := μ)
    (s := fun j : ℤ => Set.Iic j) (fun j => measurableSet_Iic.nullMeasurableSet)
    (fun _ _ hij => Set.Iic_subset_Iic.mpr hij) ⟨0, measure_ne_top _ _⟩
  have he : (⋂ j : ℤ, Set.Iic j) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx' := Set.mem_iInter.mp hx (x - 1)
    simp only [Set.mem_Iic] at hx'
    omega
  rw [he, measure_empty] at ht
  change Tendsto (fun j => (μ (Set.Iic j)).toReal) atBot (𝓝 0)
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp ht

lemma upper_tendsto (μ : Measure ℤ) [IsFiniteMeasure μ] :
    Tendsto (upper μ) atTop (𝓝 0) := by
  have ht := tendsto_measure_iInter_atTop (μ := μ)
    (s := fun j : ℤ => Set.Ici j) (fun j => measurableSet_Ici.nullMeasurableSet)
    (fun _ _ hij => Set.Ici_subset_Ici.mpr hij) ⟨0, measure_ne_top _ _⟩
  have he : (⋂ j : ℤ, Set.Ici j) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx' := Set.mem_iInter.mp hx (x + 1)
    simp only [Set.mem_Ici] at hx'
    omega
  rw [he, measure_empty] at ht
  change Tendsto (fun j => (μ (Set.Ici j)).toReal) atTop (𝓝 0)
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp ht

theorem finite_profile_cuts_escape (μ : Measure ℤ) [IsFiniteMeasure μ]
    (hμ : ∀ j, 0 < μ.real {j}) :
    (∀ R : ℤ, ∃ j : ℤ, ∀ k, score (lower μ) (upper μ) R k ≤ score (lower μ) (upper μ) R j) ∧
    (∀ j : ℕ → ℤ,
      (∀ (n : ℕ) (k : ℤ), score (lower μ) (upper μ) (n : ℤ) k ≤
        score (lower μ) (upper μ) (n : ℤ) (j n)) →
      Tendsto j atTop atBot ∧ Tendsto (fun n => j n + (n : ℤ)) atTop atTop) := by
  exact ⟨exists_maximizing_cut (lower_pos μ hμ) (upper_pos μ hμ) (lower_tendsto μ) (upper_tendsto μ),
    fun j hj => maximizing_cuts_escape (lower_strictMono μ hμ) (upper_strictAnti μ hμ)
      (lower_pos μ hμ) (upper_pos μ hμ) (lower_tendsto μ) (upper_tendsto μ) j hj⟩

end TailCuts

namespace TailCuts

lemma measurable_maximizing_cut {D : Type*} [MeasurableSpace D]
    (L U : D → ℤ → ℝ) (R : ℤ)
    (hL : ∀ j, Measurable (fun d => L d j)) (hU : ∀ j, Measurable (fun d => U d j))
    (hex : ∀ d, ∃ j, ∀ k, score (L d) (U d) R k ≤ score (L d) (U d) R j) :
    ∃ j : D → ℤ, Measurable j ∧
      ∀ d k, score (L d) (U d) R k ≤ score (L d) (U d) R (j d) := by
  classical
  let p : D → ℕ → Prop := fun d n => ∀ k,
    score (L d) (U d) R k ≤ score (L d) (U d) R (Denumerable.ofNat ℤ n)
  have hp : ∀ d, ∃ n, p d n := by
    intro d
    obtain ⟨j, hj⟩ := hex d
    exact ⟨Encodable.encode j, by simpa only [p, Denumerable.ofNat_encode] using hj⟩
  have hm : ∀ n, MeasurableSet {d | p d n} := by
    intro n
    simp only [p, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro k
    exact measurableSet_le ((hL k).min (hU (k+R)))
      ((hL _).min (hU _))
  refine ⟨fun d => Denumerable.ofNat ℤ (Nat.find (hp d)),
    (measurable_of_countable (Denumerable.ofNat ℤ)).comp (measurable_find hp hm), ?_⟩
  intro d
  exact Nat.find_spec (hp d)

end TailCuts

end

end OAI
