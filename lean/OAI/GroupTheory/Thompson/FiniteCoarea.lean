import OAI.GroupTheory.Thompson.FiniteAverage
import OAI.GroupTheory.Thompson.FiniteLevels
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

universe uG

namespace ThompsonNonamenability

open scoped BigOperators symmDiff

variable {G : Type uG} [DecidableEq G]

private theorem sum_indicator_eq_card (A C : Finset G) (hAC : A ⊆ C) :
    (∑ x ∈ C, if x ∈ A then (1 : ℝ) else 0) = (A.card : ℝ) := by
  classical
  have hfilter : C.filter (fun x => x ∈ A) = A := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hx => ⟨hAC hx, hx⟩⟩
  rw [← Finset.sum_filter, hfilter]
  simp

private theorem sum_abs_indicators_eq_card_symmDiff
    (A B C : Finset G) (hAC : A ⊆ C) (hBC : B ⊆ C) :
    (∑ x ∈ C,
      |(if x ∈ A then (1 : ℝ) else 0) -
        (if x ∈ B then (1 : ℝ) else 0)|) = ((A ∆ B).card : ℝ) := by
  classical
  have hsub : A ∆ B ⊆ C := by
    intro x hx
    rcases Finset.mem_symmDiff.mp hx with hx | hx
    · exact hAC hx.1
    · exact hBC hx.1
  calc
    _ = ∑ x ∈ C, if x ∈ A ∆ B then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;>
        simp [hA, hB, Finset.mem_symmDiff]
    _ = _ := sum_indicator_eq_card (A ∆ B) C hsub

private theorem finite_value_mem {K : Finset G} {p : G → ℝ}
    (hpK : ∀ x, x ∉ K → p x = 0) (x : G) :
    p x ∈ insert 0 (K.image p) := by
  classical
  by_cases hx : x ∈ K
  · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem p hx)
  · rw [hpK x hx]
    exact Finset.mem_insert_self _ _

namespace FiniteLevelChain

variable {K : Finset G} {p : G → ℝ}

/-- The strict superlevel set at the lower endpoint of a positive layer. -/
def levelSet (c : FiniteLevelChain K p) (i : Fin c.n) : Finset G := by
  classical
  exact K.filter (fun x => c.value i.castSucc < p x)

omit [DecidableEq G] in
theorem levelSet_subset [DecidableEq G] (c : FiniteLevelChain K p) (i : Fin c.n) :
    c.levelSet i ⊆ K := Finset.filter_subset _ _

/-- The finite carrier restriction does not change positive-threshold membership. -/
theorem mem_levelSet (c : FiniteLevelChain K p)
    (hpK : ∀ x, x ∉ K → p x = 0) (i : Fin c.n) (x : G) :
    x ∈ c.levelSet i ↔ c.value i.castSucc < p x := by
  classical
  have hv : 0 ≤ c.value i.castSucc := by
    simpa only [c.value_zero] using
      c.strictMono_value.monotone (Fin.zero_le i.castSucc)
  constructor
  · intro hx
    exact (Finset.mem_filter.mp hx).2
  · intro hx
    apply Finset.mem_filter.mpr
    refine ⟨?_, hx⟩
    by_contra hxK
    rw [hpK x hxK] at hx
    exact (not_lt_of_ge hv) hx

omit [DecidableEq G] in
theorem levelSet_nonempty [DecidableEq G] (c : FiniteLevelChain K p) (i : Fin c.n) :
    (c.levelSet i).Nonempty := by
  classical
  have hlt : c.value i.castSucc < c.value i.succ :=
    c.strictMono_value (by
      change i.val < i.val + 1
      exact Nat.lt_succ_self i.val)
  have hv : 0 ≤ c.value i.castSucc := by
    simpa only [c.value_zero] using
      c.strictMono_value.monotone (Fin.zero_le i.castSucc)
  have hpos : 0 < c.value i.succ := lt_of_le_of_lt hv hlt
  have hmem : c.value i.succ ∈ insert 0 (K.image p) := by
    rw [← c.image_value_eq]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have himage : c.value i.succ ∈ K.image p :=
    (Finset.mem_insert.mp hmem).resolve_left (ne_of_gt hpos)
  obtain ⟨x, hxK, hpx⟩ := Finset.mem_image.mp himage
  refine ⟨x, Finset.mem_filter.mpr ⟨hxK, ?_⟩⟩
  rw [hpx]
  exact hlt

/-- Exact finite layer-cake identity for the mass. -/
theorem coarea_mass (c : FiniteLevelChain K p)
    (hpK : ∀ x, x ∉ K → p x = 0) :
    (∑ x ∈ K, p x) =
      ∑ i : Fin c.n, c.gap i * ((c.levelSet i).card : ℝ) := by
  classical
  calc
    _ = ∑ x ∈ K, ∑ i : Fin c.n, c.gap i *
        (if c.value i.castSucc < p x then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact c.reconstruct (p x) (finite_value_mem hpK x)
    _ = ∑ i : Fin c.n, ∑ x ∈ K, c.gap i *
        (if c.value i.castSucc < p x then (1 : ℝ) else 0) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.mul_sum]
      congr 1
      calc
        _ = ∑ x ∈ K, if x ∈ c.levelSet i then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          simp only [c.mem_levelSet hpK i x]
        _ = _ := sum_indicator_eq_card _ K (c.levelSet_subset i)

end FiniteLevelChain

section Translation

variable [Group G]

theorem mem_leftTranslate_iff (h : G) (A : Finset G) (x : G) :
    x ∈ leftTranslate h A ↔ h⁻¹ * x ∈ A := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨h⁻¹ * x, hx, by simp⟩

namespace FiniteLevelChain

variable {K : Finset G} {p : G → ℝ}

/-- Exact coarea identity for one left translation, over its finite support carrier. -/
theorem coarea_translation (c : FiniteLevelChain K p)
    (hpK : ∀ x, x ∉ K → p x = 0) (h : G) :
    (∑ x ∈ K ∪ leftTranslate h K, |p (h⁻¹ * x) - p x|) =
      ∑ i : Fin c.n, c.gap i *
        ((leftTranslate h (c.levelSet i) ∆ c.levelSet i).card : ℝ) := by
  classical
  calc
    _ = ∑ x ∈ K ∪ leftTranslate h K, ∑ i : Fin c.n, c.gap i *
        |(if c.value i.castSucc < p (h⁻¹ * x) then (1 : ℝ) else 0) -
          (if c.value i.castSucc < p x then (1 : ℝ) else 0)| := by
      apply Finset.sum_congr rfl
      intro x hx
      exact c.abs_sub_eq_sum (p (h⁻¹ * x)) (p x)
        (finite_value_mem hpK _) (finite_value_mem hpK _)
    _ = ∑ i : Fin c.n, ∑ x ∈ K ∪ leftTranslate h K, c.gap i *
        |(if c.value i.castSucc < p (h⁻¹ * x) then (1 : ℝ) else 0) -
          (if c.value i.castSucc < p x then (1 : ℝ) else 0)| :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.mul_sum]
      congr 1
      have hleft : leftTranslate h (c.levelSet i) ⊆ K ∪ leftTranslate h K := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_union_right _
          (Finset.mem_image_of_mem (fun y => h * y) (c.levelSet_subset i hy))
      have hright : c.levelSet i ⊆ K ∪ leftTranslate h K := by
        intro x hx
        exact Finset.mem_union_left _ (c.levelSet_subset i hx)
      calc
        _ = ∑ x ∈ K ∪ leftTranslate h K,
            |(if x ∈ leftTranslate h (c.levelSet i) then (1 : ℝ) else 0) -
              (if x ∈ c.levelSet i then (1 : ℝ) else 0)| := by
          apply Finset.sum_congr rfl
          intro x hx
          simp only [mem_leftTranslate_iff, c.mem_levelSet hpK]
        _ = _ := sum_abs_indicators_eq_card_symmDiff _ _ _ hleft hright

/-- Summing the exact translation identities introduces no cardinality factor. -/
theorem coarea_sum (c : FiniteLevelChain K p)
    (hpK : ∀ x, x ∉ K → p x = 0) (S : Finset G) :
    (∑ h ∈ S, ∑ x ∈ K ∪ leftTranslate h K, |p (h⁻¹ * x) - p x|) =
      ∑ i : Fin c.n, c.gap i *
        (∑ h ∈ S, ((leftTranslate h (c.levelSet i) ∆ c.levelSet i).card : ℝ)) := by
  calc
    _ = ∑ h ∈ S, ∑ i : Fin c.n, c.gap i *
        ((leftTranslate h (c.levelSet i) ∆ c.levelSet i).card : ℝ) :=
      Finset.sum_congr rfl (fun h _ => c.coarea_translation hpK h)
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]

end FiniteLevelChain

/-- A nonempty level inside the supplied finite support has small total boundary. -/
theorem finite_folner_of_small_defect_subset
    {K S : Finset G} {p : G → ℝ} {ε : ℝ}
    (hp0 : ∀ g, 0 ≤ p g)
    (hpK : ∀ g, g ∉ K → p g = 0)
    (mass : ∑ g ∈ K, p g = 1)
    (hdef : (∑ h ∈ S, ∑ x ∈ K ∪ leftTranslate h K,
      |p (h⁻¹ * x) - p x|) < ε) :
    ∃ A : Finset G, A ⊆ K ∧ A.Nonempty ∧
      (∑ h ∈ S, ((leftTranslate h A ∆ A).card : ℝ)) < ε * (A.card : ℝ) := by
  classical
  obtain ⟨c⟩ := FiniteLevelChain.exists_chain K p (fun g _ => hp0 g)
  have hmass : (∑ i : Fin c.n, c.gap i * ((c.levelSet i).card : ℝ)) = 1 :=
    (c.coarea_mass hpK).symm.trans mass
  have hex : ∃ i : Fin c.n,
      (∑ h ∈ S, ((leftTranslate h (c.levelSet i) ∆ c.levelSet i).card : ℝ)) <
        ε * ((c.levelSet i).card : ℝ) := by
    by_contra hnone
    have hfail : ∀ i : Fin c.n, ε * ((c.levelSet i).card : ℝ) ≤
        ∑ h ∈ S, ((leftTranslate h (c.levelSet i) ∆ c.levelSet i).card : ℝ) :=
      fun i => le_of_not_gt (fun hi => hnone ⟨i, hi⟩)
    have hle : ε ≤ ∑ h ∈ S, ∑ x ∈ K ∪ leftTranslate h K,
        |p (h⁻¹ * x) - p x| := by
      calc
        ε = ε * ∑ i : Fin c.n, c.gap i * ((c.levelSet i).card : ℝ) := by
          rw [hmass, mul_one]
        _ = ∑ i : Fin c.n, c.gap i * (ε * ((c.levelSet i).card : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ ≤ ∑ i : Fin c.n, c.gap i *
            (∑ h ∈ S, ((leftTranslate h (c.levelSet i) ∆ c.levelSet i).card : ℝ)) :=
          Finset.sum_le_sum (fun i _ =>
            mul_le_mul_of_nonneg_left (hfail i) (c.gap_pos i).le)
        _ = _ := (c.coarea_sum hpK S).symm
    exact (not_lt_of_ge hle) hdef
  obtain ⟨i, hi⟩ := hex
  exact ⟨c.levelSet i, c.levelSet_subset i, c.levelSet_nonempty i, hi⟩

/-- Finite probability with small total translation defect yields a finite Følner set. -/
theorem finite_folner_of_small_defect
    {K S : Finset G} {p : G → ℝ} {ε : ℝ}
    (hp0 : ∀ g, 0 ≤ p g)
    (hpK : ∀ g, g ∉ K → p g = 0)
    (mass : ∑ g ∈ K, p g = 1)
    (hdef : (∑ h ∈ S, ∑ x ∈ K ∪ leftTranslate h K,
      |p (h⁻¹ * x) - p x|) < ε) :
    ∃ A : Finset G, A.Nonempty ∧
      (∑ h ∈ S, ((leftTranslate h A ∆ A).card : ℝ)) < ε * (A.card : ℝ) := by
  obtain ⟨A, _, hA, hsmall⟩ := finite_folner_of_small_defect_subset hp0 hpK mass hdef
  exact ⟨A, hA, hsmall⟩

end Translation

end ThompsonNonamenability

end

end OAI
