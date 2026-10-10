import OAI.Geometry.IsometricImmersion.Taylor.ChainTermDerivative
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation

def ChainWord.single (n : ℕ) : ChainWord := ⟨1, ![n]⟩
def ChainWord.pair (a b : ℕ) : ChainWord := ⟨2, ![a, b]⟩
def ChainWord.triple (a b c : ℕ) : ChainWord := ⟨3, ![a, b, c]⟩

def ChainWord.children (w : ChainWord) : List ChainWord :=
  w.prepend :: List.ofFn w.bump

def chainSum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (J : ℝ → E) (ws : List ChainWord) (t : ℝ) : ℝ :=
  (ws.map (fun w => chainTerm F J w t)).sum

theorem chainSum_append
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (J : ℝ → E) (ws vs : List ChainWord) (t : ℝ) :
    chainSum F J (ws ++ vs) t = chainSum F J ws t + chainSum F J vs t := by
  simp [chainSum]

theorem chainSum_replicate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (J : ℝ → E) (w : ChainWord) (n : ℕ) (t : ℝ) :
    chainSum F J (List.replicate n w) t = (n : ℝ) * chainTerm F J w t := by
  simp [chainSum, nsmul_eq_mul]

theorem chainSum_children
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (J : ℝ → E) (w : ChainWord) (t : ℝ) :
    chainSum F J w.children t = chainTerm F J w.prepend t +
      ∑ i, chainTerm F J (w.bump i) t := by
  simp [chainSum, ChainWord.children, List.map_ofFn, List.sum_ofFn]

theorem chainSum_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {J : ℝ → E} {t : ℝ}
    (hF : ContDiffAt ℝ ∞ F (J t)) (hJ : ContDiffAt ℝ ∞ J t)
    (ws : List ChainWord) :
    HasDerivAt (chainSum F J ws) (chainSum F J (ws.flatMap ChainWord.children) t) t := by
  induction ws with
  | nil => convert hasDerivAt_const t (0 : ℝ) using 1 <;> rfl
  | cons w ws ih =>
    have hw := chainTerm_hasDerivAt hF hJ w
    rw [← chainSum_children] at hw
    convert hw.add ih using 1 <;> try rfl
    rw [List.flatMap_cons, chainSum_append]

theorem ChainWord.children_properties {w v : ChainWord} {n : ℕ}
    (hn : 1 ≤ n) (hp : w.Positive) (hb : w.Bounded n) (hv : v ∈ w.children) :
    v.Positive ∧ v.total = w.total + 1 ∧ v.Bounded (n + 1) := by
  simp only [ChainWord.children, List.mem_cons, List.mem_ofFn] at hv
  rcases hv with rfl | ⟨i, rfl⟩
  · refine ⟨ChainWord.prepend_positive hp, w.prepend_total, ?_⟩
    exact ChainWord.prepend_bounded (by omega) (fun j => Nat.le_succ_of_le (hb j))
  · exact ⟨ChainWord.bump_positive hp i, w.bump_total i,
      ChainWord.bump_bounded hb i⟩

def topResidualWords : ℕ → List ChainWord
  | 0 => [ChainWord.triple 1 1 1]
  | m + 1 =>
      (topResidualWords m).flatMap ChainWord.children ++
        List.replicate (m + 3) (ChainWord.triple 1 1 (m + 2)) ++
        List.replicate (m + 3) (ChainWord.pair 2 (m + 2))

theorem topResidualWords_properties : ∀ m w, w ∈ topResidualWords m →
    w.Positive ∧ w.total = m + 3 ∧ w.Bounded (m + 1) := by
  intro m
  induction m with
  | zero =>
    intro w hw
    simp only [topResidualWords, List.mem_singleton] at hw
    subst w
    refine ⟨?_, ?_, ?_⟩
    · change ∀ i : Fin 3, 0 < (![1, 1, 1] : Fin 3 → ℕ) i
      intro i; fin_cases i <;> norm_num
    · change (∑ i : Fin 3, (![1, 1, 1] : Fin 3 → ℕ) i) = 0 + 3
      norm_num [Fin.sum_univ_succ]
    · change ∀ i : Fin 3, (![1, 1, 1] : Fin 3 → ℕ) i ≤ 0 + 1
      intro i; fin_cases i <;> norm_num
  | succ m ih =>
    intro w hw
    change w ∈ ((topResidualWords m).flatMap ChainWord.children ++
      List.replicate (m + 3) (ChainWord.triple 1 1 (m + 2))) ++
      List.replicate (m + 3) (ChainWord.pair 2 (m + 2)) at hw
    rw [List.mem_append, List.mem_append] at hw
    rcases hw with (hw | hw) | hw
    · obtain ⟨v, hv, hw⟩ := List.mem_flatMap.mp hw
      obtain ⟨hp, ht, hb⟩ := ih v hv
      obtain ⟨hwp, hwt, hwb⟩ := ChainWord.children_properties (by omega) hp hb hw
      refine ⟨hwp, ?_, ?_⟩
      · omega
      · simpa [Nat.add_assoc] using hwb
    · have he := List.eq_of_mem_replicate hw
      subst w
      refine ⟨?_, ?_, ?_⟩
      · change ∀ i : Fin 3, 0 < (![1, 1, m + 2] : Fin 3 → ℕ) i
        intro i; fin_cases i <;> simp
      · change (∑ i : Fin 3, (![1, 1, m + 2] : Fin 3 → ℕ) i) = m + 1 + 3
        simp [Fin.sum_univ_succ]; omega
      · change ∀ i : Fin 3, (![1, 1, m + 2] : Fin 3 → ℕ) i ≤ m + 1 + 1
        intro i; fin_cases i <;> simp
    · have he := List.eq_of_mem_replicate hw
      subst w
      refine ⟨?_, ?_, ?_⟩
      · change ∀ i : Fin 2, 0 < (![2, m + 2] : Fin 2 → ℕ) i
        intro i; fin_cases i <;> simp
      · change (∑ i : Fin 2, (![2, m + 2] : Fin 2 → ℕ) i) = m + 1 + 3
        simp [Fin.sum_univ_succ]; omega
      · change ∀ i : Fin 2, (![2, m + 2] : Fin 2 → ℕ) i ≤ m + 1 + 1
        intro i; fin_cases i <;> simp

theorem topResidualWords_sum_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (J : ℝ → E) (m : ℕ) (t : ℝ) :
    chainSum F J (topResidualWords (m + 1)) t =
      chainSum F J ((topResidualWords m).flatMap ChainWord.children) t +
      (m + 3 : ℝ) * chainTerm F J (ChainWord.triple 1 1 (m + 2)) t +
      (m + 3 : ℝ) * chainTerm F J (ChainWord.pair 2 (m + 2)) t := by
  simp only [topResidualWords, chainSum_append, chainSum_replicate, Nat.cast_add,
    Nat.cast_ofNat, add_assoc]

theorem topResidual_high_unique {m : ℕ} (hm : 8 ≤ m + 3)
    {w : ChainWord} (hw : w ∈ topResidualWords m) (base : Fin w.arity → ℕ)
    (hb : ∀ i, base i ≤ 2) {i j : Fin w.arity}
    (hi : m + 2 ≤ w.order i + base i) (hj : m + 2 ≤ w.order j + base j) : i = j := by
  classical
  by_contra hij
  have hsum := (topResidualWords_properties m w hw).2.1
  have hpair : w.order i + w.order j ≤ w.total := by
    have hh : ∑ k ∈ ({i, j} : Finset (Fin w.arity)), w.order k ≤ ∑ k, w.order k :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    simpa [ChainWord.total, Finset.sum_pair hij] using hh
  have hbi := hb i
  have hbj := hb j
  omega

end SmoothLocal.HighEquation

end

end OAI
