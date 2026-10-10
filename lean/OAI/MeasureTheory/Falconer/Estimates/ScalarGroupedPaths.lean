import OAI.MeasureTheory.Falconer.Estimates.ScalarPrefixTruncation
import Mathlib.Algebra.BigOperators.Intervals

namespace OAI

/-! Exact branching counts and first splits across groups of regularized
 dyadic levels. No abstract replacement for the original path set is used. -/
namespace Falconer.Regularization

 theorem scalar_grouped_children_card (Q : Finset (CellPath 1))
    (d k : ℕ → ℕ) (hd : Monotone d) (M : ℕ)
    (hcard : ∀ i < M, ∀ p ∈ Q.image (List.take (d i)),
      (prefixChildren Q (d i) (d (i+1)) p).card = 2^(k i))
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ M) (p : CellPath 1)
    (hp : p ∈ Q.image (List.take (d a))) :
    (prefixChildren Q (d a) (d b) p).card = 2^(∑ i ∈ Finset.Ico a b, k i) := by
  induction b,hab using Nat.le_induction with
  | base => simp [prefixChildren_same Q hp]
  | succ b hab ih =>
    rw [prefixChildren_card_compose Q (hd hab) (hd (Nat.le_succ b))]
    have hc : ∀ c ∈ prefixChildren Q (d a) (d b) p,
        (prefixChildren Q (d b) (d (b+1)) c).card = 2^(k b) := by
      intro c hc
      exact hcard b (by omega) c (prefixChildren_mem_image hc)
    rw [Finset.sum_congr rfl hc]
    simp only [Finset.sum_const,Nat.nsmul_eq_mul]
    rw [ih (by omega),Finset.sum_Ico_succ_top hab,pow_add]

 theorem scalar_first_prefix_split (u v : CellPath 1) (d : ℕ → ℕ)
    {a b : ℕ} (hab : a ≤ b) (hstart : u.take (d a) = v.take (d a))
    (hend : u.take (d b) ≠ v.take (d b)) :
    ∃ i, a ≤ i ∧ i < b ∧ u.take (d i) = v.take (d i) ∧
      u.take (d (i+1)) ≠ v.take (d (i+1)) := by
  induction b,hab using Nat.le_induction with
  | base => exact False.elim (hend hstart)
  | succ b hab ih =>
    by_cases heq : u.take (d b) = v.take (d b)
    · exact ⟨b,hab,Nat.lt_succ_self b,heq,hend⟩
    · obtain ⟨i,hai,hib,hi,hi'⟩ := ih heq
      exact ⟨i,hai,by omega,hi,hi'⟩

 theorem scalar_grouped_children_separated {N M : ℕ} {Q : Finset (CellPath 1)}
    (hQ : Q ⊆ cubePaths 1 N) (d k n : ℕ → ℕ) (hd : Monotone d)
    (hdN : ∀ i ≤ M, d i ≤ N)
    (hlevel : ∀ i < M, ScalarBranchingLevel Q (d i) (d (i+1)) (k i) (n i))
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ M) {g : ℝ}
    (hg : ∀ i, a ≤ i → i < b → k i ≠ 0 → g ≤ 6*(1/2:ℝ)^(n i))
    (p : CellPath 1) :
    ∀ u ∈ prefixChildren Q (d a) (d b) p, ∀ v ∈ prefixChildren Q (d a) (d b) p,
      u ≠ v → g ≤ |scalarPathCenter u-scalarPathCenter v| := by
  classical
  intro u hu v hv huv
  have huLen := scalar_prefix_children_length (a := d a) hQ (hdN b hb) p u hu
  have hvLen := scalar_prefix_children_length (a := d a) hQ (hdN b hb) p v hv
  have huParent := scalar_prefix_children_parent (hd hab) Q p u hu
  have hvParent := scalar_prefix_children_parent (hd hab) Q p v hv
  have hsplit := scalar_first_prefix_split u v d hab (huParent.trans hvParent.symm)
    (by
      have huTake : u.take (d b) = u := by rw [← huLen,List.take_length]
      have hvTake : v.take (d b) = v := by rw [← hvLen,List.take_length]
      simpa only [huTake,hvTake] using huv)
  obtain ⟨i,hai,hib,heq,hne⟩ := hsplit
  have hiM : i < M := lt_of_lt_of_le hib hb
  have hui : u.take (d i) ∈ Q.image (List.take (d i)) := by
    obtain ⟨q,hq,hqu⟩ := Finset.mem_image.mp hu
    refine Finset.mem_image.mpr ⟨q,(Finset.mem_filter.mp hq).1,?_⟩
    rw [← hqu,List.take_take,min_eq_left (hd (by omega : i ≤ b))]
  have huc : u.take (d (i+1)) ∈ prefixChildren Q (d i) (d (i+1)) (u.take (d i)) := by
    obtain ⟨q,hq,hqu⟩ := Finset.mem_image.mp hu
    refine Finset.mem_image.mpr ⟨q,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1,?_⟩,?_⟩
    · rw [← hqu,List.take_take,min_eq_left (hd (by omega : i ≤ b))]
    · rw [← hqu,List.take_take,min_eq_left (hd (by omega : i+1 ≤ b))]
  have hvc : v.take (d (i+1)) ∈ prefixChildren Q (d i) (d (i+1)) (u.take (d i)) := by
    obtain ⟨q,hq,hqv⟩ := Finset.mem_image.mp hv
    refine Finset.mem_image.mpr ⟨q,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1,?_⟩,?_⟩
    · rw [heq,← hqv,List.take_take,min_eq_left (hd (by omega : i ≤ b))]
    · rw [← hqv,List.take_take,min_eq_left (hd (by omega : i+1 ≤ b))]
  have hki : k i ≠ 0 := by
    intro hz
    have hc : (prefixChildren Q (d i) (d (i+1)) (u.take (d i))).card ≤ 1 := by
      rw [(hlevel i hiM).children_card _ hui,hz]
      simp
    exact hne (Finset.card_le_one.mp hc _ huc _ hvc)
  have hsep := (hlevel i hiM).separated hui _ huc _ hvc hne
  have hiDepth : d (i+1) ≤ d b := hd (by omega)
  have hdu : |scalarPathCenter u-scalarPathCenter (u.take (d (i+1)))| ≤
      (1/2:ℝ)^(d (i+1)) :=
    scalarPathCenter_same_parent huLen hiDepth (by simp only [List.take_take,min_self])
  have hdv : |scalarPathCenter v-scalarPathCenter (v.take (d (i+1)))| ≤
      (1/2:ℝ)^(d (i+1)) :=
    scalarPathCenter_same_parent hvLen hiDepth (by simp only [List.take_take,min_self])
  have hscale : (1/2:ℝ)^(d (i+1)) ≤ (1/2:ℝ)^(n i) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (hlevel i hiM).level_hi
  have htri : |scalarPathCenter (u.take (d (i+1)))-scalarPathCenter (v.take (d (i+1)))| ≤
      |scalarPathCenter u-scalarPathCenter (u.take (d (i+1)))| +
        |scalarPathCenter u-scalarPathCenter v| +
        |scalarPathCenter v-scalarPathCenter (v.take (d (i+1)))| := by
    calc
      _ ≤ |scalarPathCenter (u.take (d (i+1)))-scalarPathCenter u| +
        |scalarPathCenter u-scalarPathCenter (v.take (d (i+1)))| := abs_sub_le _ _ _
      _ ≤ |scalarPathCenter (u.take (d (i+1)))-scalarPathCenter u| +
        (|scalarPathCenter u-scalarPathCenter v| +
          |scalarPathCenter v-scalarPathCenter (v.take (d (i+1)))|) :=
        add_le_add le_rfl (abs_sub_le _ _ _)
      _ = _ := by rw [abs_sub_comm (scalarPathCenter (u.take (d (i+1))))]; ring
  have hgg := hg i hai hib hki
  linarith

end Falconer.Regularization

end OAI
