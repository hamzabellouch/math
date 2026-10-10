import OAI.Probability.SignedSweeps.BudgetAbsorption
import OAI.Probability.SignedSweeps.ColumnSubgroup

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma diagram_rowLens_sum (lam : YoungDiagram) : lam.rowLens.sum = lam.card := by
  have hh (c : ℕ × ℕ) (hc : c ∈ lam.cells) : c.1 ∈ Finset.range (lam.colLen 0) := by
    have hi : c.1 < lam.colLen c.2 := YoungDiagram.mem_iff_lt_colLen.mp hc
    exact Finset.mem_range.mpr (hi.trans_le (lam.colLen_anti 0 c.2 (Nat.zero_le _)))
  have he := Finset.sum_fiberwise_of_maps_to (g := Prod.fst) hh (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at he
  rw [YoungDiagram.rowLens, ← List.sum_toFinset _ List.nodup_range]
  simp only [List.toFinset_range, YoungDiagram.card]
  simp_rw [YoungDiagram.rowLen_eq_card, YoungDiagram.row]
  exact he

lemma partition_rowLens_sum {n : ℕ} (lam : Partition n) : lam.1.rowLens.sum = n :=
  (diagram_rowLens_sum lam.1).trans lam.2

lemma sorted_drop_term_bound (L : List ℕ) (hL : L.SortedGE) (q a : ℕ)
    (ha : a ∈ L.drop q) : q * a ≤ L.sum := by
  have hlen := List.length_pos_of_mem ha
  simp only [List.length_drop] at hlen
  have hq : q ≤ L.length := by omega
  have hsplit := List.pairwise_append.mp (show
      (L.take q ++ L.drop q).Pairwise (fun x y : ℕ => y ≤ x) by
    simpa using hL.pairwise)
  have hb : (L.take q).length * a ≤ (L.take q).sum := by
    simpa using List.sum_le_sum (l := L.take q) (f := fun _ => a) (g := id)
      (fun b hb => hsplit.2.2 b hb a ha)
  rw [List.length_take, min_eq_left hq] at hb
  have hs := List.sum_take_add_sum_drop L q
  omega

def truncatePartition {n : ℕ} (q : ℕ) (lam : Partition n) :
    Partition ((lam.1.rowLens.take q).sum) := by
  let hsort : (lam.1.rowLens.take q).SortedGE :=
    ((lam.1.rowLens_sorted).pairwise.sublist (List.take_sublist q _)).sortedGE
  refine ⟨YoungDiagram.ofRowLens _ hsort, ?_⟩
  rw [← diagram_rowLens_sum, YoungDiagram.rowLens_ofRowLens_eq_self]
  intro a ha
  exact lam.1.pos_of_mem_rowLens a (List.mem_of_mem_take ha)

@[simp]
lemma truncatePartition_rowLens {n : ℕ} (q : ℕ) (lam : Partition n) :
    (truncatePartition q lam).1.rowLens = lam.1.rowLens.take q := by
  exact YoungDiagram.rowLens_ofRowLens_eq_self
    (hw := ((lam.1.rowLens_sorted).pairwise.sublist (List.take_sublist q _)).sortedGE)
    (fun a ha =>
    lam.1.pos_of_mem_rowLens a (List.mem_of_mem_take ha))

def partsEntropy (total : ℝ) (L : List ℕ) : ℝ :=
  (L.map (fun a : ℕ => (a : ℝ) * Real.log (total / a))).sum

lemma partsEntropy_mono {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) (L : List ℕ)
    (hL : ∀ a ∈ L, 0 < a) : partsEntropy A L ≤ partsEntropy B L := by
  apply List.sum_le_sum
  intro a ha
  have hp : (0 : ℝ) < a := by exact_mod_cast hL a ha
  apply mul_le_mul_of_nonneg_left _ hp.le
  apply Real.log_le_log (div_pos hA hp)
  exact div_le_div_of_nonneg_right hAB hp.le

lemma partsEntropy_mono_of_total (A B : ℕ) (hAB : A ≤ B) (L : List ℕ)
    (hL : ∀ a ∈ L, 0 < a) (hs : L.sum ≤ A) : partsEntropy A L ≤ partsEntropy B L := by
  by_cases hA : A = 0
  · subst A
    have hz : L = [] := List.eq_nil_iff_forall_not_mem.mpr (by
      intro a ha
      have he : a = 0 := (List.sum_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hs)) a ha
      exact (Nat.ne_of_gt (hL a ha)) he)
    simp only [hz, partsEntropy, List.map_nil, List.sum_nil, le_refl]
  · apply partsEntropy_mono (by exact_mod_cast Nat.pos_of_ne_zero hA) (by exact_mod_cast hAB) L hL

lemma partsEntropy_drop_bound {total q : ℕ} (hq : 0 < q) (L : List ℕ)
    (hL : ∀ a ∈ L, 0 < a) (hterm : ∀ a ∈ L, q * a ≤ total) :
    (L.sum : ℝ) * Real.log q ≤ partsEntropy total L := by
  have hsum : (L.map (fun a : ℕ => (a : ℝ) * Real.log q)).sum = (L.sum : ℝ) * Real.log q := by
    clear hL hterm
    induction L with
    | nil => simp
    | cons a L ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, add_mul, ih]
  rw [← hsum]
  apply List.sum_le_sum
  intro a ha
  have hp : (0 : ℝ) < a := by exact_mod_cast hL a ha
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  apply mul_le_mul_of_nonneg_left _ hp.le
  apply Real.log_le_log hq'
  rw [le_div_iff₀ hp]
  exact_mod_cast hterm a ha

lemma signedEntropy_truncate {u v : ℕ} (α : Partition u) (β : Partition v) {q : ℕ}
    (hq : 0 < q) :
    signedEntropy (truncatePartition q α) (truncatePartition q β) +
      (((α.1.rowLens.drop q).sum + (β.1.rowLens.drop q).sum : ℕ) : ℝ) * Real.log q ≤
        signedEntropy α β := by
  let A := α.1.rowLens.take q ++ β.1.rowLens.take q
  let D := α.1.rowLens.drop q ++ β.1.rowLens.drop q
  have hα := List.sum_take_add_sum_drop α.1.rowLens q
  have hβ := List.sum_take_add_sum_drop β.1.rowLens q
  rw [partition_rowLens_sum] at hα hβ
  have hst : A.sum + D.sum = u + v := by simp only [A, D, List.sum_append]; omega
  have hsumle : A.sum ≤ u + v := by omega
  have hpA : ∀ a ∈ A, 0 < a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact α.1.pos_of_mem_rowLens a (List.mem_of_mem_take ha)
    · exact β.1.pos_of_mem_rowLens a (List.mem_of_mem_take ha)
  have hpD : ∀ a ∈ D, 0 < a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact α.1.pos_of_mem_rowLens a (List.mem_of_mem_drop ha)
    · exact β.1.pos_of_mem_rowLens a (List.mem_of_mem_drop ha)
  have ht : ∀ a ∈ D, q * a ≤ u + v := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · have := sorted_drop_term_bound α.1.rowLens α.1.rowLens_sorted q a ha
      rw [partition_rowLens_sum] at this
      omega
    · have := sorted_drop_term_bound β.1.rowLens β.1.rowLens_sorted q a ha
      rw [partition_rowLens_sum] at this
      omega
  have hkeep := partsEntropy_mono_of_total A.sum (u + v) hsumle A hpA (le_refl _)
  have hdrop := partsEntropy_drop_bound hq D hpD ht
  have hfull : partsEntropy (u + v : ℕ) A + partsEntropy (u + v : ℕ) D = signedEntropy α β := by
    have hs (L : List ℕ) : partsEntropy (u + v : ℕ) (L.take q) +
        partsEntropy (u + v : ℕ) (L.drop q) = partsEntropy (u + v : ℕ) L := by
      rw [partsEntropy, partsEntropy, ← List.sum_append, ← List.map_append, List.take_append_drop]
      rfl
    simpa only [partsEntropy, A, D, List.map_append, List.sum_append, ← add_assoc,
      add_comm, add_left_comm, Nat.cast_add, signedEntropy] using congrArg₂ (· + ·) (hs α.1.rowLens) (hs β.1.rowLens)
  have htrunc : partsEntropy A.sum A = signedEntropy (truncatePartition q α) (truncatePartition q β) := by
    simp [partsEntropy, signedEntropy, A]
  have hd : (D.sum : ℝ) = ((α.1.rowLens.drop q).sum + (β.1.rowLens.drop q).sum : ℕ) := by
    simp [D]
  rw [← hfull, ← htrunc, ← hd]
  exact add_le_add hkeep hdrop

lemma remainderBudget_growth {κ : ℝ} (hκ : 0 ≤ κ) {d l L : ℕ} (hd : 1 ≤ d)
    (hlL : l ≤ L) (hLn : L ≤ 2 ^ d) :
    remainderBudget κ d L ≤ remainderBudget κ d l +
      (coefficient κ d * Real.log ((2 ^ d : ℕ) : ℝ) + 1) * ((L : ℝ) - l) := by
  simp only [remainderBudget_eq_clippedBudget]
  exact clippedBudget_growth ((by positivity : (0 : ℝ) ≤ κ / 2).trans (coefficient_bounds hκ hd).1) (pow_pos (by norm_num) _) hlL hLn

lemma truncated_budget_le {η κ : ℝ} (hη : 0 ≤ η) (hκ : 0 ≤ κ)
    {d u v l : ℕ} (hd : 1 ≤ d) (hn : u + v + l = 2 ^ d)
    (α : Partition u) (β : Partition v) {q : ℕ} (hq : 0 < q)
    (hcost : coefficient κ d * Real.log ((2 ^ d : ℕ) : ℝ) + 1 ≤
      coefficient η d * Real.log q) :
    coefficient η d * signedEntropy (truncatePartition q α) (truncatePartition q β) +
      remainderBudget κ d (l + (α.1.rowLens.drop q).sum + (β.1.rowLens.drop q).sum) ≤
    coefficient η d * signedEntropy α β + remainderBudget κ d l := by
  let t := (α.1.rowLens.drop q).sum + (β.1.rowLens.drop q).sum
  have ht : l + t ≤ 2 ^ d := by
    have hu := List.sum_take_add_sum_drop α.1.rowLens q
    have hv := List.sum_take_add_sum_drop β.1.rowLens q
    rw [partition_rowLens_sum] at hu hv
    dsimp only [t]
    omega
  have hg := remainderBudget_growth hκ hd (Nat.le_add_right l t) ht
  have he := mul_le_mul_of_nonneg_left (signedEntropy_truncate α β hq)
    ((by positivity : (0 : ℝ) ≤ η / 2).trans (coefficient_bounds hη hd).1)
  have hc := mul_le_mul_of_nonneg_right hcost (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
  simp only [Nat.cast_add, add_sub_cancel_left] at hg
  rw [Nat.add_assoc]
  change coefficient η d * signedEntropy (truncatePartition q α) (truncatePartition q β) +
    remainderBudget κ d (l + t) ≤ _
  change coefficient η d * (signedEntropy (truncatePartition q α) (truncatePartition q β) +
    (t : ℝ) * Real.log q) ≤ _ at he
  nlinarith

lemma truncation_coefficient_eventually {η κ ε : ℝ} (hη : 0 < η) (hκ : 0 ≤ κ)
    (hε : 0 < ε) (hκsmall : κ < η * ε / 2) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d ≥ d₀,
      coefficient κ d * Real.log ((2 ^ d : ℕ) : ℝ) + 1 ≤
        coefficient η d * Real.log (⌈((2 ^ d : ℕ) : ℝ) ^ ε⌉₊ : ℕ) := by
  open Filter in
  have hlarge : ∀ᶠ d : ℕ in atTop,
      1 / (η * ε / 2 - κ) ≤ Real.log ((2 ^ d : ℕ) : ℝ) := by
    have ht : Tendsto (fun d : ℕ => Real.log ((2 ^ d : ℕ) : ℝ)) atTop atTop := by
      simp_rw [nat_two_pow_log]
      exact tendsto_natCast_atTop_atTop.atTop_mul_const (Real.log_pos (by norm_num))
    exact ht.eventually_ge_atTop _
  obtain ⟨D, hD⟩ := Filter.eventually_atTop.mp hlarge
  refine ⟨max D 1, le_max_right _ _, ?_⟩
  intro d hd
  have hd1 : 1 ≤ d := (le_max_right D 1).trans hd
  have hn : (0 : ℝ) < (2 ^ d : ℕ) := by positivity
  have hlog : 0 ≤ Real.log ((2 ^ d : ℕ) : ℝ) := by rw [nat_two_pow_log]; positivity
  have hq : ε * Real.log ((2 ^ d : ℕ) : ℝ) ≤
      Real.log (⌈((2 ^ d : ℕ) : ℝ) ^ ε⌉₊ : ℕ) := by
    rw [← Real.log_rpow hn]
    exact Real.log_le_log (Real.rpow_pos_of_pos hn _) (Nat.le_ceil _)
  have hηlb := (coefficient_bounds hη.le hd1).1
  have hκub := (coefficient_bounds hκ hd1).2
  have hl := (div_le_iff₀ (sub_pos.mpr hκsmall)).mp (hD d ((le_max_left _ _).trans hd))
  have hc := mul_le_mul_of_nonneg_left hq ((by positivity : (0 : ℝ) ≤ η / 2).trans (coefficient_bounds hη.le hd1).1)
  have hηterm := mul_le_mul_of_nonneg_right hηlb (mul_nonneg hε.le hlog)
  have hκterm := mul_le_mul_of_nonneg_right hκub hlog
  nlinarith

end SignedSweeps
end

end OAI
