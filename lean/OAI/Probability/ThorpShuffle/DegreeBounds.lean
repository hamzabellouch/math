import OAI.Probability.ThorpShuffle.PartitionBounds

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

def rowTail (D : YoungDiagram) : YoungDiagram where
  cells := (D.cells.filter (fun p => p.1 ≠ 0)).image (fun p => (p.1 - 1, p.2))
  isLowerSet := by
    intro y x hxy hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hpD, hp0⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_image.mpr
    refine ⟨(x.1 + 1, x.2), Finset.mem_filter.mpr ⟨?_, by omega⟩, ?_⟩
    · exact D.up_left_mem (by have := hxy.1; omega) hxy.2 hpD
    · simp

lemma mem_rowTail (D : YoungDiagram) (i j : ℕ) : (i, j) ∈ rowTail D ↔ (i + 1, j) ∈ D := by
  change (i, j) ∈ (D.cells.filter (fun p => p.1 ≠ 0)).image (fun p => (p.1 - 1, p.2)) ↔ _
  constructor
  · intro h
    obtain ⟨p, hp, he⟩ := Finset.mem_image.mp h
    obtain ⟨hpD, hp0⟩ := Finset.mem_filter.mp hp
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    have hp : p = (i + 1, j) := Prod.ext (by dsimp at h₁; omega) h₂
    simpa only [← hp, YoungDiagram.mem_cells] using hpD
  · intro h
    exact Finset.mem_image.mpr ⟨(i + 1, j), Finset.mem_filter.mpr ⟨h, by omega⟩, by simp⟩

def rowTailCells (D : YoungDiagram) : Cells (rowTail D) ≃ Lower D where
  toFun x := ⟨⟨(x.val.1 + 1, x.val.2), (mem_rowTail D _ _).mp x.property⟩, by simp⟩
  invFun x := ⟨(x.val.val.1 - 1, x.val.val.2), (mem_rowTail D _ _).mpr (by
    have h : x.val.val.1 - 1 + 1 = x.val.val.1 := by have := x.property; omega
    simpa only [h, YoungDiagram.mem_cells, Prod.mk.eta] using x.val.property)⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by
    apply Subtype.ext; apply Subtype.ext
    exact Prod.ext (by have := x.property; dsimp; omega) rfl

lemma rowTail_ext {D E : YoungDiagram} (hrow : D.rowLen 0 = E.rowLen 0) (ht : rowTail D = rowTail E) : D = E := by
  apply YoungDiagram.ext
  ext p
  rcases p with ⟨i, j⟩
  cases i with
  | zero => simp only [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, hrow]
  | succ i => simp only [YoungDiagram.mem_cells, ← mem_rowTail, ht]

def orient (D : YoungDiagram) : YoungDiagram :=
  if D.colLen 0 ≤ D.rowLen 0 then D else D.transpose

def orientation (D : YoungDiagram) : Bool := decide (D.colLen 0 ≤ D.rowLen 0)

lemma orient_rowLen (D : YoungDiagram) : (orient D).rowLen 0 = longest D := by
  unfold orient longest
  split_ifs with h
  · exact (max_eq_left h).symm
  · rw [YoungDiagram.rowLen_transpose, max_eq_right (by omega)]

lemma orient_card (D : YoungDiagram) : Fintype.card (Cells (orient D)) = Fintype.card (Cells D) := by
  unfold orient
  split_ifs
  · rfl
  · exact (Fintype.card_congr (transposeCells D).toEquiv).symm

lemma orient_extensions (D : YoungDiagram) :
    Fintype.card (Extensions (Cells (orient D))) = Fintype.card (Extensions (Cells D)) := by
  by_cases h : D.colLen 0 ≤ D.rowLen 0
  · exact congrArg (fun E : YoungDiagram => Fintype.card (Extensions (Cells E))) (show orient D = D by simp [orient, h])
  · exact (congrArg (fun E : YoungDiagram => Fintype.card (Extensions (Cells E)))
      (show orient D = D.transpose by simp [orient, h])).trans
      (extensions_card_orderIso (transposeCells D)).symm

lemma recover_orientation (D : YoungDiagram) :
    (if orientation D then orient D else (orient D).transpose) = D := by
  unfold orientation orient
  split_ifs <;> simp_all

lemma longest_le_card (D : YoungDiagram) : longest D ≤ Fintype.card (Cells D) :=
  max_le (rowLen_le_card D 0) (colLen_le_card D 0)

theorem defect_count_le (n u : ℕ) :
    Fintype.card {p : Nat.Partition n // n - longest (ofPartition p) = u} ≤
      2 * Fintype.card (Nat.Partition u) := by
  let T := {p : Nat.Partition n // n - longest (ofPartition p) = u}
  have hcard (p : T) : Fintype.card (Cells (rowTail (orient (ofPartition p.val)))) = u := by
    rw [Fintype.card_congr (rowTailCells _)]
    have hh := card_lower_add (orient (ofPartition p.val))
    rw [orient_rowLen, orient_card, card_ofPartition] at hh
    have hp := p.property
    omega
  let f (p : T) : Bool × Nat.Partition u :=
    (orientation (ofPartition p.val), toPartition (rowTail (orient (ofPartition p.val))) u (hcard p))
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply ofPartition_injective
    have hflag : orientation (ofPartition p.val) = orientation (ofPartition q.val) := congrArg Prod.fst hpq
    have ht : rowTail (orient (ofPartition p.val)) = rowTail (orient (ofPartition q.val)) := by
      have he := congrArg (fun z : Bool × Nat.Partition u => ofPartition z.2) hpq
      simpa only [f, of_toPartition] using he
    have hr : (orient (ofPartition p.val)).rowLen 0 = (orient (ofPartition q.val)).rowLen 0 := by
      simp only [orient_rowLen]
      have hp := p.property
      have hq := q.property
      have hp' := longest_le_card (ofPartition p.val)
      have hq' := longest_le_card (ofPartition q.val)
      rw [card_ofPartition] at hp' hq'
      omega
    have ho := rowTail_ext hr ht
    rw [← recover_orientation (ofPartition p.val), ← recover_orientation (ofPartition q.val), hflag, ho]
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod, Fintype.card_bool] using hh

end Thorp.Young

namespace Thorp.Specht
open scoped Classical
open Thorp.Young

abbrev NShape (n : ℕ) := Shape (Fin n)

def defect {n : ℕ} (p : NShape n) : ℕ := n - longest (ofPartition p)

lemma diagram_card {n : ℕ} (p : NShape n) : Fintype.card (Cells (ofPartition p)) = n := by
  simpa only [Fintype.card_fin] using card_ofPartition p

lemma extensions_le_degree {n : ℕ} (p : NShape n) :
    Fintype.card (Extensions (Cells (ofPartition p))) ≤ degree p :=
  extensions_card_le_degree (ofPartition p) (canonicalTableau p)

lemma degree_pos {n : ℕ} (p : NShape n) : 0 < degree p := by
  let := extensions_nonempty (Cells (ofPartition p))
  exact (Fintype.card_pos).trans_le (extensions_le_degree p)

lemma defect_add_longest {n : ℕ} (p : NShape n) : defect p + longest (ofPartition p) = n := by
  have h := longest_le_card (ofPartition p)
  rw [diagram_card] at h
  exact Nat.sub_add_cancel h

lemma choose_longest_le_degree {n : ℕ} (p : NShape n) (k : ℕ)
    (hk : k ≤ defect p) (hL : k ≤ longest (ofPartition p)) :
    (longest (ofPartition p)).choose k ≤ degree p := by
  have hc : Fintype.card (Lower (orient (ofPartition p))) = defect p := by
    have hh := card_lower_add (orient (ofPartition p))
    rw [orient_rowLen, orient_card, diagram_card] at hh
    have hd := defect_add_longest p
    omega
  have hh := choose_le_extensions (orient (ofPartition p)) k (by rwa [hc]) (by rwa [orient_rowLen])
  rw [orient_rowLen, orient_extensions] at hh
  exact hh.trans (extensions_le_degree p)

lemma small_defect_degree {n : ℕ} (p : NShape n) (h : 4 * defect p ≤ n) :
    3 ^ defect p ≤ degree p := by
  have hd := defect_add_longest p
  exact (pow_le_choose_of_mul_le 3 _ _ (by omega)).trans
    (choose_longest_le_degree p _ le_rfl (by omega))

lemma fixed_defect_degree {n : ℕ} (p : NShape n) (hp : 0 < defect p) (h : 2 * defect p ≤ n) :
    n - 2 * defect p + 1 ≤ degree p := by
  have hd := defect_add_longest p
  have hh := sub_add_one_le_choose (longest (ofPartition p)) (defect p) hp (by omega)
  have he : longest (ofPartition p) - defect p = n - 2 * defect p := by omega
  rw [he] at hh
  exact hh.trans (choose_longest_le_degree p _ le_rfl (by omega))

lemma factorial_third_bound (n : ℕ) : ((n : ℝ) / 3) ^ n ≤ (n.factorial : ℝ) := by
  rcases n with _ | n
  · norm_num
  have hn : (1 : ℝ) ≤ n + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hs : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (n + 1)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [Real.pi_gt_three]
  have he : (n + 1 : ℝ) / 3 ≤ (n + 1) / Real.exp 1 := by
    apply div_le_div_of_nonneg_left (by positivity) (Real.exp_pos 1) Real.exp_one_lt_three.le
  have hh := Stirling.le_factorial_stirling (n + 1)
  push_cast at hh
  simpa only [Nat.cast_add, Nat.cast_one] using (pow_le_pow_left₀ (by positivity) he (n+1)).trans
    ((le_mul_of_one_le_left (by positivity) hs).trans hh)

lemma small_longest_degree {n : ℕ} (p : NShape n) (hn : 0 < n)
    (hL : 8 * longest (ofPartition p) ≤ n) :
    (4 / 3 : ℝ) ^ n ≤ degree p := by
  have hf := factorial_le_rank_degree (ofPartition p) (canonicalTableau p)
  have hf' : (n.factorial : ℝ) ≤ (2 * (longest (ofPartition p) : ℝ)) ^ n * (degree p : ℝ) := by
    exact_mod_cast hf
  have he : (2 * (longest (ofPartition p) : ℝ)) ≤ (n : ℝ) / 4 := by
    have hh : (8 : ℝ) * longest (ofPartition p) ≤ n := by exact_mod_cast hL
    linarith
  have hd : (0 : ℝ) ≤ degree p := Nat.cast_nonneg _
  have hh := (factorial_third_bound n).trans (hf'.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) he n) hd))
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hid : ((n : ℝ) / 3) ^ n = ((n : ℝ) / 4) ^ n * (4 / 3 : ℝ)^n := by rw [← mul_pow]; congr 1; ring
  rw [hid] at hh
  exact le_of_mul_le_mul_left hh (pow_pos (by positivity : (0 : ℝ) < n / 4) n)

lemma bulk_degree {n : ℕ} (p : NShape n) (hn : 0 < n) (hu : n < 4 * defect p) :
    (2 : ℝ) ^ (n / 16) ≤ degree p := by
  by_cases hL : 8 * longest (ofPartition p) ≤ n
  · have hh : (2 : ℝ) ^ (n / 16) ≤ (4 / 3 : ℝ)^n := by
      have hbase : (2 : ℝ) ≤ (4 / 3 : ℝ)^16 := by norm_num
      calc
        _ ≤ ((4 / 3 : ℝ)^16)^(n/16) := pow_le_pow_left₀ (by norm_num) hbase _
        _ = (4 / 3 : ℝ)^(16 * (n/16)) := by rw [pow_mul]
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
    exact hh.trans (small_longest_degree p hn hL)
  · have hd := defect_add_longest p
    have hk : n / 16 ≤ defect p := by omega
    have hm : 2 * (n / 16) ≤ longest (ofPartition p) := by omega
    exact_mod_cast (pow_le_choose_of_mul_le 2 _ _ hm).trans
      (choose_longest_le_degree p _ hk (by omega))

lemma defect_card_bound (n u : ℕ) :
    Fintype.card {p : NShape n // defect p = u} ≤ 2 ^ (u + 1) := by
  have hh : Nat.card {p : Nat.Partition n // n - longest (ofPartition p) = u} ≤ 2 ^ (u+1) := by
    rw [← Fintype.card_eq_nat_card]
    calc
      _ ≤ 2 * Fintype.card (Nat.Partition u) := defect_count_le n u
      _ ≤ 2 * 2^u := Nat.mul_le_mul_left 2 (partition_count_le_pow u)
      _ = _ := by ring
  rw [Fintype.card_eq_nat_card]
  change Nat.card {p : Nat.Partition (Fintype.card (Fin n)) // n - longest (ofPartition p) = u} ≤ _
  have he (m k : ℕ) (h : m = k) :
      Nat.card {p : Nat.Partition m // n - longest (ofPartition p) = u} =
      Nat.card {p : Nat.Partition k // n - longest (ofPartition p) = u} := by subst k; rfl
  exact (he _ _ (Fintype.card_fin n)).trans_le hh

end Thorp.Specht

end

end OAI
