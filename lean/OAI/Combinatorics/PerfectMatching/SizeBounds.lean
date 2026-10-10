import OAI.Combinatorics.PerfectMatching.ElementaryCount

namespace OAI

section

namespace BinaryMatching.Algorithm
noncomputable section
open Finset

def inputLength (G : Input) : ℕ := (encodeInput G).length

lemma encodeNat_length (n : ℕ) : (encodeNat n).length=2*n.bits.length+1 := by
  simp [encodeNat]; omega

lemma encodeRecord_length (r : Record) :
    (encodeRecord r).length=2*(r.left.bits.length+r.right.bits.length+r.multiplicity.bits.length)+3 := by
  simp only [encodeRecord,List.length_append,encodeNat_length]
  omega

lemma records_length_le_input (G : Input) : G.records.length≤ inputLength G := by
  have hh (rs : List Record) : rs.length≤(rs.flatMap encodeRecord).length := by
    induction rs with
    | nil => simp
    | cons r rs ih =>
      simp only [List.length_cons,List.flatMap_cons,List.length_append,encodeRecord_length]
      omega
  have := hh G.records
  simp only [inputLength,encodeInput,List.length_append]
  omega

lemma record_bits_le_input (G : Input) (r : Record) (hr : r∈G.records) :
    r.multiplicity.bits.length≤ inputLength G := by
  have hh : (encodeRecord r).length≤(G.records.flatMap encodeRecord).length := by
    rw [List.length_flatMap]
    exact List.le_sum_of_mem (List.mem_map.mpr ⟨r,hr,rfl⟩)
  rw [encodeRecord_length] at hh
  unfold inputLength encodeInput
  simp only [List.length_append]
  omega

lemma log2_le_bits (m : ℕ) : Nat.log2 m≤ m.bits.length := by
  by_cases hm : m=0
  · subst m; simp
  · rw [Nat.size_eq_bits_len]
    exact (Nat.lt_size.mpr (Nat.log2_self_le hm)).le

lemma B_le_input (G : Input) : B G≤ inputLength G := by
  apply foldl_max_le _ _ _ (Nat.zero_le _)
  intro b hb
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hb
  exact (log2_le_bits r.multiplicity).trans (record_bits_le_input G r hr)

lemma covered_card_le_records (G : Input) : (covered G).card≤2*G.records.length := by
  have hh := List.toFinset_card_le
    ((G.records.filter (fun e => 0< e.multiplicity)).flatMap (fun e => [e.left,e.right]))
  have hlen : ((G.records.filter (fun e => 0< e.multiplicity)).flatMap (fun e => [e.left,e.right])).length=
      2*(G.records.filter (fun e => 0< e.multiplicity)).length := by
    rw [List.length_flatMap]
    simp
    omega
  rw [hlen] at hh
  exact hh.trans (Nat.mul_le_mul_left 2 (List.length_filter_le _ _))

lemma positive_count_order_bound (G : Input) (hN : 0< count G) : G.n≤2*inputLength G := by
  exact (positive_count_covered G hN).trans
    ((covered_card_le_records G).trans (Nat.mul_le_mul_left _ (records_length_le_input G)))

lemma multiplicity_pow_bound (G : Input) (e : Pair G.n) : multiplicity G e≤2^(B G+1) := by
  apply (Nat.lt_log2_self (n := multiplicity G e)).le.trans
  exact Nat.pow_le_pow_right (by norm_num) (by have := multiplicity_log_le_B G e; omega)

lemma count_pow_bound (G : Input) : count G≤2^((B G+2)*q G.n) := by
  have hM (M : (completeGraph G.n).Matching) : multProduct G M≤2^((B G+1)*q G.n) := by
    calc
      _ ≤ ∏ _e∈M.val,2^(B G+1) := prod_le_prod (fun e _ => multiplicity_pow_bound G e)
      _ = (2^(B G+1))^M.val.card := by simp
      _ ≤ (2^(B G+1))^(q G.n) :=
        Nat.pow_le_pow_right (by positivity) (card_le_univ M.val)
      _ = _ := by rw [pow_mul]
  calc
    _ ≤ ∑ _M : (completeGraph G.n).Matching,2^((B G+1)*q G.n) := sum_le_sum fun M _ => hM M
    _ = Fintype.card (completeGraph G.n).Matching*2^((B G+1)*q G.n) := by simp
    _ ≤ 2^(q G.n)*2^((B G+1)*q G.n) := Nat.mul_le_mul_right _ (matching_card_bound G.n)
    _ = _ := by rw [←pow_add]; congr 1; ring

lemma approximate_bits_bound (G : Input) :
    (approximate G).bits.length≤4*(inputLength G)^2*(inputLength G+2)+1 := by
  by_cases hN : count G=0
  · have ha := (approximate_correct G).2.2.mpr hN
    simp [ha]
  · have hNpos : 0< count G := Nat.pos_of_ne_zero hN
    have hn := positive_count_order_bound G hNpos
    have hb := B_le_input G
    have hq : q G.n≤4*(inputLength G)^2 := by
      apply (q_le_square (n := G.n)).trans
      calc
        G.n^2≤(2*inputLength G)^2 := Nat.pow_le_pow_left hn 2
        _ = _ := by ring
    have hExp : (B G+2)*q G.n≤4*(inputLength G)^2*(inputLength G+2) := by
      have := Nat.mul_le_mul (Nat.add_le_add_right hb 2) hq
      nlinarith
    rw [Nat.size_eq_bits_len]
    apply (Nat.size_le_size (approximate_correct G).1).trans
    apply (Nat.size_le_size (count_pow_bound G)).trans
    rw [Nat.size_pow]
    omega

theorem approximate_polynomial_output :
    ∃ P : Polynomial ℕ,∀ G,(approximate G).bits.length≤ P.eval (encodeInput G).length := by
  refine ⟨Polynomial.C 4*Polynomial.X^2*(Polynomial.X+Polynomial.C 2)+Polynomial.C 1,?_⟩
  intro G
  simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,
    Polynomial.eval_C,inputLength] using approximate_bits_bound G

end
end BinaryMatching.Algorithm
end

end OAI
