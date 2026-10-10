import OAI.Probability.SignedSweeps.ProvedRanges2

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

lemma spechtDimension_positive {n : ℕ} (lam : Partition n) : (0 : ℝ) < spechtDimension lam := by
  exact_mod_cast spechtDimension_pos lam

lemma spechtDimension_factorial_lower {n : ℕ} (lam : Partition n) :
    (n.factorial : ℝ) ≤ (spechtDimension lam : ℝ) *
      ((∏ i : Fin (lam.1.colLen 0), (lam.1.rowLen i).factorial : ℕ) : ℝ) *
      ((∏ j : Fin (lam.1.rowLen 0), (lam.1.colLen j).factorial : ℕ) : ℝ) := by
  have hb := spechtDimension_row_column_lower lam
  rw [card_rowSubgroup, card_colSubgroup] at hb
  calc
    _ ≤ _ := hb
    _ = _ := by ring

theorem specht_log_dimension_small_axes {n : ℕ} (lam : Partition n) (hn : 0 < n) :
    (n : ℝ) / 2 - 2 * ((lam.1.rowLen 0 : ℝ) + lam.1.colLen 0) ≤
      Real.log (spechtDimension lam : ℝ) := by
  have hD := spechtDimension_positive lam
  have hdim := Real.log_le_log (by positivity : (0 : ℝ) < n.factorial)
    (spechtDimension_factorial_lower lam)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul
    (spechtDimension_positive lam).ne' (by positivity), Nat.cast_prod, Nat.cast_prod,
    Real.log_prod (by intros; positivity), Real.log_prod (by intros; positivity)] at hdim
  have hrow := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (lam.1.colLen 0))))
    (fun i _ => log_factorial_upper (lam.rowLen_pos i))
  have hcol := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (lam.1.rowLen 0))))
    (fun j _ => log_factorial_upper (lam.colLen_pos j))
  have hrlog := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (lam.1.colLen 0))))
    (fun i _ => log_le_quarter_add_one (x := (lam.1.rowLen i : ℝ)) (by exact_mod_cast lam.rowLen_pos i))
  have hclog := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (lam.1.rowLen 0))))
    (fun j _ => log_le_quarter_add_one (x := (lam.1.colLen j : ℝ)) (by exact_mod_cast lam.colLen_pos j))
  have hrowsum : (∑ i : Fin (lam.1.colLen 0), (lam.1.rowLen i : ℝ)) = n := by
    exact_mod_cast lam.sum_rowLen
  have hcolsum : (∑ j : Fin (lam.1.rowLen 0), (lam.1.colLen j : ℝ)) = n := by
    exact_mod_cast lam.sum_colLen
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, hrowsum,
    hcolsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    at hrow hcol hrlog hclog
  linarith [row_column_entropy_sum_le lam hn, log_factorial_lower n]

lemma Partition.firstRow_pos {n : ℕ} (lam : Partition n) (hn : 0 < n) :
    0 < lam.1.rowLen 0 :=
  lt_of_le_of_lt (Nat.zero_le _) (lam.colOf_lt ⟨0, hn⟩)

lemma Partition.firstCol_pos {n : ℕ} (lam : Partition n) (hn : 0 < n) :
    0 < lam.1.colLen 0 :=
  lt_of_le_of_lt (Nat.zero_le _) (lam.rowOf_lt ⟨0, hn⟩)

lemma Partition.firstRow_le {n : ℕ} (lam : Partition n) (hn : 0 < n) :
    lam.1.rowLen 0 ≤ n := by
  let i : Fin (lam.1.colLen 0) := ⟨0, lam.firstCol_pos hn⟩
  calc
    _ ≤ ∑ j : Fin (lam.1.colLen 0), lam.1.rowLen j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = _ := lam.sum_rowLen

lemma factorial_product_remove_first_row {n : ℕ} (lam : Partition n) (hn : 0 < n) :
    (∏ i : Fin (lam.1.colLen 0), (lam.1.rowLen i).factorial) *
      (∏ j : Fin (lam.1.rowLen 0), (lam.1.colLen j).factorial) ≤
      (lam.1.rowLen 0).factorial * (n - lam.1.rowLen 0).factorial *
        ∏ j : Fin (lam.1.rowLen 0), lam.1.colLen j := by
  let i₀ : Fin (lam.1.colLen 0) := ⟨0, lam.firstCol_pos hn⟩
  have hfull : ∀ j : Fin (lam.1.rowLen 0), ∃ x, lam.rowIndex x = i₀ ∧ lam.colIndex x = j := by
    intro j
    refine ⟨lam.tableau ⟨(0,j), YoungDiagram.mem_iff_lt_rowLen.mpr j.isLt⟩, ?_, ?_⟩
    · apply Fin.ext; simp [Partition.rowIndex, Partition.rowOf, i₀]
    · apply Fin.ext; simp [Partition.colIndex, Partition.colOf]
  have hopen : Fintype.card {x : Fin n // lam.rowIndex x ≠ i₀} = n - lam.1.rowLen 0 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, rowIndex_fiber_card]
  have hb := factorial_product_remove_full_row lam.rowIndex lam.colIndex i₀
    lam.rowColIndex_injective hfull
  have hrn (i : Fin (lam.1.colLen 0)) : Nat.card {x : Fin n // lam.rowIndex x = i} =
      lam.1.rowLen i := Nat.card_eq_fintype_card.trans (rowIndex_fiber_card lam i)
  have hcn (j : Fin (lam.1.rowLen 0)) : Nat.card {x : Fin n // lam.colIndex x = j} =
      lam.1.colLen j := Nat.card_eq_fintype_card.trans (colIndex_fiber_card lam j)
  have hopen' : Nat.card {x : Fin n // lam.rowIndex x ≠ i₀} = n - lam.1.rowLen 0 :=
    Nat.card_eq_fintype_card.trans hopen
  simpa only [← Nat.card_eq_fintype_card, hrn, hcn, hopen'] using hb

lemma column_log_sum_le {n : ℕ} (lam : Partition n) (hn : 0 < n) :
    (∑ j : Fin (lam.1.rowLen 0), Real.log (lam.1.colLen j : ℝ)) ≤
      (lam.1.rowLen 0 : ℝ) * Real.log ((n : ℝ) / lam.1.rowLen 0) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hA : (0 : ℝ) < lam.1.rowLen 0 := by exact_mod_cast lam.firstRow_pos hn
  have hp (j : Fin (lam.1.rowLen 0)) : (0 : ℝ) < lam.1.colLen j := by
    exact_mod_cast lam.colLen_pos j
  have hb := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (lam.1.rowLen 0))))
    (fun j _ => Real.log_le_sub_one_of_pos (div_pos (hp j) (div_pos hn' hA)))
  simp_rw [Real.log_div (hp _).ne' (div_pos hn' hA).ne'] at hb
  simp only [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, ← Nat.cast_sum, lam.sum_colLen] at hb
  have he : (n : ℝ) / (n / lam.1.rowLen 0) = lam.1.rowLen 0 := by field_simp
  rw [he] at hb
  linarith

lemma log_degree_from_first_row {n : ℕ} (lam : Partition n) (hn : 0 < n)
    {D : ℝ} (hD : 0 < D) (hk : 0 < n - lam.1.rowLen 0)
    (hbound : (n.factorial : ℝ) ≤ D *
      ((∏ i : Fin (lam.1.colLen 0), (lam.1.rowLen i).factorial : ℕ) : ℝ) *
      ((∏ j : Fin (lam.1.rowLen 0), (lam.1.colLen j).factorial : ℕ) : ℝ)) :
    ((n - lam.1.rowLen 0 : ℕ) : ℝ) * Real.log ((n : ℝ) / (n - lam.1.rowLen 0 : ℕ)) -
      Real.log (lam.1.rowLen 0 : ℝ) - Real.log ((n - lam.1.rowLen 0 : ℕ) : ℝ) - 2 ≤
        Real.log D := by
  have hnat := factorial_product_remove_first_row lam hn
  have hreal : (((∏ i : Fin (lam.1.colLen 0), (lam.1.rowLen i).factorial : ℕ) : ℝ) *
      ((∏ j : Fin (lam.1.rowLen 0), (lam.1.colLen j).factorial : ℕ) : ℝ)) ≤
      ((lam.1.rowLen 0).factorial : ℝ) * ((n - lam.1.rowLen 0).factorial : ℝ) *
        ((∏ j : Fin (lam.1.rowLen 0), lam.1.colLen j : ℕ) : ℝ) := by exact_mod_cast hnat
  have htot : (n.factorial : ℝ) ≤ D * (((lam.1.rowLen 0).factorial : ℝ) *
      ((n - lam.1.rowLen 0).factorial : ℝ) *
        ((∏ j : Fin (lam.1.rowLen 0), lam.1.colLen j : ℕ) : ℝ)) :=
    hbound.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hreal hD.le)
  have hP : (0 : ℝ) < ((∏ j : Fin (lam.1.rowLen 0), lam.1.colLen j : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun j _ => lam.colLen_pos j)
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < n.factorial) htot
  rw [Real.log_mul hD.ne' (by positivity), Real.log_mul (by positivity) hP.ne',
    Real.log_mul (by positivity) (by positivity), Nat.cast_prod,
    Real.log_prod (by intro j _; exact_mod_cast (lam.colLen_pos j).ne')] at hlog
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hA : (0 : ℝ) < lam.1.rowLen 0 := by exact_mod_cast lam.firstRow_pos hn
  have hK : (0 : ℝ) < (n - lam.1.rowLen 0 : ℕ) := by exact_mod_cast hk
  have hsum : (n : ℝ) = (lam.1.rowLen 0 : ℝ) + (n - lam.1.rowLen 0 : ℕ) := by
    rw [Nat.cast_sub (lam.firstRow_le hn)]; ring
  have hc := column_log_sum_le lam hn
  rw [Real.log_div hN.ne' hA.ne'] at hc
  rw [Real.log_div hN.ne' hK.ne']
  have hsplit := congrArg (fun x : ℝ => x * Real.log n) hsum
  nlinarith [log_factorial_upper (lam.firstRow_pos hn), log_factorial_upper hk,
    log_factorial_lower n]

lemma Partition.firstCol_le {n : ℕ} (lam : Partition n) (hn : 0 < n) :
    lam.1.colLen 0 ≤ n := by
  simpa only [Partition.transpose, YoungDiagram.rowLen_transpose] using
    lam.transpose.firstRow_le hn

lemma deficit_log_ratio_lower {N A K : ℝ} (hN : 0 < N) (hK : 0 < K)
    (hsum : N = A + K) (hlong : N ≤ 100 * A) :
    (1 : ℝ) / 100 ≤ Real.log (N / K) := by
  have hp : 0 < K / N := div_pos hK hN
  have hb := Real.log_le_sub_one_of_pos hp
  rw [Real.log_div hK.ne' hN.ne'] at hb
  rw [Real.log_div hN.ne' hK.ne']
  have hratio : K / N ≤ 99 / 100 := (div_le_iff₀ hN).mpr (by linarith)
  linarith

lemma log_degree_long_first_row {n : ℕ} (lam : Partition n) (hn : 0 < n)
    {D : ℝ} (hD : 0 < D) (hk : 0 < n - lam.1.rowLen 0)
    (hlong : n ≤ 100 * lam.1.rowLen 0)
    (hbound : (n.factorial : ℝ) ≤ D *
      ((∏ i : Fin (lam.1.colLen 0), (lam.1.rowLen i).factorial : ℕ) : ℝ) *
      ((∏ j : Fin (lam.1.rowLen 0), (lam.1.colLen j).factorial : ℕ) : ℝ)) :
    ((n - lam.1.rowLen 0 : ℕ) : ℝ) / 100 - 2 * Real.log n - 2 ≤ Real.log D := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : (0 : ℝ) < (n - lam.1.rowLen 0 : ℕ) := by exact_mod_cast hk
  have hsum : (n : ℝ) = (lam.1.rowLen 0 : ℝ) + (n - lam.1.rowLen 0 : ℕ) := by
    rw [Nat.cast_sub (lam.firstRow_le hn)]; ring
  have hlong' : (n : ℝ) ≤ 100 * (lam.1.rowLen 0 : ℝ) := by exact_mod_cast hlong
  have hlog := deficit_log_ratio_lower hN hK hsum hlong'
  have hprod := mul_le_mul_of_nonneg_left hlog hK.le
  have hAlog : Real.log (lam.1.rowLen 0 : ℝ) ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast lam.firstRow_pos hn)
      (by exact_mod_cast lam.firstRow_le hn)
  have hKlog : Real.log ((n - lam.1.rowLen 0 : ℕ) : ℝ) ≤ Real.log n :=
    Real.log_le_log hK (by exact_mod_cast Nat.sub_le n (lam.1.rowLen 0))
  linarith [log_degree_from_first_row lam hn hD hk hbound]

theorem specht_log_dimension_deficit {n : ℕ} (lam : Partition n) (hn : 0 < n)
    (hcol : lam.1.colLen 0 ≤ n / 2) :
    ((n - lam.1.rowLen 0 : ℕ) : ℝ) / 200 - 2 * Real.log n - 2 ≤
      Real.log (spechtDimension lam : ℝ) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hkn : ((n - lam.1.rowLen 0 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast Nat.sub_le n (lam.1.rowLen 0)
  have hk0 : (0 : ℝ) ≤ (n - lam.1.rowLen 0 : ℕ) := by positivity
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlogD : 0 ≤ Real.log (spechtDimension lam : ℝ) :=
    Real.log_nonneg (by exact_mod_cast spechtDimension_pos lam)
  by_cases hk : n - lam.1.rowLen 0 = 0
  · simp only [hk, Nat.cast_zero, zero_div, zero_sub]
    linarith
  have hkp : 0 < n - lam.1.rowLen 0 := Nat.pos_of_ne_zero hk
  by_cases hrow : n ≤ 100 * lam.1.rowLen 0
  · have hb := log_degree_long_first_row lam hn (spechtDimension_positive lam) hkp
      hrow (spechtDimension_factorial_lower lam)
    linarith
  by_cases hcolumn : n ≤ 100 * lam.1.colLen 0
  · have hB : 2 * lam.1.colLen 0 ≤ n := by omega
    have hB' : 2 * (lam.1.colLen 0 : ℝ) ≤ n := by exact_mod_cast hB
    have hk' : 0 < n - lam.1.colLen 0 := by omega
    have hfact : (n.factorial : ℝ) ≤ (spechtDimension lam : ℝ) *
        ((∏ i : Fin (lam.transpose.1.colLen 0), (lam.transpose.1.rowLen i).factorial : ℕ) : ℝ) *
        ((∏ j : Fin (lam.transpose.1.rowLen 0), (lam.transpose.1.colLen j).factorial : ℕ) : ℝ) := by
      have hb := spechtDimension_factorial_lower lam
      rw [Fin.prod_univ_eq_prod_range (fun i => (lam.1.rowLen i).factorial),
        Fin.prod_univ_eq_prod_range (fun i => (lam.1.colLen i).factorial)] at hb
      rw [Fin.prod_univ_eq_prod_range (fun i => (lam.transpose.1.rowLen i).factorial),
        Fin.prod_univ_eq_prod_range (fun i => (lam.transpose.1.colLen i).factorial)]
      simpa only [Partition.transpose, YoungDiagram.colLen_transpose,
        YoungDiagram.rowLen_transpose, mul_assoc, mul_left_comm, mul_comm] using hb
    have hs := log_degree_long_first_row lam.transpose hn (spechtDimension_positive lam)
      (by simpa only [Partition.transpose, YoungDiagram.rowLen_transpose] using hk')
      (by simpa only [Partition.transpose, YoungDiagram.rowLen_transpose] using hcolumn) hfact
    simp only [Partition.transpose, YoungDiagram.rowLen_transpose] at hs
    rw [Nat.cast_sub (lam.firstCol_le hn)] at hs
    linarith
  · have hA : 100 * (lam.1.rowLen 0 : ℝ) < n := by exact_mod_cast Nat.lt_of_not_ge hrow
    have hB : 100 * (lam.1.colLen 0 : ℝ) < n := by exact_mod_cast Nat.lt_of_not_ge hcolumn
    linarith [specht_log_dimension_small_axes lam hn]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical
open Filter
open scoped Topology

lemma nonsparse_degree_error {δ : ℝ} (hδ : δ < 1) :
    ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d ≥ d₀,
      2 * Real.log ((2 ^ d : ℕ) : ℝ) + 2 ≤
        (((2 ^ d : ℕ) : ℝ) ^ (1 - δ)) / 400 := by
  let b := (1 - δ) * Real.log 2
  have hb : 0 < b := mul_pos (by linarith) (Real.log_pos (by norm_num))
  have hlin := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 b hb).comp
    tendsto_natCast_atTop_atTop).const_mul (2 * Real.log 2)
  have hconst := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 b hb).comp
    tendsto_natCast_atTop_atTop).const_mul 2
  have ht : Tendsto (fun d : ℕ => (2 * (d : ℝ) * Real.log 2 + 2) *
      Real.exp (-b * d)) atTop (𝓝 0) := by
    convert hlin.add hconst using 1
    · funext d
      simp only [Function.comp_apply, Real.rpow_one, Real.rpow_zero, one_mul]
      ring
    · simp
  obtain ⟨D, hD⟩ := eventually_atTop.mp
    (ht.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 400))
  refine ⟨max D 2, le_max_right _ _, ?_⟩
  intro d hd
  have hs := mul_le_mul_of_nonneg_right (hD d ((le_max_left _ _).trans hd))
    (Real.exp_nonneg (b * d))
  have he : Real.exp (-b * d) * Real.exp (b * d) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [mul_assoc, he, mul_one] at hs
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (2 ^ d : ℕ)), nat_two_pow_log]
  have hp : (d : ℝ) * Real.log 2 * (1 - δ) = b * d := by dsimp [b]; ring
  rw [hp]
  linarith

theorem nonsparse_specht_log_dimension {δ : ℝ} (hδ : δ < 1) :
    ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d ≥ d₀, ∀ lam : Partition (2 ^ d),
      lam.1.colLen 0 ≤ 2 ^ d / 2 →
      ((2 ^ d : ℕ) : ℝ) ^ (1 - δ) ≤ ((2 ^ d - lam.1.rowLen 0 : ℕ) : ℝ) →
      (((2 ^ d : ℕ) : ℝ) ^ (1 - δ)) / 400 ≤ Real.log (spechtDimension lam : ℝ) := by
  obtain ⟨d₀, hd₀, herr⟩ := nonsparse_degree_error hδ
  refine ⟨d₀, hd₀, ?_⟩
  intro d hd lam hcol hk
  linarith [herr d hd, specht_log_dimension_deficit lam (by positivity) hcol]

theorem nonsparse_signed_entropy_size {δ : ℝ} (hδ : δ < 1) :
    ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∀ d ≥ d₀, ∀ lam : Partition (2 ^ d),
      lam.1.colLen 0 ≤ 2 ^ d / 2 →
      ((2 ^ d : ℕ) : ℝ) ^ (1 - δ) ≤ ((2 ^ d - lam.1.rowLen 0 : ℕ) : ℝ) →
      ∀ (u v l : ℕ) (h : u + v + l = 2 ^ d)
        (α : Partition u) (β : Partition v) (γ : Partition l),
        SignedOccurrence h α β γ lam →
        (((2 ^ d : ℕ) : ℝ) ^ (1 - δ)) / 800 ≤
          signedEntropy α β + (l : ℝ) * Real.log ((2 ^ d : ℕ) : ℝ) := by
  obtain ⟨d₀, hd₀, hh⟩ := nonsparse_specht_log_dimension hδ
  refine ⟨d₀, hd₀, ?_⟩
  intro d hd lam hcol hk u v l h α β γ ho
  have hdim := hh d hd lam hcol hk
  have hup := signedOccurrence_log_dimension (by positivity) ho
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd₀.trans hd
  have hlog : 1 ≤ Real.log ((2 ^ d : ℕ) : ℝ) := by
    rw [nat_two_pow_log]
    nlinarith [Real.log_two_gt_d9]
  have hl := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg l : (0 : ℝ) ≤ l)
  linarith [signedEntropy_nonneg α β]

theorem nonsparse_closing_budget {η κ C δ ξ : ℝ}
    (hη : 0 < η) (hκ : 0 < κ) (hC : 0 ≤ C) (hδ : δ < 1) (hδξ : δ < ξ) :
    ∃ d₀ : ℕ, 4 ≤ d₀ ∧ ∀ d ≥ d₀, ∀ lam : Partition (2 ^ d),
      lam.1.colLen 0 ≤ 2 ^ d / 2 →
      ((2 ^ d : ℕ) : ℝ) ^ (1 - δ) ≤ ((2 ^ d - lam.1.rowLen 0 : ℕ) : ℝ) →
      ∀ (u v l : ℕ) (h : u + v + l = 2 ^ d)
        (α : Partition u) (β : Partition v) (γ : Partition l),
        SignedOccurrence h α β γ lam →
        coefficient η (childDepth d) * signedEntropy α β +
          coefficient κ (childDepth d) * l * Real.log ((2 ^ d : ℕ) : ℝ) -
          (l : ℝ) * Real.log (((2 ^ d : ℕ) : ℝ) / l) +
          C * ((l : ℝ) + (((2 ^ d : ℕ) : ℝ) ^ (1 - ξ))) ≤
        coefficient η d * signedEntropy α β + remainderBudget κ d l := by
  obtain ⟨D, hD, hclose⟩ := scalar_induction_budget hη hκ
    (by norm_num : (0 : ℝ) < 1 / 800) hC hδξ
  obtain ⟨N, _, hsize⟩ := nonsparse_signed_entropy_size hδ
  refine ⟨max D N, hD.trans (le_max_left _ _), ?_⟩
  intro d hd lam hcol hk u v l h α β γ ho
  apply hclose d ((le_max_left _ _).trans hd) (signedEntropy α β)
    (signedEntropy_nonneg α β) l
  simpa only [one_div, ← div_eq_mul_inv, mul_comm] using
    hsize d ((le_max_right _ _).trans hd) lam hcol hk u v l h α β γ ho

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical
variable {Z C R 𝕜 : Type*} [Fintype Z] [Semiring 𝕜]
  {E : Z → Type*} [∀ z, Fintype (E z)]

def assignmentBlock (X : Matrix (Sigma E) (Sigma E) 𝕜) (z : Z) :
    Matrix (E z) (E z) 𝕜 := X.submatrix (Sigma.mk z) (Sigma.mk z)

lemma assignmentBlock_mul (col : Z → C) (row : Z → R)
    (hinj : Function.Injective (fun z => (col z, row z)))
    (X Y : Matrix (Sigma E) (Sigma E) 𝕜)
    (hX : ∀ i j, col i.1 ≠ col j.1 → X i j = 0)
    (hY : ∀ i j, row i.1 ≠ row j.1 → Y i j = 0) (z : Z) :
    assignmentBlock (X * Y) z = assignmentBlock X z * assignmentBlock Y z := by
  ext i j
  simp only [assignmentBlock, Matrix.submatrix_apply, Matrix.mul_apply,
    Fintype.sum_sigma]
  rw [Finset.sum_eq_single z]
  · intro w hw hwz
    apply Finset.sum_eq_zero
    intro e he
    by_cases hc : col z = col w
    · have hr : row w ≠ row z := by
        intro hr
        exact hwz (hinj (Prod.ext hc.symm hr))
      rw [hY ⟨w,e⟩ ⟨z,j⟩ hr, mul_zero]
    · rw [hX ⟨z,i⟩ ⟨w,e⟩ hc, zero_mul]
  · simp

lemma trace_blockDiagonal'_mul (P : ∀ z, Matrix (E z) (E z) 𝕜)
    (A : Matrix (Sigma E) (Sigma E) 𝕜) :
    Matrix.trace (Matrix.blockDiagonal' P * A) =
      ∑ z, Matrix.trace (P z * assignmentBlock A z) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single z]
  · apply Finset.sum_congr rfl
    intro j hj
    simp [Matrix.blockDiagonal', assignmentBlock]
  · intro w hw hwz
    apply Finset.sum_eq_zero
    intro j hj
    simp [Matrix.blockDiagonal', hwz.symm]
  · simp

theorem labeled_assignment_trace (col : Z → C) (row : Z → R)
    (hinj : Function.Injective (fun z => (col z, row z)))
    (P : ∀ z, Matrix (E z) (E z) 𝕜) (X Y : Matrix (Sigma E) (Sigma E) 𝕜)
    (hX : ∀ i j, col i.1 ≠ col j.1 → X i j = 0)
    (hY : ∀ i j, row i.1 ≠ row j.1 → Y i j = 0) :
    Matrix.trace (Matrix.blockDiagonal' P * X * Y) =
      ∑ z, Matrix.trace (P z * assignmentBlock X z * assignmentBlock Y z) := by
  rw [Matrix.mul_assoc, trace_blockDiagonal'_mul]
  apply Finset.sum_congr rfl
  intro z hz
  rw [assignmentBlock_mul col row hinj X Y hX hY, Matrix.mul_assoc]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

abbrev HoleAssignment (L A B : Type*) := L ↪ A × B

def holeColumns {L A B : Type*} (z : HoleAssignment L A B) : L → B :=
  fun k => (z k).2

def holeRows {L A B : Type*} (z : HoleAssignment L A B) : L → A :=
  fun k => (z k).1

lemma hole_rows_columns_injective {L A B : Type*} :
    Function.Injective (fun z : HoleAssignment L A B => (holeColumns z, holeRows z)) := by
  intro z w h
  apply Function.Embedding.ext
  intro k
  exact Prod.ext (congrFun (congrArg Prod.snd h) k) (congrFun (congrArg Prod.fst h) k)

theorem labeled_hole_trace {L A B 𝕜 : Type*} [Fintype (HoleAssignment L A B)]
    [Semiring 𝕜] {E : HoleAssignment L A B → Type*} [∀ z, Fintype (E z)]
    (P : ∀ z, Matrix (E z) (E z) 𝕜) (X Y : Matrix (Sigma E) (Sigma E) 𝕜)
    (hX : ∀ i j : Sigma E, holeColumns i.1 ≠ holeColumns j.1 → X i j = 0)
    (hY : ∀ i j : Sigma E, holeRows i.1 ≠ holeRows j.1 → Y i j = 0) :
    Matrix.trace (Matrix.blockDiagonal' P * X * Y) =
      ∑ z, Matrix.trace (P z * assignmentBlock X z * assignmentBlock Y z) :=
  labeled_assignment_trace (Z := HoleAssignment L A B) (E := E)
    holeColumns holeRows hole_rows_columns_injective P X Y hX hY

lemma nonnegative_prod_le_mean_power {I : Type*} (S : Finset I) (z : I → ℝ)
    (hz : ∀ i ∈ S, 0 ≤ z i) {M : ℝ} (hM : 0 ≤ M) (hsum : ∑ i ∈ S, z i ≤ M) :
    ∏ i ∈ S, z i ≤ (M / S.card) ^ S.card := by
  by_cases hS : S = ∅
  · subst S; simp
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
  by_cases hzero : ∃ i ∈ S, z i = 0
  · obtain ⟨i, hi, hz0⟩ := hzero
    rw [Finset.prod_eq_zero hi hz0]
    positivity
  have hp (i) (hi : i ∈ S) : 0 < z i :=
    lt_of_le_of_ne (hz i hi) (by intro h; exact hzero ⟨i,hi,h.symm⟩)
  have hsumpos : 0 < ∑ i ∈ S, z i := Finset.sum_pos (fun i hi => hp i hi)
    (Finset.nonempty_iff_ne_empty.mpr hS)
  have hMp : 0 < M := hsumpos.trans_le hsum
  have havg : 0 < M / S.card := div_pos hMp hcard
  have hl (i) (hi : i ∈ S) :
      Real.log (z i) - Real.log (M / S.card) ≤ z i / (M / S.card) - 1 := by
    simpa only [Real.log_div (hp i hi).ne' havg.ne'] using
      Real.log_le_sub_one_of_pos (div_pos (hp i hi) havg)
  have hall := Finset.sum_le_sum (fun i hi => hl i hi)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
    ← Finset.sum_div] at hall
  have hquot : (∑ i ∈ S, z i) / (M / S.card) ≤ S.card := by
    apply (div_le_iff₀ havg).mpr
    rwa [mul_div_cancel₀ _ (ne_of_gt hcard)]
  apply (Real.log_le_log_iff (Finset.prod_pos hp) (pow_pos havg S.card)).mp
  rw [Real.log_prod (fun i hi => (hp i hi).ne'), Real.log_pow]
  linarith

def missingLineFactor (m k : ℕ) : ℝ := ((m : ℝ) / k) ^ k

lemma missingLineFactor_nonneg (m k : ℕ) : 0 ≤ missingLineFactor m k := by
  unfold missingLineFactor
  positivity

@[simp] lemma missingLineFactor_empty (m : ℕ) : missingLineFactor m 0 = 1 := by
  simp [missingLineFactor]

lemma missingLineFactor_le_exp (m k : ℕ) (hk : k ≤ m) :
    missingLineFactor m k ≤ Real.exp (m - k : ℝ) := by
  by_cases he : k = 0
  · subst k
    simp only [missingLineFactor_empty, Nat.cast_zero, sub_zero]
    exact Real.one_le_exp (Nat.cast_nonneg m)
  have hkp : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero he
  have hmp : (0 : ℝ) < m := hkp.trans_le (by exact_mod_cast hk)
  have havg : 0 < (m : ℝ) / k := div_pos hmp hkp
  have hl := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos havg) hkp.le
  have hb : (k : ℝ) * Real.log ((m : ℝ) / k) ≤ m - k := by
    calc
      _ ≤ (k : ℝ) * ((m : ℝ) / k - 1) := hl
      _ = _ := by field_simp
  calc
    missingLineFactor m k = Real.exp ((k : ℝ) * Real.log ((m : ℝ) / k)) := by
      rw [Real.exp_nat_mul, Real.exp_log havg]; rfl
    _ ≤ _ := Real.exp_le_exp.mpr hb

def occupiedRow {A B : Type*} [Fintype B] (W : Finset (A × B)) (i : A) : Finset B :=
  Finset.univ.filter (fun j => (i,j) ∈ W)

def missingCellFactor {A B : Type*} [Fintype A] [Fintype B] (W : Finset (A × B)) : ℝ :=
  ∏ i, missingLineFactor (Fintype.card B) (occupiedRow W i).card

lemma sum_occupiedRow_card {A B : Type*} [Fintype A] [Fintype B] (W : Finset (A × B)) :
    ∑ i, (occupiedRow W i).card = W.card := by
  simp only [occupiedRow, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Fintype.sum_prod_type' (fun i a => if (i,a) ∈ W then (1 : ℕ) else 0)]
  simp [Finset.sum_ite_mem]

theorem occupied_cell_product_bound {A B : Type*} [Fintype A] [Fintype B]
    (W : Finset (A × B)) (z : A → B → ℝ) (hz : ∀ i j, 0 ≤ z i j)
    (hsum : ∀ i, ∑ j, z i j ≤ Fintype.card B) :
    ∏ c ∈ W, z c.1 c.2 ≤ missingCellFactor W := by
  have hprod : (∏ c ∈ W, z c.1 c.2) = ∏ i, ∏ j ∈ occupiedRow W i, z i j := by
    simp only [occupiedRow, Finset.prod_filter]
    rw [← Fintype.prod_prod_type' (fun i a => if (i,a) ∈ W then z i a else 1)]
    simp [Finset.prod_ite_mem]
  rw [hprod]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact Finset.prod_nonneg (fun j hj => hz i j)
  · intro i hi
    apply nonnegative_prod_le_mean_power _ _ (fun j _ => hz i j) (Nat.cast_nonneg _)
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => hz i j)).trans (hsum i)

end SignedSweeps
end

end OAI
