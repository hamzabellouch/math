import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

namespace PeriodicTilingThree

noncomputable section

attribute [local instance] Classical.propDecidable

def wordExceptionalCells (N : ℕ) (bad : ℤ → ℤ → ℤ → Prop) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-1 : ℤ) 1).biUnion fun d =>
    (Finset.Ico (-(N : ℤ)) (2 * (N : ℤ))).biUnion fun e =>
      ((Finset.Ico (0 : ℤ) N).filter (bad d e)).image fun n => (n, d * n + e)

theorem card_wordExceptionalCells_le (N p : ℕ) (bad : ℤ → ℤ → ℤ → Prop)
    (hbad : ∀ d e : ℤ, (d = -1 ∨ d = 0 ∨ d = 1) →
      ((Finset.Ico (0 : ℤ) N).filter (bad d e)).card ≤ p) :
    (wordExceptionalCells N bad).card ≤ 9 * N * p := by
  have hE : (Finset.Ico (-(N : ℤ)) (2 * (N : ℤ))).card = 3 * N := by
    rw [Int.card_Ico]
    omega
  have hD : (Finset.Icc (-1 : ℤ) 1).card = 3 := by
    norm_num [Int.card_Icc]
  have hinner : ∀ d ∈ Finset.Icc (-1 : ℤ) 1,
      ((Finset.Ico (-(N : ℤ)) (2 * (N : ℤ))).biUnion fun e =>
        ((Finset.Ico (0 : ℤ) N).filter (bad d e)).image
          fun n => (n, d * n + e)).card ≤ 3 * N * p := by
    intro d hd
    have hd' : d = -1 ∨ d = 0 ∨ d = 1 := by
      have hd'' := Finset.mem_Icc.mp hd
      omega
    calc
      _ ≤ (Finset.Ico (-(N : ℤ)) (2 * (N : ℤ))).card * p := by
        apply Finset.card_biUnion_le_card_mul
        intro e _he
        exact Finset.card_image_le.trans (hbad d e hd')
      _ = 3 * N * p := by rw [hE]
  calc
    (wordExceptionalCells N bad).card ≤
        (Finset.Icc (-1 : ℤ) 1).card * (3 * N * p) :=
      Finset.card_biUnion_le_card_mul _ _ _ hinner
    _ = 9 * N * p := by rw [hD]; ring

theorem mem_wordExceptionalCells (N : ℕ) (bad : ℤ → ℤ → ℤ → Prop)
    (n m d : ℤ) (hn0 : 0 ≤ n) (hnN : n < N)
    (hm0 : 0 ≤ m) (hmN : m < N)
    (hd : d = -1 ∨ d = 0 ∨ d = 1) (hb : bad d (m - d * n) n) :
    (n, m) ∈ wordExceptionalCells N bad := by
  have hdmem : d ∈ Finset.Icc (-1 : ℤ) 1 := by
    rcases hd with rfl | rfl | rfl <;> simp
  have hemem : m - d * n ∈ Finset.Ico (-(N : ℤ)) (2 * (N : ℤ)) := by
    apply Finset.mem_Ico.mpr
    rcases hd with rfl | rfl | rfl <;>
      simp only [neg_one_mul, zero_mul, one_mul, sub_zero] <;> constructor <;> omega
  apply Finset.mem_biUnion.mpr
  refine ⟨d, hdmem, Finset.mem_biUnion.mpr ⟨m - d * n, hemem, ?_⟩⟩
  apply Finset.mem_image.mpr
  refine ⟨n, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hn0, hnN⟩, hb⟩, ?_⟩
  exact Prod.ext rfl (by omega)

def wordBlockedOrigins (B : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  B.biUnion fun c =>
    ((Finset.Icc (0 : ℤ) 3).product (Finset.Icc (0 : ℤ) 3)).image
      fun o => (c.1 - o.1, c.2 - o.2)

theorem card_wordBlockedOrigins_le (B : Finset (ℤ × ℤ)) :
    (wordBlockedOrigins B).card ≤ B.card * 16 := by
  apply Finset.card_biUnion_le_card_mul
  intro c _hc
  calc
    _ ≤ ((Finset.Icc (0 : ℤ) 3).product (Finset.Icc (0 : ℤ) 3)).card :=
      Finset.card_image_le
    _ = 16 := by norm_num [Finset.card_product, Int.card_Icc]

theorem mem_wordBlockedOrigins (B : Finset (ℤ × ℤ)) (r q : ℤ)
    (i j : Fin 4) (hc : (r + i.val, q + j.val) ∈ B) :
    (r, q) ∈ wordBlockedOrigins B := by
  apply Finset.mem_biUnion.mpr
  refine ⟨(r + i.val, q + j.val), hc, Finset.mem_image.mpr ?_⟩
  refine ⟨((i.val : ℤ), (j.val : ℤ)), ?_, ?_⟩
  · apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_Icc.mpr <;> constructor <;> omega
  · apply Prod.ext <;> simp

private theorem four_square_count_inequality (p : ℕ) (hp : 200 < p) :
    144 * (p ^ 2) * p < (p ^ 2 - 3) ^ 2 := by
  have hp0 : 0 < p := by omega
  have hp201 : 201 ≤ p := by omega
  have hpred : p - 1 + 1 = p := by omega
  have hpredsq := congrArg (fun k : ℕ => k * k) hpred
  have hpredmul := congrArg (fun k : ℕ => p * k) hpred
  have hsq : 3 ≤ p ^ 2 := by nlinarith
  have hsub : p ^ 2 - 3 + 3 = p ^ 2 := Nat.sub_add_cancel hsq
  have hmul : 201 * p ≤ p * p := by nlinarith [Nat.mul_le_mul_right p hp201]
  have hgap : 144 * p < (p - 1) * (p - 1) := by nlinarith
  have hsmall : p * (p - 1) ≤ p ^ 2 - 3 := by nlinarith
  have hlarge := Nat.mul_lt_mul_of_pos_left hgap (pow_pos hp0 2)
  have hbound := Nat.mul_le_mul hsmall hsmall
  nlinarith

theorem exists_clean_four_square (p : ℕ) (hp : 200 < p)
    (bad : ℤ → ℤ → ℤ → Prop)
    (hbad : ∀ d e : ℤ, (d = -1 ∨ d = 0 ∨ d = 1) →
      ((Finset.Ico (0 : ℤ) (p ^ 2 : ℕ)).filter (bad d e)).card ≤ p) :
    ∃ r q : ℤ, 0 ≤ r ∧ r + 3 < (p ^ 2 : ℕ) ∧
      0 ≤ q ∧ q + 3 < (p ^ 2 : ℕ) ∧
      ∀ i j : Fin 4, ∀ d : ℤ, (d = -1 ∨ d = 0 ∨ d = 1) →
        ¬ bad d ((q + j.val) - d * (r + i.val)) (r + i.val) := by
  let N : ℕ := p ^ 2
  have hN : 3 ≤ N := by dsimp [N]; nlinarith
  let C : Finset (ℤ × ℤ) :=
    (Finset.Ico (0 : ℤ) (N - 3 : ℕ)).product
      (Finset.Ico (0 : ℤ) (N - 3 : ℕ))
  let B := wordBlockedOrigins (wordExceptionalCells N bad)
  have hC : C.card = (N - 3) ^ 2 := by
    simp [C, Finset.card_product, Int.card_Ico, pow_two]
  have hB : B.card ≤ 144 * N * p := by
    calc
      B.card ≤ (wordExceptionalCells N bad).card * 16 :=
        card_wordBlockedOrigins_le _
      _ ≤ (9 * N * p) * 16 :=
        Nat.mul_le_mul_right 16 (card_wordExceptionalCells_le N p bad hbad)
      _ = 144 * N * p := by ring
  have hlt : B.card < C.card := by
    rw [hC]
    exact hB.trans_lt (four_square_count_inequality p hp)
  obtain ⟨⟨r, q⟩, hc, hnblocked⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨hr, hq⟩ := Finset.mem_product.mp hc
  have hr' := Finset.mem_Ico.mp hr
  have hq' := Finset.mem_Ico.mp hq
  have hr0 : 0 ≤ r := hr'.1
  have hq0 : 0 ≤ q := hq'.1
  have hr3 : r + 3 < (N : ℤ) := by omega
  have hq3 : q + 3 < (N : ℤ) := by omega
  refine ⟨r, q, hr0, hr3, hq0, hq3, ?_⟩
  intro i j d hd hb
  apply hnblocked
  apply mem_wordBlockedOrigins _ r q i j
  apply mem_wordExceptionalCells N bad (r + i.val) (q + j.val) d
  · omega
  · omega
  · omega
  · omega
  · exact hd
  · exact hb

end

end PeriodicTilingThree

end OAI
