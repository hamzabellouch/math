import OAI.Analysis.MarkovType.NormCompression
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

private theorem prefixBlocks_prefixCut_add (x y : C00) (k : ℕ) :
    prefixCut (x + y) k = prefixCut x k + prefixCut y k := by
  simp only [prefixCut, Finsupp.add_apply, Finset.sum_add_distrib]

private theorem prefixBlocks_prefixCut_smul (a : ℝ) (x : C00) (k : ℕ) :
    prefixCut (a • x) k = a * prefixCut x k := by
  simp only [prefixCut, Finsupp.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem sum_Ico_eq_prefixCut_sub (x : C00) (a b : ℕ) (hab : a ≤ b) :
    (∑ i ∈ Finset.Ico a b, x i) = prefixCut x b - prefixCut x a := by
  exact Finset.sum_Ico_eq_sub (fun i => x i) hab

@[simp] theorem prefixCut_single (i : ℕ) (a : ℝ) (k : ℕ) :
    prefixCut (Finsupp.single i a) k = if i < k then a else 0 := by
  classical
  unfold prefixCut
  by_cases hi : i < k
  · rw [ite_eq_left hi, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      exact Finsupp.single_eq_of_ne hji
    · simp [Finset.mem_range, hi]
  · rw [ite_eq_right hi]
    apply Finset.sum_eq_zero
    intro j hj
    apply Finsupp.single_eq_of_ne
    have hjk := Finset.mem_range.mp hj
    omega

def blockIndex {r : ℕ} (c : Fin (r + 1) → ℕ) (i : ℕ) : ℕ :=
  (Finset.univ.filter fun j : Fin r => c j.succ ≤ i).card

theorem blockIndex_monotone {r : ℕ} (c : Fin (r + 1) → ℕ) :
    Monotone (blockIndex c) := by
  classical
  intro i k hik
  apply Finset.card_le_card
  intro j hj
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.trans hik⟩

theorem lt_blockIndex_iff {r : ℕ} (c : Fin (r + 1) → ℕ)
    (hc : Monotone c) (j : Fin r) (i : ℕ) :
    j.val < blockIndex c i ↔ c j.succ ≤ i := by
  classical
  constructor
  · intro hj
    by_contra hn
    have hsub : (Finset.univ.filter fun k : Fin r => c k.succ ≤ i) ⊆
        Finset.Iio j := by
      intro k hk
      have hki := (Finset.mem_filter.mp hk).2
      apply Finset.mem_Iio.mpr
      by_contra hkj
      have hjk : j.succ ≤ k.succ := by
        change j.val + 1 ≤ k.val + 1
        have : j ≤ k := le_of_not_gt hkj
        exact Nat.add_le_add_right this 1
      have := hc hjk
      omega
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    change blockIndex c i ≤ j.val at hcard
    omega
  · intro hj
    have hsub : Finset.Iic j ⊆
        (Finset.univ.filter fun k : Fin r => c k.succ ≤ i) := by
      intro k hk
      have hkj := Finset.mem_Iic.mp hk
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, le_trans (hc ?_) hj⟩
      change k.val + 1 ≤ j.val + 1
      exact Nat.add_le_add_right hkj 1
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    change j.val + 1 ≤ blockIndex c i at hcard
    omega

theorem blockIndex_lt_iff {r : ℕ} (c : Fin (r + 1) → ℕ)
    (hc : Monotone c) (h0 : c 0 = 0) (j : Fin (r + 1)) (i : ℕ) :
    blockIndex c i < j.val ↔ i < c j := by
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [h0]
  · have h := lt_blockIndex_iff c hc k i
    change blockIndex c i < k.val + 1 ↔ i < c k.succ
    omega

theorem blockIndex_eq_iff {r : ℕ} (c : Fin (r + 1) → ℕ)
    (hc : Monotone c) (h0 : c 0 = 0) (j : Fin r) (i : ℕ) :
    blockIndex c i = j.val ↔ c j.castSucc ≤ i ∧ i < c j.succ := by
  have hlo := blockIndex_lt_iff c hc h0 j.castSucc i
  have hhi := blockIndex_lt_iff c hc h0 j.succ i
  change blockIndex c i < j.val ↔ i < c j.castSucc at hlo
  change blockIndex c i < j.val + 1 ↔ i < c j.succ at hhi
  omega

namespace C00

theorem ofArray_apply_ge {r : ℕ} (a : Fin r → ℝ) (k : ℕ) (hk : r ≤ k) :
    ofArray a k = 0 := by
  classical
  simp only [ofArray, place, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro j _
  apply Finsupp.single_eq_of_ne
  have := j.isLt
  omega

end C00

def prefixBlockCoeffs {r : ℕ} (c : Fin (r + 1) → ℕ) :
    C00 →ₗ[ℝ] (Fin r → ℝ) where
  toFun x j := prefixCut x (c j.succ) - prefixCut x (c j.castSucc)
  map_add' x y := by
    funext j
    simp only [prefixBlocks_prefixCut_add, Pi.add_apply]
    ring
  map_smul' a x := by
    funext j
    simp only [prefixBlocks_prefixCut_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def prefixBlocksLinear {r : ℕ} (c : Fin (r + 1) → ℕ) : C00 →ₗ[ℝ] C00 :=
  (C00.arrayLinear r).comp (prefixBlockCoeffs c)

@[simp] theorem prefixBlocksLinear_apply {r : ℕ} (c : Fin (r + 1) → ℕ) (x : C00) :
    prefixBlocksLinear c x =
      C00.ofArray (fun j : Fin r => prefixCut x (c j.succ) -
        prefixCut x (c j.castSucc)) := rfl

theorem prefixBlocksLinear_single {r : ℕ} (c : Fin (r + 1) → ℕ)
    (hc : Monotone c) (h0 : c 0 = 0) (i : ℕ) (hi : i < c (Fin.last r)) (a : ℝ) :
    prefixBlocksLinear c (Finsupp.single i a) =
      Finsupp.single (blockIndex c i) a := by
  classical
  have hblock : blockIndex c i < r :=
    (blockIndex_lt_iff c hc h0 (Fin.last r) i).mpr hi
  ext k
  rw [prefixBlocksLinear_apply]
  by_cases hk : k < r
  · let j : Fin r := ⟨k, hk⟩
    change C00.ofArray
        (fun j : Fin r => prefixCut (Finsupp.single i a) (c j.succ) -
          prefixCut (Finsupp.single i a) (c j.castSucc)) j.val =
        Finsupp.single (blockIndex c i) a j.val
    rw [C00.ofArray_apply]
    simp only [prefixCut_single, Finsupp.single_apply]
    have hle : c j.castSucc ≤ c j.succ := hc (by
      change j.val ≤ j.val + 1
      omega)
    have hfiber := blockIndex_eq_iff c hc h0 j i
    by_cases hlo : i < c j.castSucc
    · have hhi : i < c j.succ := lt_of_lt_of_le hlo hle
      have hne : blockIndex c i ≠ j.val := by omega
      simp [hlo, hhi, hne]
    · by_cases hhi : i < c j.succ
      · have heq : blockIndex c i = j.val := hfiber.mpr ⟨by omega, hhi⟩
        simp [hlo, hhi, heq]
      · have hne : blockIndex c i ≠ j.val := by omega
        simp [hlo, hhi, hne]
  · rw [C00.ofArray_apply_ge _ k (Nat.le_of_not_gt hk)]
    symm
    apply Finsupp.single_eq_of_ne
    omega

theorem prefixBlocks_eq_mapDomain {r : ℕ} (c : Fin (r + 1) → ℕ)
    (hc : Monotone c) (h0 : c 0 = 0) (x : C00)
    (hx : C00.SupportedBelow x (c (Fin.last r))) :
    C00.ofArray (fun j : Fin r => prefixCut x (c j.succ) -
      prefixCut x (c j.castSucc)) = Finsupp.mapDomain (blockIndex c) x := by
  classical
  have hrepr := C00.ofArray_restrict x (c (Fin.last r)) hx
  change prefixBlocksLinear c x = Finsupp.mapDomain (blockIndex c) x
  calc
    prefixBlocksLinear c x = prefixBlocksLinear c
        (C00.ofArray (fun i : Fin (c (Fin.last r)) => x i.val)) :=
      congrArg (prefixBlocksLinear c) hrepr.symm
    _ = ∑ i : Fin (c (Fin.last r)),
        prefixBlocksLinear c (Finsupp.single i.val (x i.val)) := by
      simp only [C00.ofArray, C00.place, map_sum]
    _ = ∑ i : Fin (c (Fin.last r)),
        Finsupp.single (blockIndex c i.val) (x i.val) := by
      apply Finset.sum_congr rfl
      intro i _
      exact prefixBlocksLinear_single c hc h0 i.val i.isLt (x i.val)
    _ = Finsupp.mapDomain (blockIndex c)
        (C00.ofArray (fun i : Fin (c (Fin.last r)) => x i.val)) := by
      rw [C00.mapDomain_ofArray]
      rfl
    _ = Finsupp.mapDomain (blockIndex c) x :=
      congrArg (Finsupp.mapDomain (blockIndex c)) hrepr

namespace OrderedNorm

theorem prefixBlocks_le (N : OrderedNorm) {r : ℕ} (c : Fin (r + 1) → ℕ)
    (hc : Monotone c) (h0 : c 0 = 0) (x : C00)
    (hx : C00.SupportedBelow x (c (Fin.last r))) :
    N (C00.ofArray (fun j : Fin r => prefixCut x (c j.succ) -
      prefixCut x (c j.castSucc))) ≤ N x := by
  rw [prefixBlocks_eq_mapDomain c hc h0 x hx]
  exact N.mapDomain_le (blockIndex c) (blockIndex_monotone c) x

theorem prefixBlocks_le_of_last_eq (N : OrderedNorm) {r B : ℕ}
    (c : Fin (r + 1) → ℕ) (hc : Monotone c) (h0 : c 0 = 0)
    (hB : c (Fin.last r) = B) (x : C00) (hx : C00.SupportedBelow x B) :
    N (C00.ofArray (fun j : Fin r => prefixCut x (c j.succ) -
      prefixCut x (c j.castSucc))) ≤ N x := by
  apply N.prefixBlocks_le c hc h0 x
  simpa only [hB] using hx

theorem consecutiveBlocks_le (N : OrderedNorm) {r : ℕ} (c : Fin (r + 1) → ℕ)
    (hc : Monotone c) (h0 : c 0 = 0) (x : C00)
    (hx : C00.SupportedBelow x (c (Fin.last r))) :
    N (C00.ofArray (fun j : Fin r =>
      ∑ i ∈ Finset.Ico (c j.castSucc) (c j.succ), x i)) ≤ N x := by
  have hcoeff : (fun j : Fin r =>
      ∑ i ∈ Finset.Ico (c j.castSucc) (c j.succ), x i) =
      (fun j : Fin r => prefixCut x (c j.succ) - prefixCut x (c j.castSucc)) := by
    funext j
    exact sum_Ico_eq_prefixCut_sub x _ _ (hc (by
      change j.val ≤ j.val + 1
      omega))
  rw [hcoeff]
  exact N.prefixBlocks_le c hc h0 x hx

end OrderedNorm

end MarkovSuperreflexivity

end

end OAI
