import OAI.Combinatorics.FiniteCircle.BinaryDistortion

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem get_encode_block {α : Type*} {w : ℕ} (c : α → Fin w → Bool)
    (x : List α) (i : Fin x.length) (r : Fin w) :
    (encode c x).get ⟨i.val * w + r.val, by
      rw [length_encode]
      nlinarith [i.isLt, r.isLt]⟩ = c (x.get i) r := by
  induction x with
  | nil => exact Fin.elim0 i
  | cons a x ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.val_zero, Nat.zero_mul, Nat.zero_add, encode_cons, List.get_eq_getElem,
        List.getElem_cons_zero]
      rw [List.getElem_append_left (by simp only [List.length_ofFn]; exact r.isLt), List.getElem_ofFn]
    · have hit : (j.val+1)*w+r.val < (List.ofFn (c a) ++ encode c x).length := by
        simp only [List.length_append, List.length_ofFn, length_encode]
        nlinarith [j.isLt, r.isLt]
      change (List.ofFn (c a) ++ encode c x)[(j.val+1)*w+r.val] = c (x.get j) r
      rw [List.getElem_append_right (by simp only [List.length_ofFn]; nlinarith)]
      convert ih j using 1
      simp only [List.length_ofFn, List.get_eq_getElem]
      congr 1
      simp [Nat.add_mul, Nat.add_comm, Nat.add_left_comm]

theorem get_encode {α : Type*} {w : ℕ} (hw : 0 < w) (c : α → Fin w → Bool)
    (x : List α) (k : Fin (encode c x).length) :
    (encode c x).get k = c (x.get ⟨k.val/w, by
      apply (Nat.div_lt_iff_lt_mul hw).mpr
      simpa only [length_encode, Nat.mul_comm] using k.isLt⟩)
      ⟨k.val%w, Nat.mod_lt _ hw⟩ := by
  have h := get_encode_block c x ⟨k.val/w, by
    apply (Nat.div_lt_iff_lt_mul hw).mpr
    simpa only [length_encode, Nat.mul_comm] using k.isLt⟩ ⟨k.val%w, Nat.mod_lt _ hw⟩
  convert h using 1
  congr 1
  apply Fin.ext
  simpa only [Nat.mul_comm] using (Nat.div_add_mod k.val w).symm

theorem indexSpan_ofFn {w n : ℕ} (f : Fin n → Fin w) (hn : 0 < n) :
    indexSpan (List.ofFn f) = (f ⟨n-1, by omega⟩).val + 1 - (f ⟨0, hn⟩).val := by
  cases n with
  | zero => omega
  | succ n =>
    have he : List.ofFn f ≠ [] := by simp
    have hl := List.getLast_ofFn (f := f) he
    simp only [List.ofFn_succ, List.getLast_eq_getLastD] at hl
    simp only [List.ofFn_succ, indexSpan]
    rw [hl]
    rfl

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

def localIndices (A : WordMatching x y q) {w : ℕ} (hw : 0 < w)
    (S : Finset (Fin q)) : List (Fin w) :=
  List.ofFn (fun k : Fin S.card =>
    ⟨(A.left (S.orderEmbOfFin rfl k)).val % w, Nat.mod_lt _ hw⟩)

@[simp] theorem localIndices_length (A : WordMatching x y q) {w : ℕ} (hw : 0 < w)
    (S : Finset (Fin q)) : (A.localIndices hw S).length = S.card := List.length_ofFn

theorem mod_strictMono_on_block (A : WordMatching x y q) {w i : ℕ}
    {k l : Fin q} (hk : k ∈ A.sourceBlock w i) (hl : l ∈ A.sourceBlock w i)
    (hkl : k < l) : (A.left k).val % w < (A.left l).val % w := by
  have hm : (A.left k).val < (A.left l).val := A.left.strictMono hkl
  have h1 := Nat.mod_add_div (A.left k).val w
  have h2 := Nat.mod_add_div (A.left l).val w
  rw [(A.mem_sourceBlock w i k).mp hk] at h1
  rw [(A.mem_sourceBlock w i l).mp hl] at h2
  omega

theorem localIndices_sorted (A : WordMatching x y q) {w i : ℕ} (hw : 0 < w)
    {S : Finset (Fin q)} (hS : S ⊆ A.sourceBlock w i) :
    (A.localIndices hw S).Pairwise (fun i j => i.val < j.val) := by
  apply List.pairwise_ofFn.mpr
  intro k l hkl
  exact A.mod_strictMono_on_block (hS (S.orderEmbOfFin_mem rfl k))
    (hS (S.orderEmbOfFin_mem rfl l)) ((S.orderEmbOfFin rfl).strictMono hkl)

theorem localIndices_span (A : WordMatching x y q) {w i : ℕ} (hw : 0 < w)
    {S : Finset (Fin q)} (hS : S ⊆ A.sourceBlock w i) :
    indexSpan (A.localIndices hw S) = (A.symm.rightSpan S).card := by
  by_cases h : S.Nonempty
  · have hc : 0 < S.card := Finset.card_pos.mpr h
    rw [localIndices, indexSpan_ofFn _ hc, A.symm.rightSpan_eq_Icc h, Fin.card_Icc]
    dsimp only
    rw [Finset.orderEmbOfFin_last rfl hc, Finset.orderEmbOfFin_zero rfl hc]
    simp only [symm]
    have h1 := Nat.mod_add_div (A.left (S.min' h)).val w
    have h2 := Nat.mod_add_div (A.left (S.max' h)).val w
    rw [(A.mem_sourceBlock w i _).mp (hS (S.min'_mem h))] at h1
    rw [(A.mem_sourceBlock w i _).mp (hS (S.max'_mem h))] at h2
    omega
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hl : A.localIndices hw S = [] := List.length_eq_zero_iff.mp (by simp [he])
    rw [hl]
    simp [indexSpan, he, rightSpan]

def blockPair (A : WordMatching x y q) (w i j : ℕ) : Finset (Fin q) :=
  A.sourceBlock w i ∩ A.symm.sourceBlock w j

theorem blockPair_convex (A : WordMatching x y q) (w i j : ℕ) :
    ConvexIndices (A.blockPair w i j) := by
  intro k hk l hl v hkv hvl
  exact Finset.mem_inter.mpr
    ⟨A.sourceBlock_convex w i k (Finset.mem_inter.mp hk).1 l (Finset.mem_inter.mp hl).1 v hkv hvl,
     A.symm.sourceBlock_convex w j k (Finset.mem_inter.mp hk).2 l (Finset.mem_inter.mp hl).2 v hkv hvl⟩

def targetBlocks (A : WordMatching x y q) (w : ℕ) (S : Finset (Fin q)) : Finset ℕ :=
  S.image (fun k => (A.right k).val / w)

theorem targetBlocks_card_le_three (A : WordMatching x y q) {w : ℕ} (hw : 0 < w)
    {S : Finset (Fin q)} (hspan : (A.rightSpan S).card ≤ 2*w) :
    (A.targetBlocks w S).card ≤ 3 := by
  by_cases h : S.Nonempty
  · let lo := (A.right (S.min' h)).val
    let hi := (A.right (S.max' h)).val
    have hle : lo ≤ hi := A.right.monotone (S.min'_le _ (S.max'_mem h))
    have hspan' : hi + 1 - lo ≤ 2*w := by
      simpa only [A.rightSpan_eq_Icc h, Fin.card_Icc] using hspan
    have hdiv : hi/w ≤ lo/w+2 := by
      have hlo := Nat.mod_add_div lo w
      have hhi := Nat.mod_add_div hi w
      have hm := Nat.mod_lt lo hw
      by_contra hh
      have hh : lo/w+3 ≤ hi/w := by omega
      have hh' := Nat.mul_le_mul_left w hh
      have hs : hi+1 ≤ lo+2*w := by omega
      have hh2 : w*(lo/w)+3*w ≤ hi := calc
        _ = w*(lo/w+3) := by ring
        _ ≤ w*(hi/w) := hh'
        _ ≤ hi := Nat.mul_div_le hi w
      have hlo2 : lo < w*(lo/w)+w := by omega
      omega
    have hs : A.targetBlocks w S ⊆ Finset.Icc (lo/w) (lo/w+2) := by
      intro j hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      have hklo : lo ≤ (A.right k).val := A.right.monotone (S.min'_le _ hk)
      have hkhi : (A.right k).val ≤ hi := A.right.monotone (S.le_max' _ hk)
      exact Finset.mem_Icc.mpr ⟨Nat.div_le_div_right hklo, (Nat.div_le_div_right hkhi).trans hdiv⟩
    have hc := Finset.card_le_card hs
    rw [Nat.card_Icc] at hc
    omega
  · simp [targetBlocks, Finset.not_nonempty_iff_eq_empty.mp h]

theorem sum_blockPair_card (A : WordMatching x y q) (w i : ℕ) :
    ∑ j ∈ A.targetBlocks w (A.sourceBlock w i), (A.blockPair w i j).card =
      (A.sourceBlock w i).card := by
  have hpair (j : ℕ) : A.blockPair w i j = (A.sourceBlock w i).filter (fun k => (A.right k).val / w = j) := by
    ext k
    simp [blockPair, mem_sourceBlock, symm]
  simp_rw [hpair]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  apply Finset.filter_true_of_mem
  intro k hk
  exact Finset.mem_image_of_mem _ hk

theorem exists_large_blockPair (A : WordMatching x y q) {w i : ℕ} (hw : 0 < w)
    (hspan : (A.rightSpan (A.sourceBlock w i)).card ≤ 2*w)
    (hcard : 3*w < 4*(A.sourceBlock w i).card) :
    ∃ j ∈ A.targetBlocks w (A.sourceBlock w i), w ≤ 4*(A.blockPair w i j).card := by
  by_contra hh
  push Not at hh
  have hs := Finset.sum_le_sum (fun j hj => (hh j hj).le)
  rw [← Finset.mul_sum, A.sum_blockPair_card, Finset.sum_const, smul_eq_mul] at hs
  have ht := A.targetBlocks_card_le_three hw hspan
  have hmul := Nat.mul_le_mul_right w ht
  omega

end WordMatching

end FiniteCircle

end OAI
