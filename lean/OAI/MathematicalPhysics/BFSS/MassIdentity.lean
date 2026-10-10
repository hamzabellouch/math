import Mathlib
import OAI.MathematicalPhysics.BFSS.GammaIdentity

namespace OAI

/-! Weighted mass-spin identities and rotation generators. -/

namespace BFSSGamma
noncomputable section
open Matrix Finset
variable (G : Space → Mat)
variable (hG : ∀ i j, G i * G j + G j * G i = (if i = j then 2 else 0) • (1 : Mat))
include hG
variable (hSym : ∀ i, (G i).transpose = G i)
include hSym
def firstThree : Finset Space := {0, 1, 2}
def massWeight (i : Space) : ℝ := if i < 3 then 2 else -1
def massT : Mat := G 0 * G 1 * G 2
def skew (A : Mat) : Mat := (1 / 2 : ℝ) • (A - A.transpose)
def massC (v : Spin → ℝ) : Mat := ∑ i, massWeight i •
  skew (Matrix.vecMulVec (G i *ᵥ v) ((G i * massT G) *ᵥ v))
def massR (v : Spin → ℝ) (i j : Space) : ℝ :=
  massWeight j * dotProduct v ((G i * G j * massT G) *ᵥ v)
def rotationSpin (R : Space → Space → ℝ) : Mat :=
  (1/4 : ℝ) • ∑ i, ∑ j, R i j • (G i * G j)

def MassSpinIdentity : Prop := ∀ (v : Spin → ℝ), (∑ α, v α ^ 2) = 1 →
  massC G v = (-3/4 : ℝ) • massT G - (1/2 : ℝ) • rotationSpin G (massR G v)

omit hG hSym in
lemma firstThree_sort : firstThree.sort (· ≤ ·) = [0,1,2] := by
  rw [firstThree, Finset.sort_insert (· ≤ ·) (by simp) (by decide),
    Finset.sort_insert (· ≤ ·) (by simp) (by decide)]
  simp
omit hG hSym in
lemma firstThree_card : firstThree.card = 3 := by decide
omit hG hSym in
lemma mem_firstThree (i : Space) : i ∈ firstThree ↔ i < 3 := by
  simp only [firstThree, Finset.mem_insert, Finset.mem_singleton]
  change (i = 0 ∨ i = 1 ∨ i = 2) ↔ i.val < 3
  simp only [Fin.ext_iff]
  omega
omit hG hSym in
lemma massWeight_sum : ∑ i : Space, massWeight i = 0 := by
  norm_num [massWeight, Fin.sum_univ_succ, Fin.lt_def]
omit hG hSym in
lemma word_firstThree : word G firstThree = massT G := by
  simp only [word, firstThree_sort, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, massT, Matrix.mul_assoc]

lemma massT_transpose : (massT G).transpose = -massT G := by
  rw [← word_firstThree, word_transpose G hG hSym, firstThree_card]
  norm_num [rankSign, Nat.choose]

omit hSym in
lemma massT_sq (_hSym : ∀ index, (G index).transpose = G index) :
    massT G * massT G = -(1 : Mat) := by
  have h := reverseWord_mul_word G hG firstThree
  have hr : reverseWord G firstThree = -massT G := by
    rw [reverseWord, list_reverse_eq G hG _ (Finset.sort_nodup _ _), Finset.length_sort,
      firstThree_card]
    change rankSign 3 • word G firstThree = _
    rw [word_firstThree]
    norm_num [rankSign, Nat.choose]
  rw [hr, word_firstThree, neg_mul] at h
  exact neg_eq_iff_eq_neg.mp h

omit hSym in
lemma gamma_massT_conj (i : Space) :
    G i * massT G * G i = (if i < 3 then (1 : ℝ) else -1) • massT G := by
  rw [← word_firstThree, word_conj G hG, wordSign_eq, firstThree_card]
  simp only [mem_firstThree]
  split_ifs <;> norm_num

omit hSym in
lemma gamma_massT_comm (i : Space) :
    G i * massT G = (if i < 3 then (1 : ℝ) else -1) • (massT G * G i) := by
  have h := congrArg (fun X : Mat => G i * X) (gamma_massT_conj G hG i)
  simp only [← Matrix.mul_assoc, gamma_sq G hG, one_mul, mul_smul_comm] at h
  split_ifs at h ⊢ <;> simp only [one_smul, neg_smul, one_smul] at h ⊢
  · exact h.symm
  · simpa only [neg_neg] using (congrArg Neg.neg h).symm

omit hG hSym in
lemma skew_transpose (A : Mat) : (skew A).transpose = -skew A := by
  simp only [skew, Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_transpose]
  module

omit hG hSym in
lemma massC_skew (v : Spin → ℝ) : (massC G v).transpose = -massC G v := by
  simp only [massC, Matrix.transpose_sum, Matrix.transpose_smul, skew_transpose,
    smul_neg, Finset.sum_neg_distrib]

omit hG hSym in
lemma trace_skew_outer (M : Mat) (hM : M.transpose = -M) (x y : Spin → ℝ) :
    Matrix.trace (M * skew (Matrix.vecMulVec x y)) = dotProduct y (M *ᵥ x) := by
  rw [skew, mul_smul_comm, mul_sub, Matrix.trace_smul, Matrix.trace_sub]
  have ht := Matrix.trace_transpose_mul M (Matrix.vecMulVec x y)
  rw [hM, neg_mul, Matrix.trace_neg] at ht
  rw [trace_mul_outer] at ht ⊢
  simp only [smul_eq_mul]
  linarith

omit hSym in
lemma weighted_word_conj (s : Finset Space) :
    ∑ i, massWeight i • (G i * word G s * G i) =
      (-2 * (-1 : ℝ)^s.card * (∑ i ∈ s, massWeight i)) • word G s := by
  simp_rw [word_conj G hG, smul_smul, wordSign_eq]
  rw [← Finset.sum_smul]
  congr 1
  calc
    _ = ∑ i : Space, ((-1 : ℝ)^s.card * massWeight i -
           2 * (-1 : ℝ)^s.card * (if i ∈ s then massWeight i else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, massWeight_sum, mul_zero,
        ← Finset.mul_sum]
      simp only [Finset.sum_ite_mem, Finset.univ_inter, zero_sub]
      ring

lemma mass_trace_word (s : Finset Space) (hs : (word G s).transpose = -word G s)
    (v : Spin → ℝ) :
    Matrix.trace ((word G s).transpose * massC G v) =
      (-2 * (-1 : ℝ)^s.card * (∑ i ∈ s, massWeight i)) *
        dotProduct v ((word G s * massT G) *ᵥ v) := by
  have hterm (i : Space) :
      Matrix.trace ((word G s).transpose *
        skew (Matrix.vecMulVec (G i *ᵥ v) ((G i * massT G) *ᵥ v))) =
        -dotProduct v ((massT G * G i * (word G s).transpose * G i) *ᵥ v) := by
    have ht : ((word G s).transpose).transpose = -(word G s).transpose := by
      rw [Matrix.transpose_transpose, hs, neg_neg]
    rw [trace_skew_outer _ ht, dot_mulVec_left, Matrix.transpose_mul, massT_transpose G hG hSym,
      hSym, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    simp only [neg_mul, Matrix.neg_mulVec, dotProduct_neg]
  rw [massC, Matrix.mul_sum, Matrix.trace_sum]
  simp_rw [mul_smul_comm, Matrix.trace_smul, hterm, smul_eq_mul]
  have hcs := weighted_word_conj G hG s
  have hs' : (∑ i, massWeight i • (G i * (word G s).transpose * G i)) =
      (-2 * (-1 : ℝ)^s.card * (∑ i ∈ s, massWeight i)) • (word G s).transpose := by
    simpa only [hs, mul_neg, neg_mul, smul_neg, Finset.sum_neg_distrib] using
      congrArg Neg.neg hcs
  have hd : dotProduct v ((massT G * (word G s).transpose) *ᵥ v) =
      - dotProduct v ((word G s * massT G) *ᵥ v) := by
    have h := dot_transpose (word G s * massT G) v
    simpa only [Matrix.transpose_mul, massT_transpose G hG hSym, neg_mul,
      Matrix.neg_mulVec, dotProduct_neg, neg_neg] using congrArg Neg.neg h
  calc
    _ = -dotProduct v ((massT G *
      (∑ i, massWeight i • (G i * (word G s).transpose * G i))) *ᵥ v) := by
      simp only [Matrix.mul_sum, mul_smul_comm, Matrix.sum_mulVec, Matrix.smul_mulVec,
        dotProduct_sum, dotProduct_smul, smul_eq_mul, mul_neg, Finset.sum_neg_distrib,
        ← Matrix.mul_assoc]
    _ = _ := by
      rw [hs', mul_smul_comm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hd]
      ring

omit hG hSym in
lemma word_pair (i j : Space) (hij : i < j) : word G {i,j} = G i * G j := by
  rw [word, Finset.sort_insert (· ≤ ·) (by simpa using hij.le) (by simpa using hij.ne)]
  simp

lemma word_trace_dual (s t : Finset Space) (hs : s.card ≤ 4) (ht : t.card ≤ 4) :
    Matrix.trace ((word G s).transpose * word G t) = if s = t then 16 else 0 := by
  have h := trace_reverseWord_word G hG hs ht
  have hr : (word G s).transpose = reverseWord G s := by
    exact list_transpose G hSym _
  rwa [hr]

omit hG hSym in
lemma mass_stats (s : Finset Space) :
    (s.filter (fun i => i < 3)).card + (s.filter (fun i => ¬ i < 3)).card = s.card := by
  exact Finset.card_filter_add_card_filter_not _

omit hG hSym in
lemma mass_weight_stats (s : Finset Space) :
    (∑ i ∈ s, massWeight i) = 2 * ((s.filter (fun i => i < 3)).card : ℝ) -
      ((s.filter (fun i => ¬ i < 3)).card : ℝ) := by
  simp only [massWeight, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]
  ring

omit hG hSym in
lemma mass_sign_stats (s : Finset Space) :
    (∏ i ∈ s, if i < 3 then (1 : ℝ) else -1) =
      (-1 : ℝ) ^ (s.filter (fun i => ¬ i < 3)).card := by
  rw [Finset.prod_ite]
  simp

omit hSym in
lemma massT_gamma_comm (i : Space) :
    massT G * G i = (if i < 3 then (1 : ℝ) else -1) • (G i * massT G) := by
  have h := gamma_massT_comm G hG i
  split_ifs at h ⊢ <;> simp only [one_smul, neg_smul, one_smul] at h ⊢
  · exact h.symm
  · simpa only [neg_neg] using (congrArg Neg.neg h).symm

omit hSym in
lemma massT_list_comm (l : List Space) :
    massT G * (l.map G).prod =
      (l.map (fun i => if i < 3 then (1 : ℝ) else -1)).prod •
        ((l.map G).prod * massT G) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [← Matrix.mul_assoc, massT_gamma_comm G hG, smul_mul_assoc,
      Matrix.mul_assoc, ih, mul_smul_comm, smul_smul]
    simp only [Matrix.mul_assoc]

omit hSym in
lemma massT_word_comm (s : Finset Space) :
    massT G * word G s =
      ((-1 : ℝ) ^ (s.filter (fun i => ¬ i < 3)).card) • (word G s * massT G) := by
  have h := massT_list_comm G hG (s.sort (· ≤ ·))
  rw [← List.prod_toFinset _ (Finset.sort_nodup _ _)] at h
  simpa only [Finset.sort_toFinset, word, mass_sign_stats] using h

lemma word_massT_transpose (s : Finset Space) (hs : (word G s).transpose = -word G s) :
    (word G s * massT G).transpose =
      ((-1 : ℝ) ^ (s.filter (fun i => ¬ i < 3)).card) • (word G s * massT G) := by
  rw [Matrix.transpose_mul, massT_transpose G hG hSym, hs, neg_mul_neg,
    massT_word_comm G hG]

omit hG hSym in
lemma thirdWord_no_outside (s : Finset Space) (hs : s.card = 3)
    (ho : (s.filter (fun i => ¬ i < 3)).card = 0) : s = firstThree := by
  apply Finset.eq_of_subset_of_card_le _ (by rw [firstThree_card, hs])
  intro i hi
  rw [mem_firstThree]
  by_contra hn
  have hm : i ∈ s.filter (fun i => ¬ i < 3) := Finset.mem_filter.mpr ⟨hi, hn⟩
  have hz := Finset.card_eq_zero.mp ho
  rw [hz] at hm
  exact Finset.notMem_empty i hm

lemma thirdWord_mass_pair (s : Finset Space) (hs : s.card = 3)
    (v : Spin → ℝ) (hv : ∑ α, v α ^ 2 = 1) :
    Matrix.trace ((word G s).transpose * massC G v) =
      if s = firstThree then -12 else 0 := by
  have hsk : (word G s).transpose = -word G s := by
    rw [word_transpose G hG hSym, hs]
    norm_num [rankSign, Nat.choose]
  rw [mass_trace_word G hG hSym _ hsk]
  have hsum := mass_weight_stats s
  have hstats := mass_stats s
  have hout : (s.filter (fun i => ¬ i < 3)).card ≤ 3 := by omega
  have ht := word_massT_transpose G hG hSym s hsk
  generalize ho : (s.filter (fun i => ¬ i < 3)).card = o at *
  interval_cases o
  · have heq := thirdWord_no_outside s hs ho
    rw [heq, word_firstThree, massT_sq G hG hSym, Matrix.neg_mulVec,
      Matrix.one_mulVec, dotProduct_neg]
    have hv' : dotProduct v v = 1 := by simpa only [dotProduct, pow_two] using hv
    rw [hv']
    have hi : (s.filter (fun i => i < 3)).card = 3 := by omega
    rw [hi] at hsum
    norm_num at hsum
    rw [← heq, hsum, hs]
    norm_num
  · have hz := dot_skew_zero (word G s * massT G) (by norm_num at ht ⊢; exact ht) v
    have heq : s ≠ firstThree := by
      intro h
      rw [h] at ho
      have hh : (firstThree.filter (fun i => ¬ i < 3)) = ∅ := by
        ext i; simp [mem_firstThree]
      simp only [hh, Finset.card_empty] at ho
      omega
    rw [hz, ite_eq_right heq, mul_zero]
  · have hi : (s.filter (fun i => i < 3)).card = 1 := by omega
    rw [hi] at hsum
    norm_num at hsum
    rw [hsum]
    have heq : s ≠ firstThree := by
      intro h
      rw [h] at ho
      have hh : (firstThree.filter (fun i => ¬ i < 3)) = ∅ := by
        ext i; simp [mem_firstThree]
      simp only [hh, Finset.card_empty] at ho
      omega
    rw [ite_eq_right heq]
    ring
  · have hz := dot_skew_zero (word G s * massT G) (by norm_num at ht ⊢; exact ht) v
    have heq : s ≠ firstThree := by
      intro h
      rw [h] at ho
      have hh : (firstThree.filter (fun i => ¬ i < 3)) = ∅ := by
        ext i; simp [mem_firstThree]
      simp only [hh, Finset.card_empty] at ho
      omega
    rw [hz, ite_eq_right heq, mul_zero]

lemma gamma_pair_mass_transpose (i j : Space) (hij : i ≠ j) :
    (G i * G j * massT G).transpose =
      ((if i < 3 then (1 : ℝ) else -1) * (if j < 3 then (1 : ℝ) else -1)) •
        (G i * G j * massT G) := by
  have hsk : (G i * G j).transpose = -(G i * G j) := by
    rw [Matrix.transpose_mul, hSym, hSym, gamma_anti G hG (Ne.symm hij)]
  rw [Matrix.transpose_mul, massT_transpose G hG hSym, hsk, neg_mul_neg,
    ← Matrix.mul_assoc, massT_gamma_comm G hG, smul_mul_assoc, Matrix.mul_assoc,
    massT_gamma_comm G hG, mul_smul_comm, smul_smul]
  simp only [Matrix.mul_assoc]

lemma mass_pair_weight_cancel (v : Spin → ℝ) (i j : Space) :
    (massWeight i - massWeight j) * dotProduct v ((G i * G j * massT G) *ᵥ v) = 0 := by
  by_cases hi : i < 3 <;> by_cases hj : j < 3
  · simp [massWeight, hi, hj]
  · have hij : i ≠ j := by rintro rfl; contradiction
    have ht := gamma_pair_mass_transpose G hG hSym i j hij
    have hz := dot_skew_zero (G i * G j * massT G) (by
        simpa only [ite_eq_left hi, ite_eq_right hj, one_mul, neg_smul, one_smul] using ht) v
    rw [hz, mul_zero]
  · have hij : i ≠ j := by rintro rfl; contradiction
    have ht := gamma_pair_mass_transpose G hG hSym i j hij
    have hz := dot_skew_zero (G i * G j * massT G) (by
        simpa only [ite_eq_right hi, ite_eq_left hj, mul_one, neg_smul, one_smul] using ht) v
    rw [hz, mul_zero]
  · simp [massWeight, hi, hj]

lemma massR_diag (v : Spin → ℝ) (i : Space) : massR G v i i = 0 := by
  rw [massR, gamma_sq G hG, one_mul, dot_skew_zero _ (massT_transpose G hG hSym), mul_zero]

lemma massR_skew (v : Spin → ℝ) (i j : Space) : massR G v j i = -massR G v i j := by
  by_cases hij : i = j
  · subst j; rw [massR_diag G hG hSym]; simp
  · have hji := gamma_anti G hG (Ne.symm hij)
    have hw := mass_pair_weight_cancel G hG hSym v i j
    simp only [massR, hji, neg_mul, Matrix.neg_mulVec, dotProduct_neg]
    nlinarith

omit hG in
lemma rotationSpin_skew (R : Space → Space → ℝ) (hR : ∀ i j, R j i = -R i j) :
    (rotationSpin G R).transpose = -rotationSpin G R := by
  simp only [rotationSpin, Matrix.transpose_smul, Matrix.transpose_sum,
    Matrix.transpose_mul, hSym]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib, ← smul_neg]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hR i j, neg_smul, smul_neg]

lemma trace_dual_pair (s : Finset Space) (hs : s.card ≤ 4) (i j : Space) (hij : i < j) :
    Matrix.trace ((word G s).transpose * (G i * G j)) =
      if s = {i,j} then 16 else 0 := by
  rw [← word_pair G i j hij]
  exact word_trace_dual G hG hSym s {i,j} hs (by simp [hij.ne])

lemma trace_rotationSpin_other (s : Finset Space) (hs : s.card ≤ 4) (hs2 : s.card ≠ 2)
    (R : Space → Space → ℝ) (hR : ∀ i, R i i = 0) :
    Matrix.trace ((word G s).transpose * rotationSpin G R) = 0 := by
  rw [rotationSpin, mul_smul_comm, Matrix.trace_smul, Matrix.mul_sum, Matrix.trace_sum]
  have hterm (i : Space) :
      Matrix.trace ((word G s).transpose * (∑ j, R i j • (G i * G j))) = 0 := by
    rw [Matrix.mul_sum, Matrix.trace_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [mul_smul_comm, Matrix.trace_smul]
    by_cases hij : i = j
    · subst j; rw [hR]; simp
    · rcases lt_or_gt_of_ne hij with hlt | hlt
      · have hne : s ≠ {i,j} := by
          intro heq
          apply hs2
          rw [heq]
          simp [hij]
        rw [trace_dual_pair G hG hSym s hs i j hlt, ite_eq_right hne, smul_zero]
      · have hne : s ≠ {j,i} := by
          intro heq
          apply hs2
          rw [heq]
          simp [Ne.symm hij]
        rw [gamma_anti G hG hij, mul_neg, Matrix.trace_neg,
          trace_dual_pair G hG hSym s hs j i hlt, ite_eq_right hne]
        simp
  simp_rw [hterm]
  simp

omit hG hSym in
lemma sorted_pair_unique (i j a b : Space) (hij : i < j) (hab : a < b)
    (h : ({i,j} : Finset Space) = {a,b}) : i = a ∧ j = b := by
  have hi : i = a ∨ i = b := by
    have : i ∈ ({a,b} : Finset Space) := by rw [← h]; simp
    simpa using this
  have hj : j = a ∨ j = b := by
    have : j ∈ ({a,b} : Finset Space) := by rw [← h]; simp
    simpa using this
  rcases hi with hi|hi <;> rcases hj with hj|hj
  · subst a; subst j; exact False.elim (lt_irrefl _ hij)
  · exact ⟨hi,hj⟩
  · subst b; subst a; exact False.elim (lt_asymm hij hab)
  · subst b; subst j; exact False.elim (lt_irrefl _ hij)

lemma trace_pair_pair (i j : Space) (hij : i < j) (a b : Space) :
    Matrix.trace ((G i * G j).transpose * (G a * G b)) =
      16 * (if a = i ∧ b = j then (1 : ℝ) else 0) -
      16 * (if a = j ∧ b = i then (1 : ℝ) else 0) := by
  rw [← word_pair G i j hij]
  by_cases hab : a = b
  · subst b
    have hs : ({i,j} : Finset Space).card ≤ 4 := by simp [hij.ne]
    rw [gamma_sq G hG, mul_one, Matrix.trace_transpose, trace_word G hG {i,j} hs]
    have hne : ({i,j} : Finset Space) ≠ ∅ := by simp
    rw [ite_eq_right hne]
    have h1 : ¬ (a = i ∧ a = j) := by rintro ⟨rfl, h⟩; exact hij.ne h
    have h2 : ¬ (a = j ∧ a = i) := by rintro ⟨rfl, h⟩; exact hij.ne h.symm
    simp [h1, h2]
  · rcases lt_or_gt_of_ne hab with hab | hab
    · rw [trace_dual_pair G hG hSym {i,j} (by simp [hij.ne]) a b hab]
      have heq : ({i,j} : Finset Space) = {a,b} ↔ a = i ∧ b = j := by
        constructor
        · intro h; obtain ⟨h1,h2⟩ := sorted_pair_unique i j a b hij hab h
          exact ⟨h1.symm,h2.symm⟩
        · rintro ⟨rfl,rfl⟩; rfl
      have hne : ¬ (a = j ∧ b = i) := by rintro ⟨rfl,rfl⟩; exact lt_asymm hij hab
      simp only [heq, ite_eq_right hne, mul_zero, sub_zero]
      split_ifs <;> norm_num
    · rw [gamma_anti G hG hab.ne.symm, mul_neg, Matrix.trace_neg,
        trace_dual_pair G hG hSym {i,j} (by simp [hij.ne]) b a hab]
      have heq : ({i,j} : Finset Space) = {b,a} ↔ a = j ∧ b = i := by
        constructor
        · intro h; obtain ⟨h1,h2⟩ := sorted_pair_unique i j b a hij hab h
          exact ⟨h2.symm,h1.symm⟩
        · rintro ⟨rfl,rfl⟩; rfl
      have hne : ¬ (a = i ∧ b = j) := by rintro ⟨rfl,rfl⟩; exact lt_asymm hij hab
      simp only [heq, ite_eq_right hne, mul_zero, zero_sub]
      split_ifs <;> norm_num

lemma trace_rotationSpin_pair (i j : Space) (hij : i < j)
    (R : Space → Space → ℝ) (hR : ∀ i j, R j i = -R i j) :
    Matrix.trace ((G i * G j).transpose * rotationSpin G R) = 8 * R i j := by
  simp only [rotationSpin, mul_smul_comm, Matrix.trace_smul, Matrix.mul_sum, Matrix.trace_sum,
    smul_eq_mul, trace_pair_pair G hG hSym i j hij]
  simp only [mul_sub, Finset.sum_sub_distrib]
  have h1 : (∑ a, ∑ b, R a b * (16 * if a = i ∧ b = j then (1 : ℝ) else 0)) = 16 * R i j := by
    have ht (a b : Space) : R a b *(16 * if a=i ∧ b=j then (1 : ℝ) else 0) =
        if a=i then if b=j then 16 * R i j else 0 else 0 := by
      by_cases ha : a=i <;> by_cases hb : b=j <;> simp [ha, hb]; ring
    simp_rw [ht]
    simp
  have h2 : (∑ a, ∑ b, R a b * (16 * if a = j ∧ b = i then (1 : ℝ) else 0)) = 16 * R j i := by
    have ht (a b : Space) : R a b *(16 * if a=j ∧ b=i then (1 : ℝ) else 0) =
        if a=j then if b=i then 16 * R j i else 0 else 0 := by
      by_cases ha : a=j <;> by_cases hb : b=i <;> simp [ha, hb]; ring
    simp_rw [ht]
    simp
  rw [h1, h2, hR]
  ring

lemma mass_pair_trace (v : Spin → ℝ) (i j : Space) (hij : i < j) :
    Matrix.trace ((G i * G j).transpose * massC G v) = -4 * massR G v i j := by
  have hsk : (word G {i,j}).transpose = -word G {i,j} := by
    rw [word_pair G i j hij, Matrix.transpose_mul, hSym, hSym,
      gamma_anti G hG (Ne.symm hij.ne)]
  have ht := mass_trace_word G hG hSym {i,j} hsk v
  rw [word_pair G i j hij, Finset.card_pair hij.ne, Finset.sum_pair hij.ne] at ht
  have hw := mass_pair_weight_cancel G hG hSym v i j
  simp only [massR]
  norm_num at ht
  rw [Matrix.transpose_mul]
  nlinarith [ht, hw]

def massRHS (v : Spin → ℝ) : Mat :=
  (-3/4 : ℝ) • massT G - (1/2 : ℝ) • rotationSpin G (massR G v)

lemma massRHS_skew (v : Spin → ℝ) : (massRHS G v).transpose = -massRHS G v := by
  simp only [massRHS, Matrix.transpose_sub, Matrix.transpose_smul,
    massT_transpose G hG hSym, rotationSpin_skew G hSym _ (massR_skew G hG hSym v)]
  module

omit hG hSym in
lemma trace_symm_skew (M B : Mat) (hM : M.transpose = M) (hB : B.transpose = -B) :
    Matrix.trace (M * B) = 0 := by
  rw [Matrix.trace_mul_comm]
  exact trace_skew_symm B M hB hM

lemma mass_identity_trace_word (s : Finset Space) (hs : s.card ≤ 4)
    (v : Spin → ℝ) (hv : ∑ α, v α ^ 2 = 1) :
    Matrix.trace ((word G s).transpose * massC G v) =
      Matrix.trace ((word G s).transpose * massRHS G v) := by
  have htrans := word_transpose G hG hSym s
  by_cases h2 : s.card = 2
  · obtain ⟨i,j,hij,heq⟩ := Finset.card_eq_two.mp h2
    have hpair (i j : Space) (hij : i < j) (heq : s = {i,j}) :
        Matrix.trace ((word G s).transpose * massC G v) =
          Matrix.trace ((word G s).transpose * massRHS G v) := by
      have hne : s ≠ firstThree := by
        intro hh; have := congrArg Finset.card hh; rw [h2, firstThree_card] at this; omega
      have hT : Matrix.trace ((word G s).transpose * massT G) = 0 := by
        rw [← word_firstThree, word_trace_dual G hG hSym _ _ hs (by rw [firstThree_card]; omega), ite_eq_right hne]
      rw [massRHS, mul_sub, mul_smul_comm, mul_smul_comm, Matrix.trace_sub,
        Matrix.trace_smul, Matrix.trace_smul, hT]
      rw [heq, word_pair G i j hij, mass_pair_trace G hG hSym v i j hij,
        trace_rotationSpin_pair G hG hSym i j hij _ (massR_skew G hG hSym v)]
      simp only [smul_eq_mul]
      ring
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact hpair i j hlt heq
    · exact hpair j i hlt (by simpa only [Finset.pair_comm] using heq)
  · by_cases h3 : s.card = 3
    · rw [thirdWord_mass_pair G hG hSym s h3 v hv]
      have hother := trace_rotationSpin_other G hG hSym s hs h2 (massR G v)
        (massR_diag G hG hSym v)
      rw [massRHS, mul_sub, mul_smul_comm, mul_smul_comm, Matrix.trace_sub,
        Matrix.trace_smul, Matrix.trace_smul, hother, ← word_firstThree,
        word_trace_dual G hG hSym s firstThree hs (by rw [firstThree_card]; omega)]
      split_ifs <;> norm_num
    · have hM : (word G s).transpose = word G s := by
        interval_cases hcard : s.card <;> norm_num [hcard, rankSign, Nat.choose] at htrans ⊢
        all_goals first | exact htrans | omega
      rw [hM, trace_symm_skew _ _ hM (massC_skew G v),
        trace_symm_skew _ _ hM (massRHS_skew G hG hSym v)]

theorem mass_spin_identity : MassSpinIdentity G := by
  intro v hv
  change massC G v = massRHS G v
  have ht : (massC G v).transpose = (massRHS G v).transpose := by
    apply matrix_eq_of_trace_words G hG
    intro a
    calc
      _ = Matrix.trace ((word G (shortSet a)).transpose * massC G v) := by
        simpa only [Matrix.transpose_transpose] using
          (Matrix.trace_transpose_mul (word G (shortSet a)) (massC G v).transpose).symm
      _ = Matrix.trace ((word G (shortSet a)).transpose * massRHS G v) :=
        mass_identity_trace_word G hG hSym (shortSet a) (shortSet_card a) v hv
      _ = _ := by
        simpa only [Matrix.transpose_transpose] using
          (Matrix.trace_transpose_mul (word G (shortSet a)) (massRHS G v).transpose)
  simpa only [Matrix.transpose_transpose] using congrArg Matrix.transpose ht

end
end BFSSGamma

end OAI
