import Mathlib

namespace OAI

/-! Clifford words, trace orthogonality and finite gamma-matrix bases. -/

namespace BFSSGamma
noncomputable section
open Matrix Finset
abbrev Space := Fin 9
abbrev Spin := Fin 16
abbrev Mat := Matrix Spin Spin ℝ
variable (G : Space → Mat)
variable (hG : ∀ i j, G i * G j + G j * G i = (if i = j then 2 else 0) • (1 : Mat))

def gammaTwo (i j : Space) : Mat := (1 / 2 : ℝ) • (G i * G j - G j * G i)
def symm (A : Mat) : Mat := (1 / 2 : ℝ) • (A + A.transpose)

def SpinIdentity : Prop := ∀ (v : Spin → ℝ), (∑ α, v α ^ 2) = 1 → ∀ j : Space,
  ∑ i, symm (Matrix.vecMulVec (G i *ᵥ v) (gammaTwo G i j *ᵥ v)) =
    (1 / 2 * dotProduct v (G j *ᵥ v)) • (1 : Mat) - (1 / 2 : ℝ) • G j

include hG

lemma gamma_sq (i : Space) : G i * G i = 1 := by
  have h := hG i i
  simp only [ite_true, two_smul] at h
  ext a b
  have hab := congr_fun (congr_fun h a) b
  simp only [Matrix.add_apply] at hab
  linarith

lemma gamma_anti {i j : Space} (hij : i ≠ j) : G i * G j = -(G j * G i) := by
  have h := hG i j
  simpa only [ite_eq_right hij, zero_smul, add_eq_zero_iff_eq_neg] using h

def singleSign (i j : Space) : ℝ := if i = j then 1 else -1

def word (s : Finset Space) : Mat := ((s.sort (· ≤ ·)).map G).prod

def reverseWord (s : Finset Space) : Mat := ((s.sort (· ≤ ·)).reverse.map G).prod

def wordSign (i : Space) (s : Finset Space) : ℝ := ∏ j ∈ s, singleSign i j

lemma gamma_conj (i j : Space) : G i * G j * G i = singleSign i j • G j := by
  by_cases hij : i = j
  · subst j
    simp only [gamma_sq G hG, one_mul, singleSign, ite_true, one_smul]
  · rw [gamma_anti G hG hij, neg_mul, Matrix.mul_assoc, gamma_sq G hG, mul_one]
    simp [singleSign, hij]

lemma conj_mul (i : Space) (A B : Mat) :
    G i * (A * B) * G i = (G i * A * G i) * (G i * B * G i) := by
  symm
  calc
    _ = G i * A * (G i * G i) * B * G i := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [gamma_sq G hG, mul_one]; simp only [Matrix.mul_assoc]

lemma list_conj (i : Space) (l : List Space) :
    G i * (l.map G).prod * G i = (l.map (singleSign i)).prod • (l.map G).prod := by
  induction l with
  | nil => simp [gamma_sq G hG]
  | cons j l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [conj_mul G hG, gamma_conj G hG, ih, smul_mul_assoc, mul_smul_comm, smul_smul]

lemma word_conj (i : Space) (s : Finset Space) :
    G i * word G s * G i = wordSign i s • word G s := by
  have h := list_conj G hG i (s.sort (· ≤ ·))
  rw [← List.prod_toFinset _ (Finset.sort_nodup _ _)] at h
  simpa [word, wordSign] using h

lemma list_inverse (l : List Space) :
    (l.reverse.map G).prod * (l.map G).prod = 1 := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.reverse_cons, List.map_append, List.prod_append,
      List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]
    calc
      _ = (l.reverse.map G).prod * (G j * G j) * (l.map G).prod  := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [gamma_sq G hG, mul_one, ih]

lemma reverseWord_mul_word (s : Finset Space) : reverseWord G s * word G s = 1 :=
  list_inverse G hG (s.sort (· ≤ ·))

lemma trace_conj (i : Space) (A : Mat) : Matrix.trace (G i * A * G i) = Matrix.trace A := by
  rw [Matrix.trace_mul_cycle, gamma_sq G hG, one_mul]

omit hG in
lemma wordSign_eq (i : Space) (s : Finset Space) :
    wordSign i s = (-1 : ℝ) ^ s.card * (if i ∈ s then -1 else 1) := by
  induction s using Finset.induction_on with
  | empty => simp [wordSign]
  | @insert a s ha ih =>
    rw [wordSign, Finset.prod_insert ha]
    change singleSign i a * wordSign i s = _
    rw [ih, Finset.card_insert_of_notMem ha, pow_succ]
    by_cases hia : i = a
    · subst i
      simp [singleSign, ha]
    · by_cases his : i ∈ s <;> simp [singleSign, hia, his]

omit hG in
lemma wordSign_eq_or (i : Space) (s : Finset Space) :
    wordSign i s = 1 ∨ wordSign i s = -1 := by
  rw [wordSign_eq]
  rcases neg_one_pow_eq_or ℝ s.card with h | h <;> rw [h] <;>
    by_cases his : i ∈ s <;> simp [his]

omit hG in
lemma signs_separate {s t : Finset Space} (hs : s.card ≤ 4) (ht : t.card ≤ 4)
    (hst : s ≠ t) : ∃ i, wordSign i s ≠ wordSign i t := by
  by_contra! heq
  have hu : (s ∪ t).card < (univ : Finset Space).card := by
    have := Finset.card_union_le s t
    simp only [Finset.card_univ, Fintype.card_fin] at *
    omega
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hu
  have hjs : j ∉ s := fun h => hj (Finset.mem_union_left t h)
  have hjt : j ∉ t := fun h => hj (Finset.mem_union_right s h)
  have hp : (-1 : ℝ)^s.card = (-1 : ℝ)^t.card := by
    simpa [wordSign_eq, hjs, hjt] using heq j
  have hn : (-1 : ℝ)^t.card ≠ 0 := pow_ne_zero _ (by norm_num)
  apply hst
  ext i
  have hi := heq i
  rw [wordSign_eq, wordSign_eq, hp] at hi
  have hi' := mul_left_cancel₀ hn hi
  by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;> simp [his, hit] at hi' ⊢ <;> norm_num at hi'

lemma reverseWord_conj (i : Space) (s : Finset Space) :
    G i * reverseWord G s * G i = wordSign i s • reverseWord G s := by
  have h := list_conj G hG i (s.sort (· ≤ ·)).reverse
  have hp : ((s.sort (· ≤ ·)).reverse.map (singleSign i)).prod = wordSign i s := by
    rw [List.map_reverse, List.prod_reverse,
      ← List.prod_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
    rfl
  rw [hp] at h
  exact h

lemma trace_reverseWord_word {s t : Finset Space} (hs : s.card ≤ 4) (ht : t.card ≤ 4) :
    Matrix.trace (reverseWord G s * word G t) = if s = t then 16 else 0 := by
  split_ifs with hst
  · subst t
    rw [reverseWord_mul_word G hG]
    norm_num [Matrix.trace_one,Spin]
  · obtain ⟨i, hi⟩ := signs_separate hs ht hst
    have h := trace_conj G hG i (reverseWord G s * word G t)
    rw [conj_mul G hG, reverseWord_conj G hG, word_conj G hG,
      smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.trace_smul, smul_eq_mul] at h
    have hp : wordSign i s * wordSign i t = -1 := by
      rcases wordSign_eq_or i s with hs' | hs'
      · rcases wordSign_eq_or i t with ht' | ht'
        · exact False.elim (hi (hs'.trans ht'.symm))
        · rw [hs', ht']; norm_num
      · rcases wordSign_eq_or i t with ht' | ht'
        · rw [hs', ht']; norm_num
        · exact False.elim (hi (hs'.trans ht'.symm))
    rw [hp] at h
    linarith

abbrev ShortIndex := (r : Fin 5) × {s : Finset Space // s.card = r.val}

def shortSet (a : ShortIndex) : Finset Space := a.2.val

omit hG in
lemma shortSet_card (a : ShortIndex) : (shortSet a).card ≤ 4 := by
  rw [shortSet, a.2.property]
  omega

omit hG in
lemma shortSet_injective : Function.Injective shortSet := by
  intro a b hab
  rcases a with ⟨r,a,ha⟩
  rcases b with ⟨q,b,hb⟩
  change a = b at hab
  subst b
  have hrq : r = q := Fin.ext (ha.symm.trans hb)
  subst q
  rfl

omit hG in
lemma shortIndex_card : Fintype.card ShortIndex = 256 := by
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_finset_len, Fintype.card_fin]
  norm_num [Fin.sum_univ_succ, Nat.choose]

lemma words_linearIndependent : LinearIndependent ℝ (fun a : ShortIndex => word G (shortSet a)) := by
  classical
  rw [linearIndependent_iff']
  intro s c hc a ha
  have ht := congrArg (fun M => Matrix.trace (reverseWord G (shortSet a) * M)) hc
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul, mul_zero, Matrix.trace_zero] at ht
  have he (b : ShortIndex) :
      Matrix.trace (reverseWord G (shortSet a) * word G (shortSet b)) =
      if b = a then 16 else 0 := by
    rw [trace_reverseWord_word G hG (shortSet_card a) (shortSet_card b)]
    simp only [shortSet_injective.eq_iff, eq_comm]
  simp_rw [he] at ht
  simp only [mul_ite, mul_zero] at ht
  rw [Finset.sum_ite_eq' _ _] at ht
  simp only [ha, ite_true] at ht
  linarith

lemma words_span : Submodule.span ℝ (Set.range (fun a : ShortIndex => word G (shortSet a))) = ⊤ := by
  have : Nonempty ShortIndex := ⟨⟨0, ⟨∅, rfl⟩⟩⟩
  apply (words_linearIndependent G hG).span_eq_top_of_card_eq_finrank
  rw [shortIndex_card, Module.finrank_matrix]
  norm_num [Spin]

lemma list_commute (a : Space) (l : List Space) (ha : a ∉ l) :
    (l.map G).prod * G a = (-1 : ℝ)^l.length • (G a * (l.map G).prod) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    have hab : b ≠ a := by intro h; apply ha; simp [h]
    have hal : a ∉ l := fun h => ha (List.mem_cons_of_mem _ h)
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    calc
      _ = G b * ((l.map G).prod * G a) := by rw [Matrix.mul_assoc]
      _ = G b * ((-1 : ℝ)^l.length • (G a * (l.map G).prod)) := by rw [ih hal]
      _ = (-1 : ℝ)^l.length • (-(G a * G b) * (l.map G).prod) := by
        rw [mul_smul_comm, ← Matrix.mul_assoc, gamma_anti G hG hab]
      _ = _ := by rw [pow_succ, mul_smul]; simp only [neg_mul, neg_smul, one_smul, Matrix.mul_assoc]

def rankSign (n : ℕ) : ℝ := (-1)^n.choose 2

lemma list_reverse_eq (l : List Space) (hl : l.Nodup) :
    (l.reverse.map G).prod = rankSign l.length • (l.map G).prod := by
  induction l with
  | nil => simp [rankSign]
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.nodup_cons.mp hl
    simp only [List.reverse_cons, List.map_append, List.prod_append,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [ih hl, smul_mul_assoc, list_commute G hG a l ha, smul_smul]
    simp only [List.length_cons, rankSign, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
    rw [mul_comm]

variable (hSym : ∀ i, (G i).transpose = G i)
include hSym

omit hG in
lemma list_transpose (l : List Space) :
    ((l.map G).prod).transpose = (l.reverse.map G).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.transpose_mul, hSym, ih,
      List.reverse_cons, List.map_append, List.prod_append, List.map_nil, List.prod_nil,
      mul_one]

lemma word_transpose (s : Finset Space) :
    (word G s).transpose = rankSign s.card • word G s := by
  rw [word, list_transpose G hSym, list_reverse_eq G hG _ (Finset.sort_nodup _ _)]
  rw [Finset.length_sort]

omit hSym hG in
lemma symm_transpose (A : Mat) : (symm A).transpose = symm A := by
  simp only [symm, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose]
  rw [add_comm]

omit hSym in
lemma matrix_eq_of_trace_words {A B : Mat}
    (h : ∀ a : ShortIndex, Matrix.trace (word G (shortSet a) * A) =
      Matrix.trace (word G (shortSet a) * B)) : A = B := by
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro M
  have hm : M ∈ Submodule.span ℝ (Set.range (fun a : ShortIndex => word G (shortSet a))) := by
    rw [words_span G hG]
    trivial
  induction hm using Submodule.span_induction with
  | mem x hx => obtain ⟨a,rfl⟩ := hx; exact h a
  | zero => simp
  | add x y hx hy hx' hy' => simp only [add_mul, Matrix.trace_add, hx', hy']
  | smul c x hx hx' => simp only [smul_mul_assoc, Matrix.trace_smul, hx']

omit hSym in
lemma sum_word_conj (s : Finset Space) :
    ∑ i, G i * word G s * G i =
      ((-1 : ℝ)^s.card * (9 - 2 * (s.card : ℝ))) • word G s := by
  simp_rw [word_conj G hG, wordSign_eq]
  rw [← Finset.sum_smul]
  congr 1
  rw [← Finset.mul_sum]
  congr 1
  have hsum : (∑ i : Space, if i ∈ s then (-1 : ℝ) else 1) = 9 - 2 * (s.card : ℝ) := by
    calc
      _ = ∑ i : Space, (1 - 2 * (if i ∈ s then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        split_ifs <;> norm_num
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, mul_one, ← Finset.mul_sum, Finset.sum_boole]
        have hf : (univ.filter (fun i : Space => i ∈ s)) = s := by ext i; simp
        rw [hf]
        norm_num
  exact hsum

omit hSym in
lemma gammaTwo_alt (i j : Space) :
    gammaTwo G i j = G i * G j - (if i = j then (1 : ℝ) else 0) • (1 : Mat) := by
  by_cases hij : i = j
  · subst j
    simp [gammaTwo, gamma_sq G hG]
  · have hji := gamma_anti G hG (Ne.symm hij)
    rw [gammaTwo, hji, ite_eq_right hij, zero_smul, sub_zero]
    module

end
end BFSSGamma

end OAI
