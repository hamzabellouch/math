import Mathlib

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.FreeMoments

attribute [local instance] Classical.propDecidable

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (τ : A →ₗ[ℂ] ℂ)

structure Letter where
  color : ι
  val : A
  mem : val ∈ S color
  centered : τ val = 0

variable {S τ}

def word (w : List (Letter S τ)) : A := (w.map Letter.val).prod

def Reduced (w : List (Letter S τ)) : Prop :=
  w.IsChain (fun a b => a.color ≠ b.color)

def Free (S : ι → StarSubalgebra ℂ A) (τ : A →ₗ[ℂ] ℂ) : Prop :=
  ∀ w : List (Letter S τ), Reduced w → w ≠ [] → τ (word w) = 0

@[simp] lemma word_nil : word ([] : List (Letter S τ)) = 1 := rfl

@[simp] lemma word_cons (a : Letter S τ) (w : List (Letter S τ)) :
    word (a :: w) = a.val * word w := rfl

@[simp] lemma word_append (w z : List (Letter S τ)) :
    word (w ++ z) = word w * word z := by simp [word, List.prod_append]

@[simp] lemma reduced_nil : Reduced ([] : List (Letter S τ)) := List.isChain_nil

@[simp] lemma reduced_singleton (a : Letter S τ) : Reduced [a] := List.IsChain.singleton a

lemma Reduced.tail {a : Letter S τ} {w : List (Letter S τ)}
    (h : Reduced (a :: w)) : Reduced w := List.IsChain.tail h

variable (hstar : ∀ a : A, τ (star a) = star (τ a))

def Letter.conj (a : Letter S τ) : Letter S τ where
  color := a.color
  val := star a.val
  mem := star_mem a.mem
  centered := by rw [hstar, a.centered, star_zero]

@[simp] lemma star_color (a : Letter S τ) : (a.conj hstar).color = a.color := rfl

@[simp] lemma star_val (a : Letter S τ) : (a.conj hstar).val = star a.val := rfl

def reverseStar (w : List (Letter S τ)) : List (Letter S τ) :=
  (w.map (Letter.conj hstar)).reverse

@[simp] lemma word_reverseStar (w : List (Letter S τ)) :
    word (reverseStar hstar w) = star (word w) := by
  induction w with
  | nil => simp [reverseStar]
  | cons a w ih =>
    rw [show reverseStar hstar (a :: w) = reverseStar hstar w ++ [a.conj hstar] by
      simp only [reverseStar, List.map_cons, List.reverse_cons]]
    simp [ih, star_mul]

lemma Reduced.reverseStar {w : List (Letter S τ)} (h : Reduced w) :
    Reduced (reverseStar hstar w) := by
  apply List.isChain_reverse.mpr
  apply (List.isChain_map _).mpr
  exact h.imp (fun _ _ hab => hab.symm)

lemma reduced_join {a b : Letter S τ} {w z : List (Letter S τ)}
    (hw : Reduced (a :: w)) (hz : Reduced (b :: z)) (hab : a.color ≠ b.color) :
    Reduced (reverseStar hstar (a :: w) ++ b :: z) := by
  apply (Reduced.reverseStar hstar hw).append hz
  intro x hx y hy
  simp only [List.head?_cons, Option.mem_some_iff] at hy
  subst y
  have hx' : x = a.conj hstar := by
    exact (by simpa [reverseStar, List.getLast?_reverse] using hx : _ = x).symm
  subst x
  exact hab

include hstar in
lemma gram_different_head (hfree : Free S τ) {a b : Letter S τ}
    {w z : List (Letter S τ)} (hw : Reduced (a :: w)) (hz : Reduced (b :: z))
    (hab : a.color ≠ b.color) :
    τ (star (word (a :: w)) * word (b :: z)) = 0 := by
  have h := hfree (reverseStar hstar (a :: w) ++ b :: z)
    (reduced_join hstar hw hz hab) (by simp)
  simpa using h

variable (h1 : τ 1 = 1)

def centeredPair (a b : Letter S τ) (hab : a.color = b.color) : Letter S τ where
  color := a.color
  val := star a.val * b.val - τ (star a.val * b.val) • (1 : A)
  mem := sub_mem
    (mul_mem (star_mem a.mem) (by simpa [hab] using b.mem))
    (SMulMemClass.smul_mem _ (one_mem (S a.color)))
  centered := by simp [map_sub, map_smul, h1]

lemma reduced_pair_join {a b : Letter S τ} {w z : List (Letter S τ)}
    (hw : Reduced (a :: w)) (hz : Reduced (b :: z)) (hab : a.color = b.color) :
    Reduced (reverseStar hstar w ++ centeredPair h1 a b hab :: z) := by
  have hz' : Reduced (centeredPair h1 a b hab :: z) := by
    apply hz.imp_head
    intro c hc
    exact hab ▸ hc
  apply (Reduced.reverseStar hstar hw.tail).append hz'
  intro x hx y hy
  simp only [List.head?_cons, Option.mem_some_iff] at hy
  subst y
  cases w with
  | nil => simp [reverseStar] at hx
  | cons c w =>
    have hx' : x = c.conj hstar := by
      exact (by simpa [reverseStar, List.getLast?_reverse] using hx : _ = x).symm
    subst x
    exact hw.rel.symm

include hstar h1 in
lemma gram_same_head (hfree : Free S τ) {a b : Letter S τ}
    {w z : List (Letter S τ)} (hw : Reduced (a :: w)) (hz : Reduced (b :: z))
    (hab : a.color = b.color) :
    τ (star (word (a :: w)) * word (b :: z)) =
      τ (star a.val * b.val) * τ (star (word w) * word z) := by
  have h := hfree (reverseStar hstar w ++ centeredPair h1 a b hab :: z)
    (reduced_pair_join hstar h1 hw hz hab) (by simp)
  have hid : star (word w) * (star a.val * b.val - τ (star a.val * b.val) • (1 : A)) * word z =
      star (word (a :: w)) * word (b :: z) -
        τ (star a.val * b.val) • (star (word w) * word z) := by
    simp only [word_cons, star_mul, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
      mul_one, mul_assoc]
  simp only [word_append, word_reverseStar, word_cons, centeredPair] at h
  rw [← mul_assoc, hid, map_sub, map_smul] at h
  exact sub_eq_zero.mp h

def gram : List (Letter S τ) → List (Letter S τ) → ℂ
  | [], [] => 1
  | [], _ :: _ => 0
  | _ :: _, [] => 0
  | a :: w, b :: z => if a.color = b.color then τ (star a.val * b.val) * gram w z else 0

include hstar h1 in
theorem gram_word (hfree : Free S τ) (w z : List (Letter S τ))
    (hw : Reduced w) (hz : Reduced z) :
    τ (star (word w) * word z) = gram w z := by
  classical
  induction w generalizing z with
  | nil =>
    cases z with
    | nil => simpa [gram] using h1
    | cons b z => simpa [gram] using hfree (b :: z) hz (by simp)
  | cons a w ih =>
    cases z with
    | nil =>
      rw [word_nil, mul_one, hstar, hfree (a :: w) hw (by simp)]
      simp only [star_zero, gram]
    | cons b z =>
      by_cases hab : a.color = b.color
      · rw [gram, ite_eq_left hab, gram_same_head hstar h1 hfree hw hz hab,
          ih z hw.tail hz.tail]
      · rw [gram, ite_eq_right hab, gram_different_head hstar hfree hw hz hab]

lemma gram_zero_of_colors_ne (w z : List (Letter S τ))
    (h : w.map Letter.color ≠ z.map Letter.color) : gram w z = 0 := by
  induction w generalizing z with
  | nil => cases z <;> simp_all [gram]
  | cons a w ih =>
    cases z with
    | nil => rfl
    | cons b z =>
      by_cases hab : a.color = b.color
      · rw [gram, ite_eq_left hab]
        have ht : w.map Letter.color ≠ z.map Letter.color := by
          intro ht
          exact h (by simp [hab, ht])
        rw [ih z ht, mul_zero]
      · simp only [gram, ite_eq_right hab]

lemma gram_ofFn {n : ℕ} (v w : Fin n → Letter S τ)
    (hc : ∀ i, (v i).color = (w i).color) :
    gram (List.ofFn v) (List.ofFn w) = ∏ i, τ (star (v i).val * (w i).val) := by
  induction n with
  | zero => simp [gram]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, gram, ite_eq_left (hc 0),
      ih (fun i => v i.succ) (fun i => w i.succ) (fun i => hc i.succ), Fin.prod_univ_succ]

include hstar h1 in
lemma reduced_word_orthogonal (hfree : Free S τ) (w z : List (Letter S τ))
    (hw : Reduced w) (hz : Reduced z) (hc : w.map Letter.color ≠ z.map Letter.color) :
    τ (star (word w) * word z) = 0 := by
  rw [gram_word hstar h1 hfree w z hw hz, gram_zero_of_colors_ne w z hc]

include hstar h1 in
lemma reduced_word_inner {n : ℕ} (hfree : Free S τ) (v w : Fin n → Letter S τ)
    (hv : Reduced (List.ofFn v)) (hw : Reduced (List.ofFn w))
    (hc : ∀ i, (v i).color = (w i).color) :
    τ (star (word (List.ofFn v)) * word (List.ofFn w)) =
      ∏ i, τ (star (v i).val * (w i).val) := by
  rw [gram_word hstar h1 hfree _ _ hv hw, gram_ofFn v w hc]

def centerLetter (i : ι) (a : A) (ha : a ∈ S i) : Letter S τ where
  color := i
  val := a - τ a • (1 : A)
  mem := sub_mem ha (SMulMemClass.smul_mem _ (one_mem (S i)))
  centered := by simp [map_sub, map_smul, h1]

def wordSpan (S : ι → StarSubalgebra ℂ A) (τ : A →ₗ[ℂ] ℂ) : Submodule ℂ A :=
  Submodule.span ℂ {a | ∃ w : List (Letter S τ), Reduced w ∧ word w = a}

lemma word_mem_span {w : List (Letter S τ)} (hw : Reduced w) :
    word w ∈ wordSpan S τ := Submodule.subset_span ⟨w, hw, rfl⟩

lemma one_mem_wordSpan : (1 : A) ∈ wordSpan S τ :=
  word_mem_span (w := []) reduced_nil

include h1 in
lemma generator_mem_wordSpan (i : ι) (a : A) (ha : a ∈ S i) : a ∈ wordSpan S τ := by
  have hc := word_mem_span (reduced_singleton (centerLetter h1 i a ha))
  have hs := (wordSpan S τ).smul_mem (τ a) one_mem_wordSpan
  have hd : word [centerLetter h1 i a ha] + τ a • (1 : A) = a := by
    simp [centerLetter]
  rw [← hd]
  exact (wordSpan S τ).add_mem hc hs

include h1 in
lemma generator_mul_word (i : ι) (a : A) (ha : a ∈ S i)
    (w : List (Letter S τ)) (hw : Reduced w) : a * word w ∈ wordSpan S τ := by
  cases w with
  | nil => simpa using generator_mem_wordSpan h1 i a ha
  | cons b w =>
    by_cases hc : i = b.color
    · have hab : a * b.val ∈ S i := mul_mem ha (by simpa [hc] using b.mem)
      let c := centerLetter h1 i (a * b.val) hab
      have hw' : Reduced (c :: w) := by
        apply hw.imp_head
        intro z hz
        change i ≠ z.color
        simpa [hc] using hz
      have hmem := (wordSpan S τ).add_mem (word_mem_span hw')
        ((wordSpan S τ).smul_mem (τ (a * b.val)) (word_mem_span hw.tail))
      have heq : word (c :: w) + τ (a * b.val) • word w = a * word (b :: w) := by
        simp only [word_cons, c, centerLetter, sub_mul, smul_mul_assoc, one_mul, mul_assoc]
        exact sub_add_cancel _ _
      rwa [heq] at hmem
    · let c := centerLetter h1 i a ha
      have hw' : Reduced (c :: b :: w) := List.isChain_cons_cons.mpr ⟨hc, hw⟩
      have hmem := (wordSpan S τ).add_mem (word_mem_span hw')
        ((wordSpan S τ).smul_mem (τ a) (word_mem_span hw))
      have heq : word (c :: b :: w) + τ a • word (b :: w) = a * word (b :: w) := by
        change (a - τ a • (1 : A)) * word (b :: w) + τ a • word (b :: w) = _
        simp only [sub_mul, smul_mul_assoc, one_mul, sub_add_cancel]
      rwa [heq] at hmem

include h1 in
lemma generator_mul_span (i : ι) (a : A) (ha : a ∈ S i)
    {b : A} (hb : b ∈ wordSpan S τ) : a * b ∈ wordSpan S τ := by
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨w, hw, rfl⟩ := hb
    exact generator_mul_word h1 i a ha w hw
  | zero => simp only [mul_zero, Submodule.zero_mem]
  | add b c _ _ hb hc => simpa only [mul_add] using (wordSpan S τ).add_mem hb hc
  | smul z b _ hb => simpa only [mul_smul_comm] using (wordSpan S τ).smul_mem z hb

include h1 in
lemma word_mul_span (w : List (Letter S τ)) {b : A} (hb : b ∈ wordSpan S τ) :
    word w * b ∈ wordSpan S τ := by
  induction w with
  | nil => simpa using hb
  | cons a w ih =>
    simpa only [word_cons, mul_assoc] using generator_mul_span h1 a.color a.val a.mem ih

include h1 in
lemma mul_mem_wordSpan {a b : A} (ha : a ∈ wordSpan S τ) (hb : b ∈ wordSpan S τ) :
    a * b ∈ wordSpan S τ := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨w, _, rfl⟩ := ha
    exact word_mul_span h1 w hb
  | zero => simp only [zero_mul, Submodule.zero_mem]
  | add a c _ _ ha hc => simpa only [add_mul] using (wordSpan S τ).add_mem ha hc
  | smul z a _ ha => simpa only [smul_mul_assoc] using (wordSpan S τ).smul_mem z ha

include hstar in
lemma star_mem_wordSpan {a : A} (ha : a ∈ wordSpan S τ) : star a ∈ wordSpan S τ := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨w, hw, rfl⟩ := ha
    rw [← word_reverseStar hstar]
    exact word_mem_span (Reduced.reverseStar hstar hw)
  | zero => simp only [star_zero, Submodule.zero_mem]
  | add a c _ _ ha hc => simpa only [star_add] using (wordSpan S τ).add_mem ha hc
  | smul z a _ ha => simpa only [star_smul] using (wordSpan S τ).smul_mem (star z) ha

variable (S) in

def reducedAlgebra : StarSubalgebra ℂ A where
  carrier := wordSpan S τ
  zero_mem' := (wordSpan S τ).zero_mem
  add_mem' := (wordSpan S τ).add_mem
  one_mem' := one_mem_wordSpan
  mul_mem' := mul_mem_wordSpan h1
  algebraMap_mem' z := by
    change algebraMap ℂ A z ∈ wordSpan S τ
    rw [Algebra.algebraMap_eq_smul_one]
    exact (wordSpan S τ).smul_mem z one_mem_wordSpan
  star_mem' := star_mem_wordSpan hstar

include hstar h1 in
lemma generator_le_reducedAlgebra (i : ι) : S i ≤ reducedAlgebra S hstar h1 :=
  fun a ha => generator_mem_wordSpan h1 i a ha

lemma reducedAlgebra_eq_iSup : reducedAlgebra S hstar h1 = ⨆ i, S i := by
  apply le_antisymm
  · intro a ha
    change a ∈ wordSpan S τ at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨w, hw, rfl⟩ := ha
      clear hw
      induction w with
      | nil => exact one_mem _
      | cons b w ih =>
        exact mul_mem ((le_iSup S b.color) b.mem) ih
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul z a _ ha => exact SMulMemClass.smul_mem z ha
  · exact iSup_le (fun i => generator_le_reducedAlgebra (S := S) (hstar := hstar) (h1 := h1) i)

end Kadison.FreeMoments
end

end OAI
