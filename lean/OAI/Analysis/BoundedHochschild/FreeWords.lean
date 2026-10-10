import Mathlib
import OAI.Analysis.BoundedHochschild.ProductTaylor

namespace OAI

/-! Reduced free words, cancellation fibers and repeated-letter bounds. -/

noncomputable section


namespace HochschildFreeWords
variable {α : Type*}
def charge (a : α × Bool) : ℤ := if a.2 then 1 else -1
@[simp] theorem charge_true (a : α) : charge (a, true) = 1 := rfl
@[simp] theorem charge_false (a : α) : charge (a, false) = -1 := rfl
@[simp] theorem charge_not (a : α) (b : Bool) :
    charge (a, b) + charge (a, !b) = 0 := by cases b <;> rfl
def total (l : List (α × Bool)) : ℤ := (l.map charge).sum
@[simp] theorem total_nil : total ([] : List (α × Bool)) = 0 := rfl
@[simp] theorem total_cons (a : α × Bool) (l : List (α × Bool)) :
    total (a :: l) = charge a + total l := by simp [total]
@[simp] theorem total_append (l k : List (α × Bool)) :
    total (l ++ k) = total l + total k := by simp [total]
@[simp] theorem total_reverse (l : List (α × Bool)) : total l.reverse = total l := by
  simp [total, List.map_reverse]
 
def Above (h : ℤ) : List (α × Bool) → Prop
  | [] => 0 ≤ h
  | a :: l => 0 ≤ h ∧ Above (h + charge a) l
@[simp] theorem above_nil (h : ℤ) : Above h ([] : List (α × Bool)) ↔ 0 ≤ h := Iff.rfl
@[simp] theorem above_cons (h : ℤ) (a : α × Bool) (l : List (α × Bool)) :
    Above h (a :: l) ↔ 0 ≤ h ∧ Above (h + charge a) l := Iff.rfl
lemma above_start {h : ℤ} {l : List (α × Bool)} (hl : Above h l) : 0 ≤ h := by
  cases l with
  | nil => exact hl
  | cons a l => exact hl.1
lemma above_mono {h k : ℤ} (hh : h ≤ k) {l : List (α × Bool)}
    (hl : Above h l) : Above k l := by
  induction l generalizing h k with
  | nil => exact hl.trans hh
  | cons a l ih => exact ⟨hl.1.trans hh, ih (by omega) hl.2⟩
lemma above_append (h : ℤ) (l k : List (α × Bool)) :
    Above h (l ++ k) ↔ Above h l ∧ Above (h + total l) k := by
  induction l generalizing h with
  | nil => simpa using (fun hh : Above h k => above_start hh)
  | cons a l ih =>
    simp only [List.cons_append, above_cons, ih, total_cons]
    constructor
    · rintro ⟨hh, hl, hk⟩
      exact ⟨⟨hh, hl⟩, by convert hk using 1; omega⟩
    · rintro ⟨⟨hh, hl⟩, hk⟩
      exact ⟨hh, hl, by convert hk using 1; omega⟩
lemma above_cancel (h : ℤ) (l k : List (α × Bool)) (a : α) (b : Bool)
    (hw : Above h (l ++ (a,b) :: (a,!b) :: k)) : Above h (l ++ k) := by
  rw [above_append] at hw ⊢
  refine ⟨hw.1, ?_⟩
  have hk := hw.2.2.2
  convert hk using 1
  have := charge_not a b
  omega
lemma total_step {l k : List (α × Bool)} (h : FreeGroup.Red.Step l k) :
    total l = total k := by
  cases h with
  | @not l k a b =>
    simp only [total_append, total_cons]
    have := charge_not a b
    omega
lemma above_step {h : ℤ} {l k : List (α × Bool)} (hr : FreeGroup.Red.Step l k)
    (hl : Above h l) : Above h k := by
  cases hr
  exact above_cancel _ _ _ _ _ hl
lemma above_reverse_step {h : ℤ} {l k : List (α × Bool)}
    (hr : FreeGroup.Red.Step l k) (hl : Above h l.reverse) : Above h k.reverse := by
  cases hr with
  | @not l k a b =>
    simp only [List.reverse_append, List.reverse_cons, List.append_assoc] at hl ⊢
    have hh : Above h (k.reverse ++ (a,!b) :: (a,!(!b)) :: l.reverse) := by
      simpa using hl
    exact above_cancel _ _ _ _ _ hh
lemma above_red {h : ℤ} {l k : List (α × Bool)} (hr : FreeGroup.Red l k)
    (hl : Above h l) : Above h k := by
  induction hr with
  | refl => exact hl
  | tail hr hs ih => exact above_step hs ih
lemma above_reverse_red {h : ℤ} {l k : List (α × Bool)} (hr : FreeGroup.Red l k)
    (hl : Above h l.reverse) : Above h k.reverse := by
  induction hr with
  | refl => exact hl
  | tail hr hs ih => exact above_reverse_step hs ih
lemma total_red {l k : List (α × Bool)} (hr : FreeGroup.Red l k) : total l = total k := by
  induction hr with
  | refl => rfl
  | tail hr hs ih => exact ih.trans (total_step hs)
lemma above_head {l : List (α × Bool)} (hl : Above 0 l) (hne : l ≠ []) :
    l.head?.map Prod.snd = some true := by
  cases l with
  | nil => exact (hne rfl).elim
  | cons a l =>
    obtain ⟨a,b⟩ := a
    have hh := above_start hl.2
    cases b with
    | false => simp [charge] at hh
    | true => rfl
 
inductive OddBlock : List (α × Bool) → Prop
  | one (a : α) : OddBlock [(a,true)]
  | step (a b : α) {l : List (α × Bool)} : OddBlock l →
      OddBlock ((a,true)::(b,false)::l)
lemma OddBlock.total {l : List (α × Bool)} (hl : OddBlock l) : total l = 1 := by
  induction hl with
  | one a => simp
  | step a b hl ih => simp [ih]
lemma OddBlock.above {l : List (α × Bool)} (hl : OddBlock l) : Above 0 l := by
  induction hl with
  | one a => simp [Above]
  | step a b hl ih => simpa [Above] using ih
lemma OddBlock.above_reverse {l : List (α × Bool)} (hl : OddBlock l) :
    Above 0 l.reverse := by
  induction hl with
  | one a => simp [Above]
  | @step a b l hl ih =>
    simp only [List.reverse_cons, List.append_assoc]
    rw [above_append]
    exact ⟨ih, by simp [hl.total, Above]⟩
lemma blocks_total (ls : List (List (α × Bool))) (h : ∀ l ∈ ls, OddBlock l) :
    total ls.flatten = ls.length := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    simp only [List.flatten_cons, total_append, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [(h l (by simp)).total, ih (fun k hk => h k (by simp [hk]))]
    omega
lemma blocks_above (ls : List (List (α × Bool))) (h : ∀ l ∈ ls, OddBlock l) :
    Above 0 ls.flatten ∧ Above 0 ls.flatten.reverse := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    have hl := h l (by simp)
    have ht := fun k hk => h k (List.mem_cons_of_mem l hk)
    obtain ⟨hp, hs⟩ := ih ht
    simp only [List.flatten_cons, List.reverse_append, above_append]
    refine ⟨⟨hl.above, above_mono ?_ hp⟩, ⟨hs, above_mono ?_ hl.above_reverse⟩⟩
    · rw [hl.total]; omega
    · rw [total_reverse, blocks_total ls ht]; positivity
 

theorem ordered_blocks_reduced [DecidableEq α]
    (ls : List (List (α × Bool))) (hne : ls ≠ []) (h : ∀ l ∈ ls, OddBlock l) :
    let w := FreeGroup.reduce ls.flatten
    w ≠ [] ∧ w.head?.map Prod.snd = some true ∧
      w.reverse.head?.map Prod.snd = some true := by
  dsimp
  have ht := total_red (FreeGroup.reduce.red (L := ls.flatten))
  rw [blocks_total ls h] at ht
  have hn : FreeGroup.reduce ls.flatten ≠ [] := by
    intro hz
    rw [hz, total_nil] at ht
    have : ls.length = 0 := by exact_mod_cast ht
    exact hne (List.length_eq_zero_iff.mp this)
  obtain ⟨hp, hs⟩ := blocks_above ls h
  exact ⟨hn, above_head (above_red FreeGroup.reduce.red hp) hn,
    above_head (above_reverse_red FreeGroup.reduce.red hs) (by simpa)⟩
end HochschildFreeWords

namespace HochschildFreeWords
open Finset
variable {α : Type*}
 
def insertPair (w : List (α × Bool)) (i : ℕ) (x : α × Bool) : List (α × Bool) :=
  w.take i ++ x :: (x.1, !x.2) :: w.drop i
@[simp] theorem length_insertPair (w : List (α × Bool)) (i : ℕ) (x : α × Bool) :
    (insertPair w i x).length = w.length + 2 := by
  simp only [insertPair, List.length_append, List.length_cons, List.length_take,
    List.length_drop]
  omega
lemma insertPair_append (l k : List (α × Bool)) (a : α) (b : Bool) :
    insertPair (l ++ k) l.length (a,b) = l ++ (a,b) :: (a,!b) :: k := by
  simp [insertPair]
variable [DecidableEq α] [Fintype α]
 

def expansions : ℕ → List (α × Bool) → Finset (List (α × Bool))
  | 0, w => {w}
  | p+1, w => (expansions p w).biUnion fun v =>
      (range (v.length + 1)).biUnion fun i => univ.image (insertPair v i)
lemma mem_expansions_length {p : ℕ} {v w : List (α × Bool)}
    (hv : v ∈ expansions p w) : v.length = w.length + 2*p := by
  induction p generalizing v with
  | zero =>
    simp only [expansions, mem_singleton] at hv
    simp [hv]
  | succ p ih =>
    simp only [expansions, mem_biUnion, mem_image, mem_univ, true_and] at hv
    obtain ⟨u, hu, i, hi, x, rfl⟩ := hv
    rw [length_insertPair, ih hu]
    omega
lemma expansions_insert {p : ℕ} {v w : List (α × Bool)} (hv : v ∈ expansions p w)
    (i : ℕ) (hi : i ≤ v.length) (x : α × Bool) :
    insertPair v i x ∈ expansions (p+1) w := by
  simp only [expansions, mem_biUnion, mem_image, mem_univ, true_and]
  exact ⟨v, hv, i, by simpa using hi, x, rfl⟩
lemma red_mem_expansions {v w : List (α × Bool)} (h : FreeGroup.Red v w) :
    ∃ p, v.length = w.length + 2*p ∧ v ∈ expansions p w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, by omega, by simp [expansions]⟩
  | @head v u hs hr ih =>
    obtain ⟨p, hp, hm⟩ := ih
    refine ⟨p+1, ?_, ?_⟩
    · have := hs.length; omega
    · cases hs with
      | @not l k a b =>
        simpa only [insertPair_append] using
          expansions_insert hm l.length (by simp) (a,b)
lemma mem_expansions_of_reduce {v w : List (α × Bool)} (h : FreeGroup.reduce v = w) :
    v ∈ expansions ((v.length-w.length)/2) w := by
  obtain ⟨p, hp, hm⟩ := red_mem_expansions (h ▸ FreeGroup.reduce.red (L := v))
  have : (v.length - w.length) / 2 = p := by omega
  simpa only [this] using hm
lemma card_expansions_succ (p : ℕ) (w : List (α × Bool)) :
    (expansions (p+1) w).card ≤
      (expansions p w).card * (w.length + 2*p + 1) * (2 * Fintype.card α) := by
  conv_lhs => unfold expansions
  apply (card_biUnion_le).trans
  calc
    _ ≤ ∑ v ∈ expansions p w, (w.length + 2*p + 1) * (2 * Fintype.card α) := by
      apply sum_le_sum
      intro v hv
      apply card_biUnion_le.trans
      calc
        _ ≤ ∑ _i ∈ range (v.length+1), Fintype.card (α × Bool) := by
          apply sum_le_sum
          intro i hi
          exact card_image_le
        _ = _ := by
          rw [mem_expansions_length hv]
          simp [Nat.mul_comm, Nat.mul_left_comm]
    _ = _ := by simp [Nat.mul_assoc]
 

theorem card_expansions_le (p : ℕ) (w : List (α × Bool)) :
    (expansions p w).card ≤ (2 * (w.length + 2*p)) ^ p * (Fintype.card α) ^ p := by
  induction p with
  | zero => simp [expansions]
  | succ p ih =>
    calc
      _ ≤ (expansions p w).card * (w.length+2*p+1) * (2 * Fintype.card α) :=
        card_expansions_succ p w
      _ ≤ ((2 * (w.length+2*p)) ^ p * (Fintype.card α)^p) *
          (w.length+2*p+1) * (2 * Fintype.card α) := by gcongr
      _ ≤ ((2 * (w.length+2*(p+1))) ^ p * (Fintype.card α)^p) *
          (w.length+2*(p+1)) * (2 * Fintype.card α) := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul
          (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) p)) (by omega))
      _ = _ := by rw [pow_succ, pow_succ]; ring
 
theorem reduction_fiber_bound (S : Finset (List (α × Bool)))
    (L : ℕ) (w : List (α × Bool)) (hne : S.Nonempty)
    (hS : ∀ v ∈ S, v.length = L ∧ FreeGroup.reduce v = w) :
    ∃ p, L = w.length + 2*p ∧
      S.card ≤ (2*L)^p * (Fintype.card α)^p := by
  obtain ⟨v, hv⟩ := hne
  obtain ⟨p, hp, _⟩ := red_mem_expansions
    ((hS v hv).2 ▸ FreeGroup.reduce.red (L := v))
  rw [(hS v hv).1] at hp
  refine ⟨p, hp, ?_⟩
  have hsub : S ⊆ expansions p w := by
    intro u hu
    have he := mem_expansions_of_reduce (hS u hu).2
    rw [(hS u hu).1] at he
    have : (L-w.length)/2 = p := by omega
    simpa only [this] using he
  exact (card_le_card hsub).trans (by simpa only [← hp] using card_expansions_le p w)

 

theorem normalized_reduction_fiber_bound (S : Finset (List (α × Bool)))
    (L : ℕ) (w : List (α × Bool))
    (hS : ∀ v ∈ S, v.length = L ∧ FreeGroup.reduce v = w)
    (hr : 0 < Fintype.card α) :
    (S.card : ℝ) / (Real.sqrt (Fintype.card α))^L ≤
      ((2 * (L+1) : ℕ)^L : ℝ) / (Real.sqrt (Fintype.card α))^w.length := by
  have hrreal : 0 < (Fintype.card α : ℝ) := by exact_mod_cast hr
  have hsqrt : 0 < Real.sqrt (Fintype.card α) := Real.sqrt_pos.mpr hrreal
  have hsqrt2 := Real.sq_sqrt hrreal.le
  by_cases hempty : S = ∅
  · simp only [hempty, card_empty, Nat.cast_zero, zero_div]
    positivity
  obtain ⟨p, hp, hb⟩ := reduction_fiber_bound S L w
    (Finset.nonempty_iff_ne_empty.mpr hempty) hS
  have hpL : p ≤ L := by omega
  have hconst : (2*L)^p ≤ (2*(L+1))^L :=
    (Nat.pow_le_pow_left (by omega) p).trans (Nat.pow_le_pow_right (by omega) hpL)
  have hcount : (S.card : ℝ) ≤ ((2*(L+1))^L : ℕ) * (Fintype.card α : ℝ)^p := by
    exact_mod_cast hb.trans (Nat.mul_le_mul_right _ hconst)
  have hpow : (Real.sqrt (Fintype.card α))^L =
      (Real.sqrt (Fintype.card α))^w.length * (Fintype.card α : ℝ)^p := by
    rw [hp, pow_add, pow_mul, hsqrt2]
  rw [hpow]
  apply (div_le_div_iff₀ (mul_pos (pow_pos hsqrt _) (pow_pos hrreal _))
    (pow_pos hsqrt _)).mpr
  calc
    _ ≤ (((2*(L+1))^L : ℕ) * (Fintype.card α : ℝ)^p) *
        (Real.sqrt (Fintype.card α))^w.length :=
      mul_le_mul_of_nonneg_right hcount (pow_nonneg hsqrt.le w.length)
    _ = _ := by push_cast; ring
end HochschildFreeWords
namespace HochschildFreeWords
open Finset
variable {α : Type*} [DecidableEq α] [Fintype α]
def allWords : ℕ → Finset (List (α × Bool))
  | 0 => {[]}
  | n+1 => ((univ : Finset (α × Bool)) ×ˢ allWords n).image
      (fun p => p.1 :: p.2)
omit [DecidableEq α] [Fintype α] in
lemma cons_pair_injective : Function.Injective (fun p : (α × Bool) × List (α × Bool) =>
    p.1 :: p.2) := by
  rintro ⟨a,l⟩ ⟨b,k⟩ h
  simp only [List.cons.injEq] at h
  exact Prod.ext h.1 h.2
lemma mem_allWords {w : List (α × Bool)} {n : ℕ} :
    w ∈ allWords n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [allWords]
  | succ n ih =>
    cases w with
    | nil => simp [allWords]
    | cons a l => simp [allWords, ih]
lemma card_allWords (n : ℕ) : (allWords (α := α) n).card =
    (2 * Fintype.card α)^n := by
  induction n with
  | zero => simp [allWords]
  | succ n ih =>
    rw [allWords, card_image_of_injective _ cons_pair_injective, card_product, ih]
    simp [pow_succ, Nat.mul_comm]
def badWords (n : ℕ) : Finset (List (α × Bool)) :=
  (allWords n).filter fun w => ¬ (w.map Prod.fst).Nodup
lemma mem_badWords {w : List (α × Bool)} {n : ℕ} :
    w ∈ badWords n ↔ w.length = n ∧ ¬ (w.map Prod.fst).Nodup := by
  simp [badWords, mem_allWords]
lemma card_badWords_one : (badWords (α := α) 1).card = 0 := by
  rw [card_eq_zero]
  apply eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hl, hn⟩ := mem_badWords.mp hw
  obtain ⟨a,rfl⟩ := List.length_eq_one_iff.mp hl
  simp at hn
lemma card_badWords_succ (n : ℕ) :
    (badWords (α := α) (n+1)).card ≤
      (2 * Fintype.card α) * (badWords (α := α) n).card +
      (2 * n) * (2 * Fintype.card α)^n := by
  let A := ((univ : Finset (α × Bool)) ×ˢ badWords n).image
    (fun p => p.1 :: p.2)
  let B := (allWords (α := α) n).biUnion fun w =>
    ((w.map Prod.fst).toFinset ×ˢ (univ : Finset Bool)).image fun p => p :: w
  have hsub : badWords (α := α) (n+1) ⊆ A ∪ B := by
    intro w hw
    obtain ⟨hl, hn⟩ := mem_badWords.mp hw
    cases w with
    | nil => simp at hl
    | cons a w =>
      have hwlen : w.length = n := by simpa using hl
      simp only [List.map_cons, List.nodup_cons, not_and_or] at hn
      rcases hn with hhead | htail
      · apply mem_union_right
        simp only [B, mem_biUnion, mem_image, mem_product, List.mem_toFinset,
          mem_univ, and_true]
        exact ⟨w, mem_allWords.mpr hwlen, a, by simpa only [not_not] using hhead, rfl⟩
      · apply mem_union_left
        simp only [A, mem_image, mem_product, mem_univ, true_and]
        exact ⟨(a,w), mem_badWords.mpr ⟨hwlen, htail⟩, rfl⟩
  have hA : A.card ≤ (2 * Fintype.card α) * (badWords (α := α) n).card := by
    exact card_image_le.trans (by simp [card_product, Nat.mul_comm])
  have hB : B.card ≤ (2*n) * (2 * Fintype.card α)^n := by
    apply card_biUnion_le.trans
    calc
      _ ≤ ∑ _w ∈ allWords (α := α) n, n*2 := by
        apply sum_le_sum
        intro w hw
        apply card_image_le.trans
        rw [card_product, card_univ, Fintype.card_bool]
        gcongr
        exact (List.toFinset_card_le _).trans_eq (by simpa using mem_allWords.mp hw)
      _ = _ := by simp [card_allWords, Nat.mul_comm]
  exact (card_le_card hsub).trans ((card_union_le A B).trans (Nat.add_le_add hA hB))
 
theorem card_badWords_le (n : ℕ) :
    (badWords (α := α) (n+1)).card ≤
      (n+1).choose 2 * 2^(n+1) * (Fintype.card α)^n := by
  induction n with
  | zero => simp [card_badWords_one]
  | succ n ih =>
    calc
      _ ≤ (2 * Fintype.card α) * (badWords (α := α) (n+1)).card +
          (2*(n+1)) * (2 * Fintype.card α)^(n+1) := card_badWords_succ (n+1)
      _ ≤ (2 * Fintype.card α) * ((n+1).choose 2 * 2^(n+1) * (Fintype.card α)^n) +
          (2*(n+1)) * (2 * Fintype.card α)^(n+1) := by gcongr
      _ = _ := by
        have hc : (n+1+1).choose 2 = (n+1) + (n+1).choose 2 := by
          exact Nat.choose_succ_succ (n+1) 1 |>.trans (by simp)
        rw [hc]
        simp only [mul_pow, pow_succ]
        ring
end HochschildFreeWords
end

end OAI
