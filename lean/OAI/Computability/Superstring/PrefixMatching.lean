import OAI.Computability.Superstring.Tables

namespace OAI

namespace Superstring.PrefixGreedy
open BitCode
variable {α : Type} [Coded α]

@[fun_prop] theorem poly_prefer : Poly (fun q : Token α × Token α => prefer q.1 q.2) := by
  have hp : Poly (fun q : Token α × Token α => if less q.1.2.length q.2.2.length then q.2 else q.1) := by
    fun_prop
  simpa only [prefer, less, decide_eq_true_eq] using hp

@[fun_prop] theorem poly_largest : Poly (largest : List (Token α) → Token α) := by
  have hs : ∀ a b : Token α, bitSize (prefer a b) ≤ bitSize a +
      (Polynomial.X : Polynomial ℕ).eval (bitSize b) := by
    intro a b
    unfold prefer
    split <;> simp only [Polynomial.eval_X] <;> omega
  have hf := BitCode.Poly.foldl_additive poly_prefer Polynomial.X hs
  exact hf.comp (BitCode.Poly.id.pair (BitCode.Poly.headD (0,[])))

variable [DecidableEq α]

@[fun_prop] theorem poly_prefixB : Poly (fun q : List α × List α => prefixB q.1 q.2) := by
  have hp : Poly (fun q : List α × List α => equal q.1 (q.2.take q.1.length)) := by fun_prop
  convert hp using 1
  funext q
  apply Bool.eq_iff_iff.mpr
  simp only [prefixB, equal, decide_eq_true_eq, List.prefix_iff_eq_take]

@[fun_prop] theorem poly_remove : Poly (fun q : Token α × List (Token α) => remove q.1 q.2) := by
  have hp := BitCode.Poly.filterFn (p := fun q : (Token α × List (Token α)) × Token α =>
    !(equal q.2 q.1.1)) (by fun_prop) (BitCode.Poly.snd : Poly (Prod.snd : Token α × List (Token α) → _))
  convert hp using 1
  funext q
  simp only [remove, equal, decide_not]

@[fun_prop] theorem poly_extension : Poly (fun q : Token α × List (Token α) => extension q.1 q.2) := by
  unfold extension
  exact (BitCode.Poly.headD (0,[])).comp (BitCode.Poly.filterFn
    (p := fun q : (Token α × List (Token α)) × Token α => prefixB q.1.1.2 q.2.2)
    (by fun_prop) BitCode.Poly.snd)

@[fun_prop] theorem poly_step : Poly (step : State α → State α) := by
  unfold step
  fun_prop

omit [DecidableEq α] in
theorem largest_size {R : List (Token α)} (hR : R ≠ []) : bitSize (largest R) ≤ bitSize R :=
  bitSize_mem (largest_spec R hR).1

theorem extension_size (a : Token α) (S : List (Token α)) :
    bitSize (extension a S) ≤ bitSize S + 2 := by
  have hb : ∀ xs : List (Token α), bitSize (xs.headD (0,[])) ≤ bitSize xs + 2 := by
    intro xs
    cases xs with
    | nil => simp
    | cons x xs => simp only [List.headD_cons, bitSize_cons]; omega
  have hh := hb (S.filter (fun b => prefixB a.2 b.2))
  have hm := bitSize_sublist (List.filter_sublist (p := fun b => prefixB a.2 b.2) (l := S))
  exact le_trans hh (Nat.add_le_add_right hm 2)

theorem step_bounds (q : State α) :
    bitSize (step q).1 + bitSize (step q).2.1 ≤ bitSize q.1 + bitSize q.2.1 ∧
    bitSize (step q).2.2 ≤ bitSize q.2.2 + (bitSize q.1 + bitSize q.2.1 + 3) := by
  by_cases he : q.1.isEmpty = true
  · simp only [step, he, ite_true]
    omega
  · have hne : q.1 ≠ [] := by simpa only [List.isEmpty_iff] using he
    have ha := largest_size hne
    have hb := extension_size (largest q.1) q.2.1
    have hr := bitSize_sublist (List.filter_sublist (p := fun b => decide (b ≠ largest q.1)) (l := q.1))
    have hs := bitSize_sublist (List.filter_sublist (p := fun b => decide (b ≠ extension (largest q.1) q.2.1)) (l := q.2.1))
    simp only [step, he, Bool.false_eq_true, ite_false, bitSize_cons, bitSize_prod, remove]
    constructor <;> omega

theorem iterate_size (q : State α) (n : ℕ) :
    bitSize (step^[n] q).1 + bitSize (step^[n] q).2.1 ≤ bitSize q.1 + bitSize q.2.1 ∧
    bitSize (step^[n] q).2.2 ≤ bitSize q.2.2 + n * (bitSize q.1 + bitSize q.2.1 + 3) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have hh := step_bounds (step^[n] q)
    constructor
    · exact hh.1.trans ih.1
    · rw [Nat.succ_mul]
      omega

@[fun_prop] theorem poly_iterate : Poly (fun q : ℕ × State α => step^[q.1] q.2) := by
  apply BitCode.Poly.iterate poly_step (Polynomial.X * Polynomial.X + 4 * Polynomial.X + 4)
  intro n q j hj
  have h := iterate_size q j
  rcases q with ⟨R,S,P⟩
  have ht : bitSize (step^[j] (R,S,P)) ≤
      bitSize R + bitSize S + bitSize P + j * (bitSize R + bitSize S + 3) := by
    generalize he : step^[j] (R,S,P) = z at *
    rcases z with ⟨R',S',P'⟩
    simp only [bitSize_prod]
    dsimp only at h
    omega
  simp only [bitSize_prod, bitSize_nat, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_ofNat]
  have hjn : j ≤ n := by omega
  have hm := Nat.mul_le_mul_right (bitSize R + bitSize S + 3) hjn
  nlinarith

def compute (R S : List (Token α)) : List (Token α × Token α) :=
  (step^[R.length] (R,S,[])).2.2

@[fun_prop] theorem poly_compute : Poly (fun q : List (Token α) × List (Token α) => compute q.1 q.2) := by
  unfold compute
  exact (BitCode.Poly.snd.comp BitCode.Poly.snd).comp
    (poly_iterate.comp (BitCode.Poly.length.comp BitCode.Poly.fst |>.pair
      (BitCode.Poly.fst.pair (BitCode.Poly.snd.pair (BitCode.Poly.const [])))))

omit [Coded α] in
theorem compute_correct (R S : List (Token α)) (hR : R.Nodup) (hS : S.Nodup)
    (hc : Capacity Prod.snd Prod.snd R.toFinset S.toFinset) (hl : R.length = S.length) :
    ((compute R S).map Prod.fst).Perm R ∧ ((compute R S).map Prod.snd).Perm S ∧
      ∀ p ∈ compute R S, p.1.2 <+: p.2.2 := by
  have h := iterate_correct R.length R S [] hR hS hc hl le_rfl (by simp)
  simpa only [compute, List.map_nil, List.append_nil] using h.2.2

end Superstring.PrefixGreedy

end OAI
