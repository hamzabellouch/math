import OAI.Computability.Superstring.GroupSupply

namespace OAI

namespace Superstring.BitCode
variable {α : Type} [Inhabited α] [DecidableEq α]
def lexLT (lt : α × α → Bool) (v w : List α) : Bool :=
  (equal v (w.take v.length) && less v.length w.length) ||
    (List.range (min v.length w.length)).any (fun i =>
      equal (v.take i) (w.take i) && lt (v[i]?.getD default,w[i]?.getD default))

omit [Inhabited α] [DecidableEq α] in
theorem take_eq_iff {v w : List α} {i : ℕ} (hv : i ≤ v.length) (hw : i ≤ w.length) :
    v.take i = w.take i ↔ ∀ j, (hj : j < i) → v[j]'(by omega) = w[j]'(by omega) := by
  constructor
  · intro he j hj
    have hh := congrArg (fun u => u[j]?) he
    simpa only [List.getElem?_take,ite_eq_left hj,List.getElem?_eq_getElem (by omega : j<v.length),
      List.getElem?_eq_getElem (by omega : j<w.length),Option.some.injEq] using hh
  · intro he
    apply List.ext_getElem
    · simp [List.length_take, Nat.min_eq_left hv,Nat.min_eq_left hw]
    · intro j hj hj'
      have hji : j < i := lt_of_lt_of_le hj (List.length_take_le _ _)
      simp only [List.getElem_take,he j hji]

theorem lexLT_eq [LinearOrder α] (lt : α × α → Bool)
    (hlt : ∀ x, lt x = decide (x.1<x.2)) (v w : List α) :
    lexLT lt v w = true ↔ v<w := by
  rw [List.lt_iff_exists]
  simp only [lexLT,Bool.or_eq_true,Bool.and_eq_true,equal,less,decide_eq_true_eq,
    List.any_eq_true,List.mem_range]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨i,hi,he,hlt'⟩
    have hv : i<v.length := lt_of_lt_of_le hi (Nat.min_le_left ..)
    have hw : i<w.length := lt_of_lt_of_le hi (Nat.min_le_right ..)
    refine ⟨i,hv,hw,(take_eq_iff hv.le hw.le).mp he,?_⟩
    simpa only [hlt,List.getElem?_eq_getElem hv,List.getElem?_eq_getElem hw,
      Option.getD_some,decide_eq_true_eq] using hlt'
  · rintro ⟨i,hv,hw,he,hl⟩
    refine ⟨i,lt_min hv hw,(take_eq_iff hv.le hw.le).mpr he,?_⟩
    simpa only [hlt,List.getElem?_eq_getElem hv,List.getElem?_eq_getElem hw,
      Option.getD_some,decide_eq_true_eq] using hl

variable [Coded α]
@[fun_prop] theorem poly_lexLT {lt : α × α → Bool} (hlt : Poly lt) :
    Poly (fun q : List α × List α => lexLT lt q.1 q.2) := by
  unfold lexLT
  apply Poly.or.comp (f := fun q : List α × List α =>
    (equal q.1 (q.2.take q.1.length) && less q.1.length q.2.length,
    (List.range (min q.1.length q.2.length)).any (fun i =>
      equal (q.1.take i) (q.2.take i) && lt (q.1[i]?.getD default,q.2[i]?.getD default))))
  apply Poly.pair (by fun_prop)
  apply Poly.anyFn (p := fun q : (List α × List α) × ℕ =>
    equal (q.1.1.take q.2) (q.1.2.take q.2) && lt (q.1.1[q.2]?.getD default,q.1.2[q.2]?.getD default))
  · apply Poly.and.comp (f := fun q : (List α × List α) × ℕ =>
      (equal (q.1.1.take q.2) (q.1.2.take q.2),lt (q.1.1[q.2]?.getD default,q.1.2[q.2]?.getD default)))
    apply Poly.pair (by fun_prop)
    apply hlt.comp
    exact ((Poly.getD default).comp (f := fun q : (List α × List α) × ℕ => (q.1.1,q.2)) (by fun_prop)).pair
      ((Poly.getD default).comp (f := fun q : (List α × List α) × ℕ => (q.1.2,q.2)) (by fun_prop))
  · fun_prop

@[fun_prop] theorem Poly.ltBool : Poly (fun q : Bool × Bool => decide (q.1 < q.2)) := by
  have h : Poly (fun q : Bool × Bool => !q.1 && q.2) := by fun_prop
  convert h using 1
  funext q
  rcases q with ⟨a,b⟩
  cases a <;> cases b <;> rfl

@[fun_prop] theorem Poly.ltList [LinearOrder α] (h : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (fun q : List α × List α => decide (q.1<q.2)) := by
  convert poly_lexLT h using 1
  funext q
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using (lexLT_eq _ (fun _ => rfl) q.1 q.2).symm

@[fun_prop] theorem Poly.leList [LinearOrder α] (h : Poly (fun q : α × α => decide (q.1<q.2))) :
    Poly (fun q : List α × List α => decide (q.1≤q.2)) := by
  have H := Poly.not.comp ((Poly.ltList h).comp (Poly.snd.pair Poly.fst))
  convert H using 1
  funext q
  simp only [Function.comp_apply,← decide_not,not_lt]
end Superstring.BitCode


namespace Superstring.RotationCode
open BitCode Hierarchical
variable {α : Type} [Inhabited α] [LinearOrder α]

omit [Inhabited α] [LinearOrder α] in
theorem forward_mod {A : ℤ → α} {p : ℕ} (per : Function.Periodic A (p:ℤ)) (t : ℤ) (n : ℕ) :
    forward A t (n % p) = forward A t n := by
  have hh := periodic_emod (fun x => A (t+x)) (p:ℤ)
    (by intro x; simpa only [← add_assoc] using per (t+x)) (n:ℤ)
  simpa only [forward, Pi.toLex_apply, Int.natCast_emod] using hh

omit [Inhabited α] in
theorem window_lt_iff {A : ℤ → α} {p : ℕ} (hp : 0 < p)
    (per : Function.Periodic A (p:ℤ)) (a b : ℤ) :
    textWord A a (a+p) < textWord A b (b+p) ↔ forward A a < forward A b := by
  have hlen (t : ℤ) : (textWord A t (t+p)).length = p := by simp [length_textWord]
  rw [List.lt_iff_exists]
  constructor
  · rintro (⟨_,hh⟩|⟨i,hi,hj,he,hl⟩)
    · simp only [hlen,lt_self_iff_false] at hh
    · refine ⟨i,?_,?_⟩
      · intro j hj
        have hh := he j hj
        simpa only [textWord,List.getElem_ofFn,forward,Pi.toLex_apply] using hh
      · simpa only [textWord,List.getElem_ofFn,forward,Pi.toLex_apply] using hl
  · rintro ⟨i,he,hl⟩
    have hi : i < p := by
      by_contra hn
      have hm : i%p < i := lt_of_lt_of_le (Nat.mod_lt i hp) (by omega)
      have hh := he (i%p) hm
      rw [forward_mod per,forward_mod per] at hh
      exact (ne_of_lt hl) hh
    right
    refine ⟨i,by simpa only [hlen] using hi,by simpa only [hlen] using hi,?_,?_⟩
    · intro j hj
      simpa only [textWord,List.getElem_ofFn,forward,Pi.toLex_apply] using he j hj
    · simpa only [textWord,List.getElem_ofFn,forward,Pi.toLex_apply] using hl

omit [Inhabited α] in
theorem window_le_iff {A : ℤ → α} {p : ℕ} (hp : 0 < p)
    (per : Function.Periodic A (p:ℤ)) (a b : ℤ) :
    textWord A a (a+p) ≤ textWord A b (b+p) ↔ forward A a ≤ forward A b := by
  rw [← not_lt,← not_lt,window_lt_iff hp per]
  rfl

def phase (U : List α) : ℕ :=
  ThreadArray.first U.length (fun i => (List.range U.length).all (fun j =>
    decide (PeriodWord.window U j ((j:ℤ)+U.length) ≤ PeriodWord.window U i ((i:ℤ)+U.length))))

theorem phase_spec (U : List α) (hp : 0 < U.length) :
    phase U < U.length ∧ ∀ x, forward (PeriodWord.text U) x ≤ forward (PeriodWord.text U) (phase U) := by
  obtain ⟨t,ht0,htp,ht⟩ := exists_greatest_rotation (PeriodWord.text U) U.length hp (PeriodWord.periodic U)
  have hpref (x y : ℤ) : PeriodWord.window U x (x+U.length) ≤ PeriodWord.window U y (y+U.length) ↔
      forward (PeriodWord.text U) x ≤ forward (PeriodWord.text U) y := by
    simp only [PeriodWord.window_eq,window_le_iff hp (PeriodWord.periodic U)]
  have hex : ∃ i < U.length, (List.range U.length).all (fun j =>
      decide (PeriodWord.window U j ((j:ℤ)+U.length) ≤ PeriodWord.window U i ((i:ℤ)+U.length))) = true := by
    refine ⟨t.toNat,by omega,List.all_eq_true.mpr (fun j _ => ?_)⟩
    apply decide_eq_true
    apply (hpref _ _).mpr
    simpa only [Int.toNat_of_nonneg ht0] using ht j
  have hs := ThreadArray.first_spec hex
  refine ⟨hs.1,?_⟩
  intro x
  let r := (x % (U.length:ℤ)).toNat
  have hrlt : r < U.length := by
    have := Int.emod_nonneg x (show (U.length:ℤ) ≠ 0 by omega)
    have := Int.emod_lt_of_pos x (show (0:ℤ) < U.length by omega)
    dsimp only [r]; omega
  have hle := List.all_eq_true.mp hs.2.1 r (List.mem_range.mpr hrlt)
  have hh := (hpref _ _).mp (of_decide_eq_true hle)
  have he : forward (PeriodWord.text U) x = forward (PeriodWord.text U) r := by
    apply congrArg toLex
    funext n
    have hr : (r:ℤ) = x % (U.length:ℤ) := by
      exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
    have hdiv := Int.emod_add_ediv_mul x (U.length:ℤ)
    have hh := (PeriodWord.periodic U).sub_int_mul_eq (x := x+n) (x/U.length)
    simp only [Int.cast_id] at hh
    have hx : x+n-(x/(U.length:ℤ))*U.length = (r:ℤ)+n := by omega
    rw [hx] at hh
    exact hh.symm
  rw [he]
  exact hh

variable [Coded α]
@[fun_prop] theorem poly_phase (hlt : Poly (fun q : α × α => decide (q.1<q.2))) : Poly (phase (α := α)) := by
  have hle := BitCode.Poly.leList hlt
  unfold phase ThreadArray.first
  apply (BitCode.Poly.headD 0).comp
  apply BitCode.Poly.filterFn
    (p := fun t : List α × ℕ => (List.range t.1.length).all (fun j =>
      decide (PeriodWord.window t.1 j ((j:ℤ)+t.1.length) ≤ PeriodWord.window t.1 t.2 ((t.2:ℤ)+t.1.length))))
  · apply BitCode.Poly.allFn
      (p := fun t : (List α × ℕ) × ℕ =>
        decide (PeriodWord.window t.1.1 t.2 ((t.2:ℤ)+t.1.1.length) ≤
          PeriodWord.window t.1.1 t.1.2 ((t.1.2:ℤ)+t.1.1.length)))
    · exact hle.comp (f := fun t : (List α × ℕ) × ℕ =>
        (PeriodWord.window t.1.1 t.2 ((t.2:ℤ)+t.1.1.length),
          PeriodWord.window t.1.1 t.1.2 ((t.1.2:ℤ)+t.1.1.length))) (by fun_prop)
    · fun_prop
  · fun_prop
end Superstring.RotationCode


namespace Superstring.RotationCode
open BitCode Hierarchical
variable {α : Type} [LinearOrder α]
theorem maximal_unique {A : ℤ → α} {p : ℕ} (h : Primitive A p)
    {a b : ℤ} (ha : 0 ≤ a) (hap : a < p) (hb : 0 ≤ b) (hbp : b < p)
    (hA : ∀ x, forward A x ≤ forward A a) (hB : ∀ x, forward A x ≤ forward A b) : a = b := by
  have he : forward A a = forward A b := le_antisymm (hB a) (hA b)
  have he' : (fun x => A (x+a)) = (fun x => A (x+b)) := by
    apply periodic_eq_of_forward_eq _ _ p p h.positive h.positive
      (fun x => by simpa only [add_right_comm] using h.periodic (x+a))
      (fun x => by simpa only [add_right_comm] using h.periodic (x+b)) 0
    simpa only [forward_shift,zero_add] using he
  exact h.alignment_unique ha hap hb hbp (congrFun he')

variable [Inhabited α]
theorem phase_eq_distinguished {G : Type} {V : Set (List α)}
    (C : LayerCollection V G) (g : G) (hprim : Primitive (C.text g) (C.period g))
    (U : List α) (hlen : U.length = C.period g) (ht : PeriodWord.text U = C.text g) :
    (phase U : ℤ) = C.distinguished g := by
  obtain ⟨hp,hm⟩ := phase_spec U (by rw [hlen]; exact C.positive g)
  have hs := (exists_greatest_rotation (C.text g) (C.period g) (C.positive g) (C.periodic g)).choose_spec
  apply maximal_unique hprim (by omega) (by omega) hs.1 hs.2.1
  · simpa only [ht] using hm
  · exact C.distinguished_max g
end Superstring.RotationCode

end OAI
