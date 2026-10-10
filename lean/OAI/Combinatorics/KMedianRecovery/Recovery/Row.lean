import Mathlib

namespace OAI

namespace MetricKMedianRecovery.RationalLinearFeasibility

structure Row (n : ℕ) where
  coeff : Fin n → ℚ
  bound : ℚ

def Row.value {n : ℕ} (r : Row n) (x : Fin n → ℚ) : ℚ := ∑ i, r.coeff i * x i
noncomputable def Row.realValue {n : ℕ} (r : Row n) (x : Fin n → ℝ) : ℝ :=
  ∑ i, (r.coeff i : ℝ) * x i

def Row.Holds {n : ℕ} (r : Row n) (x : Fin n → ℚ) : Prop := r.value x ≤ r.bound
noncomputable def Row.RealHolds {n : ℕ} (r : Row n) (x : Fin n → ℝ) : Prop := r.realValue x ≤ r.bound
instance {n : ℕ} (r : Row n) (x : Fin n → ℚ) : Decidable (r.Holds x) := inferInstanceAs (Decidable (_ ≤ _))

def Row.head {n : ℕ} (r : Row (n+1)) : ℚ := r.coeff 0
def Row.tail {n : ℕ} (r : Row (n+1)) : Row n := ⟨fun i => r.coeff i.succ,r.bound⟩

def Row.combine {n : ℕ} (p q : Row (n+1)) : Row n :=
  ⟨fun i => -q.head*p.coeff i.succ+p.head*q.coeff i.succ,-q.head*p.bound+p.head*q.bound⟩

lemma Row.value_cons {n : ℕ} (r : Row (n+1)) (a : ℚ) (x : Fin n → ℚ) :
    r.value (Fin.cons a x) = r.head*a+r.tail.value x := by
  simp [Row.value,Row.head,Row.tail,Fin.sum_univ_succ]

lemma Row.realValue_cons {n : ℕ} (r : Row (n+1)) (a : ℝ) (x : Fin n → ℝ) :
    r.realValue (Fin.cons a x) = (r.head:ℝ)*a+r.tail.realValue x := by
  simp [Row.realValue,Row.head,Row.tail,Fin.sum_univ_succ]

lemma Row.combine_value {n : ℕ} (p q : Row (n+1)) (x : Fin n → ℚ) :
    (p.combine q).value x = -q.head*p.tail.value x+p.head*q.tail.value x := by
  simp only [Row.value,Row.combine,Row.tail,add_mul,Finset.sum_add_distrib,mul_assoc,Finset.mul_sum]

lemma Row.combine_realValue {n : ℕ} (p q : Row (n+1)) (x : Fin n → ℝ) :
    (p.combine q).realValue x = -(q.head:ℝ)*p.tail.realValue x+(p.head:ℝ)*q.tail.realValue x := by
  simp only [Row.realValue,Row.combine,Row.tail,Rat.cast_add,Rat.cast_mul,Rat.cast_neg,
    add_mul,Finset.sum_add_distrib,mul_assoc,Finset.mul_sum]

lemma Row.realHolds_cast {n : ℕ} (r : Row n) (x : Fin n → ℚ) :
    r.RealHolds (fun i => (x i : ℝ)) ↔ r.Holds x := by
  unfold Row.RealHolds Row.realValue Row.Holds Row.value
  dsimp only
  norm_cast

def eliminate {n : ℕ} (rows : List (Row (n+1))) : List (Row n) :=
  ((rows.filter (fun r => r.head = 0)).map Row.tail) ++
    (rows.filter (fun r => 0 < r.head)).flatMap
      (fun p => (rows.filter (fun r => r.head < 0)).map (Row.combine p))

lemma eliminate_sound {n : ℕ} (rows : List (Row (n+1))) (a : ℝ) (x : Fin n → ℝ)
    (h : ∀ r ∈ rows, r.RealHolds (Fin.cons a x)) :
    ∀ r ∈ eliminate rows, r.RealHolds x := by
  intro r hr
  simp only [eliminate,List.mem_append,List.mem_map,List.mem_filter,List.mem_flatMap,
    decide_eq_true_eq] at hr
  rcases hr with ⟨q,⟨hq,hzero⟩,rfl⟩ | ⟨p,⟨hp,hpos⟩,q,⟨hq,hneg⟩,rfl⟩
  · have hh := h q hq
    unfold Row.RealHolds at hh ⊢
    rw [Row.realValue_cons,hzero,Rat.cast_zero,zero_mul,zero_add] at hh
    exact hh
  · have hh := h p hp
    have hk := h q hq
    unfold Row.RealHolds at hh hk ⊢
    rw [Row.realValue_cons] at hh hk
    rw [Row.combine_realValue]
    change -(q.head:ℝ)*p.tail.realValue x+(p.head:ℝ)*q.tail.realValue x ≤
      ((-q.head*p.bound+p.head*q.bound : ℚ):ℝ)
    push_cast
    have hp' : (0:ℝ) < (p.head:ℝ) := Rat.cast_pos.mpr hpos
    have hq' : (q.head:ℝ) < 0 := Rat.cast_lt_zero.mpr hneg
    nlinarith [mul_le_mul_of_nonneg_left hh (neg_nonneg.mpr hq'.le),
      mul_le_mul_of_nonneg_left hk hp'.le]

def boundary {n : ℕ} (r : Row (n+1)) (x : Fin n → ℚ) : ℚ :=
  (r.bound-r.tail.value x)/r.head

def lowers {n : ℕ} (rows : List (Row (n+1))) (x : Fin n → ℚ) : List ℚ :=
  (rows.filter (fun r => r.head < 0)).map (fun r => boundary r x)
def uppers {n : ℕ} (rows : List (Row (n+1))) (x : Fin n → ℚ) : List ℚ :=
  (rows.filter (fun r => 0 < r.head)).map (fun r => boundary r x)

def pick (L U : List ℚ) : ℚ := L.foldr max (U.foldr min 0)

lemma le_foldr_max (L : List ℚ) (a b : ℚ) (hb : b ∈ L) : b ≤ L.foldr max a := by
  induction L with
  | nil => simp at hb
  | cons c L ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact le_max_left _ _
    · exact (ih hb).trans (le_max_right _ _)

lemma foldr_min_le (L : List ℚ) (a b : ℚ) (hb : b ∈ L) : L.foldr min a ≤ b := by
  induction L with
  | nil => simp at hb
  | cons c L ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hb)

lemma foldr_max_le (L : List ℚ) (a b : ℚ) (ha : a ≤ b) (h : ∀ c ∈ L, c ≤ b) :
    L.foldr max a ≤ b := by
  induction L with
  | nil => exact ha
  | cons c L ih => exact max_le (h c (List.mem_cons_self ..)) (ih (fun d hd => h d (List.mem_cons_of_mem _ hd)))

lemma pick_spec (L U : List ℚ) (h : ∀ l ∈ L, ∀ u ∈ U, l ≤ u) :
    (∀ l ∈ L, l ≤ pick L U) ∧ (∀ u ∈ U, pick L U ≤ u) := by
  constructor
  · intro l hl
    exact le_foldr_max L _ l hl
  · intro u hu
    exact foldr_max_le L _ u (foldr_min_le U 0 u hu) (fun l hl => h l hl u hu)

lemma boundary_order {n : ℕ} (p q : Row (n+1)) (x : Fin n → ℚ)
    (hp : 0 < p.head) (hq : q.head < 0) (h : (p.combine q).Holds x) :
    boundary q x ≤ boundary p x := by
  unfold Row.Holds at h
  rw [Row.combine_value] at h
  change -q.head*p.tail.value x+p.head*q.tail.value x ≤ -q.head*p.bound+p.head*q.bound at h
  unfold boundary
  apply (le_div_iff₀ hp).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff_of_neg hq).mpr
  nlinarith

lemma eliminate_complete {n : ℕ} (rows : List (Row (n+1))) (x : Fin n → ℚ)
    (h : ∀ r ∈ eliminate rows, r.Holds x) :
    ∀ r ∈ rows, r.Holds (Fin.cons (pick (lowers rows x) (uppers rows x)) x) := by
  have hord : ∀ l ∈ lowers rows x, ∀ u ∈ uppers rows x, l ≤ u := by
    intro l hl u hu
    simp only [lowers,uppers,List.mem_map,List.mem_filter,decide_eq_true_eq] at hl hu
    obtain ⟨q,⟨hq,hneg⟩,rfl⟩ := hl
    obtain ⟨p,⟨hp,hpos⟩,rfl⟩ := hu
    apply boundary_order p q x hpos hneg
    apply h
    simp only [eliminate,List.mem_append,List.mem_map,List.mem_filter,List.mem_flatMap,decide_eq_true_eq]
    exact Or.inr ⟨p,⟨hp,hpos⟩,q,⟨hq,hneg⟩,rfl⟩
  have hs := pick_spec (lowers rows x) (uppers rows x) hord
  intro r hr
  unfold Row.Holds
  rw [Row.value_cons]
  rcases lt_trichotomy r.head 0 with hn | hz | hp
  · have hh := hs.1 (boundary r x) (by simp only [lowers,List.mem_map,List.mem_filter,decide_eq_true_eq]; exact ⟨r,⟨hr,hn⟩,rfl⟩)
    unfold boundary at hh
    have hk := (div_le_iff_of_neg hn).mp hh
    nlinarith
  · have hh := h r.tail (by simp only [eliminate,List.mem_append,List.mem_map,List.mem_filter]; exact Or.inl ⟨r,⟨hr,by simpa using hz⟩,rfl⟩)
    simpa only [Row.Holds,Row.tail,hz,zero_mul,zero_add] using hh
  · have hh := hs.2 (boundary r x) (by simp only [uppers,List.mem_map,List.mem_filter,decide_eq_true_eq]; exact ⟨r,⟨hr,hp⟩,rfl⟩)
    unfold boundary at hh
    have hk := (le_div_iff₀ hp).mp hh
    nlinarith

def solve : (n : ℕ) → List (Row n) → Option (Fin n → ℚ)
  | 0, rows => if ∀ r ∈ rows, (0:ℚ) ≤ r.bound then some Fin.elim0 else none
  | n+1, rows => (solve n (eliminate rows)).map (fun x => Fin.cons (pick (lowers rows x) (uppers rows x)) x)

lemma solve_sound (n : ℕ) (rows : List (Row n)) (x : Fin n → ℚ) (h : solve n rows = some x) :
    ∀ r ∈ rows, r.Holds x := by
  induction n with
  | zero =>
    simp only [solve] at h
    split_ifs at h with hh
    · intro r hr
      simpa [Row.Holds,Row.value] using hh r hr
  | succ n ih =>
    simp only [solve,Option.map_eq_some_iff] at h
    obtain ⟨y,hy,rfl⟩ := h
    exact eliminate_complete rows y (ih (eliminate rows) y hy)

lemma solve_complete (n : ℕ) (rows : List (Row n)) (x : Fin n → ℝ)
    (h : ∀ r ∈ rows, r.RealHolds x) : ∃ y, solve n rows = some y := by
  induction n with
  | zero =>
    have hh : ∀ r ∈ rows, (0:ℚ) ≤ r.bound := by
      intro r hr
      have hh := h r hr
      simpa only [Row.RealHolds,Row.realValue,Finset.univ_eq_empty,Finset.sum_empty,Rat.cast_nonneg] using hh
    exact ⟨Fin.elim0,ite_eq_left hh⟩
  | succ n ih =>
    have hh : ∀ r ∈ eliminate rows, r.RealHolds (fun i => x i.succ) := by
      apply eliminate_sound rows (x 0)
      change ∀ r ∈ rows, r.RealHolds (Fin.cons (x 0) (Fin.tail x))
      simpa only [Fin.cons_self_tail] using h
    obtain ⟨y,hy⟩ := ih (eliminate rows) (fun i => x i.succ) hh
    refine ⟨Fin.cons (pick (lowers rows y) (uppers rows y)) y,?_⟩
    simp only [solve,hy,Option.map_some]

theorem rational_witness (n : ℕ) (rows : List (Row n)) :
    (∃ x : Fin n → ℝ, ∀ r ∈ rows, r.RealHolds x) ↔
      ∃ y : Fin n → ℚ, ∀ r ∈ rows, r.Holds y := by
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨y,hy⟩ := solve_complete n rows x hx
    exact ⟨y,solve_sound n rows y hy⟩
  · rintro ⟨y,hy⟩
    exact ⟨fun i => (y i:ℝ),fun r hr => (r.realHolds_cast y).mpr (hy r hr)⟩

end MetricKMedianRecovery.RationalLinearFeasibility

end OAI
