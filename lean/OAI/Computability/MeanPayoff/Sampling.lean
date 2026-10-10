import OAI.Computability.MeanPayoff.Budgets

namespace OAI

section

namespace MeanPayoff
namespace RandomTree
open scoped Classical

theorem badCount_eq_countP {α : Type} (P : α → Prop) (as : List α) :
    badCount P as = as.countP (fun a => decide (¬P a)) := by
  induction as with
  | nil => rfl
  | cons a as ha => by_cases h : P a <;> simp [badCount, h, ha, Nat.add_comm]

theorem badCount_perm {α : Type} (P : α → Prop) {as bs : List α} (h : as.Perm bs) :
    badCount P as = badCount P bs := by
  simpa only [badCount_eq_countP] using h.countP_eq (fun a => decide (¬P a))

theorem badCount_sublist {α : Type} (P : α → Prop) {as bs : List α} (h : as.Sublist bs) :
    badCount P as ≤ badCount P bs := by
  simpa only [badCount_eq_countP] using
    (h.countP_le (p := fun a => decide (¬P a)))

theorem badCount_eq_length {α : Type} (P : α → Prop) (as : List α)
    (h : ∀ a ∈ as, ¬P a) : badCount P as = as.length := by
  rw [badCount_eq_countP, List.countP_eq_length]
  simpa using h

theorem badCount_map_le {α β : Type} (f : α → β) (P : α → Prop) (Q : β → Prop)
    (h : ∀ a, P a → Q (f a)) (as : List α) : badCount Q (as.map f) ≤ badCount P as := by
  induction as with
  | nil => rfl
  | cons a as ha =>
    by_cases hp : P a <;> by_cases hq : Q (f a) <;> simp_all [badCount] ; omega

end RandomTree

def medianInt (as : List ℤ) : ℤ :=
  if h : 0 < as.length then
    (as.mergeSort (· ≤ ·))[as.length / 2]'(by
      simpa only [List.length_mergeSort] using Nat.div_lt_self h (by norm_num))
  else 0

def median {V : Type} (as : List (Vec V)) : Vec V :=
  fun i => medianInt (as.map (fun p => p i))

theorem medianInt_mem {as : List ℤ} (ha : 0 < as.length) : medianInt as ∈ as := by
  rw [medianInt, dite_eq_left ha]
  exact (List.mergeSort_perm as (· ≤ ·)).mem_iff.mp (List.getElem_mem _)

theorem median_inBox {V : Type} {as : List (Vec V)} {a b : Vec V}
    (ha : 0 < as.length) (h : ∀ p ∈ as, InBox a b p) : InBox a b (median as) := by
  constructor
  · intro i
    obtain ⟨p, hp, he⟩ := List.mem_map.mp (medianInt_mem (by simpa using ha :
      0 < (as.map (fun p => p i)).length))
    rw [median, ← he]
    exact (h p hp).1 i
  · intro i
    obtain ⟨p, hp, he⟩ := List.mem_map.mp (medianInt_mem (by simpa using ha :
      0 < (as.map (fun p => p i)).length))
    rw [median, ← he]
    exact (h p hp).2 i

open RandomTree in
 theorem medianInt_lower_failure {as : List ℤ} {y : ℤ} (ha : 0 < as.length)
    (hf : medianInt as < y) : as.length ≤ 2 * badCount (fun a => y ≤ a) as := by
  let bs := as.mergeSort (· ≤ ·)
  have hlen : bs.length = as.length := List.length_mergeSort as
  have hk : as.length / 2 < bs.length := by rw [hlen]; exact Nat.div_lt_self ha (by norm_num)
  have hsort : bs.SortedLE := List.sortedLE_mergeSort
  have hf' : bs[as.length / 2] < y := by simpa only [medianInt, dite_eq_left ha] using hf
  have hbad : badCount (fun a => y ≤ a) (bs.take (as.length / 2 + 1)) = as.length / 2 + 1 := by
    rw [badCount_eq_length]
    · simp only [List.length_take, hlen]
      omega
    · intro a hm
      obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.mp hm
      have hle : bs[j] ≤ bs[as.length / 2] :=
        hsort.getElem_le_getElem_of_le (by omega)
      omega
  have hm := badCount_sublist (fun a => y ≤ a) (List.take_sublist (as.length / 2 + 1) bs)
  rw [hbad, badCount_perm _ (List.mergeSort_perm as (· ≤ ·))] at hm
  omega

open RandomTree in
 theorem medianInt_upper_failure {as : List ℤ} {z : ℤ} (ha : 0 < as.length)
    (hf : z < medianInt as) : as.length ≤ 2 * badCount (fun a => a ≤ z) as := by
  let bs := as.mergeSort (· ≤ ·)
  have hlen : bs.length = as.length := List.length_mergeSort as
  have hk : as.length / 2 < bs.length := by rw [hlen]; exact Nat.div_lt_self ha (by norm_num)
  have hsort : bs.SortedLE := List.sortedLE_mergeSort
  have hf' : z < bs[as.length / 2] := by simpa only [medianInt, dite_eq_left ha] using hf
  have hbad : badCount (fun a => a ≤ z) (bs.drop (as.length / 2)) = as.length - as.length / 2 := by
    rw [badCount_eq_length]
    · simp only [List.length_drop, hlen]
    · intro a hm
      obtain ⟨j, hj, rfl⟩ := List.mem_drop_iff_getElem.mp hm
      have hle : bs[as.length / 2] ≤ bs[as.length / 2 + j] :=
        hsort.getElem_le_getElem_of_le (by omega)
      omega
  have hm := badCount_sublist (fun a => a ≤ z) (List.drop_sublist (as.length / 2) bs)
  rw [hbad, badCount_perm _ (List.mergeSort_perm as (· ≤ ·))] at hm
  omega

open RandomTree in
 theorem median_lower_failure {V : Type} {as : List (Vec V)} {y : Vec V}
    (ha : 0 < as.length) (hf : ¬ y ≤ median as) :
    as.length ≤ 2 * badCount (fun p => y ≤ p) as := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, median as i < y i := by
    simpa only [Pi.le_def, not_forall, not_le] using hf
  have hm := medianInt_lower_failure (by simpa : 0 < (as.map (fun p => p i)).length) hi
  have hb := badCount_map_le (fun p : Vec V => p i) (fun p => y ≤ p)
    (fun a => y i ≤ a) (fun p hp => hp i) as
  simp only [List.length_map] at hm
  omega

open RandomTree in
 theorem median_upper_failure {V : Type} {as : List (Vec V)} {z : Vec V}
    (ha : 0 < as.length) (hf : ¬ median as ≤ z) :
    as.length ≤ 2 * badCount (fun p => p ≤ z) as := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, z i < median as i := by
    simpa only [Pi.le_def, not_forall, not_le] using hf
  have hm := medianInt_upper_failure (by simpa : 0 < (as.map (fun p => p i)).length) hi
  have hb := badCount_map_le (fun p : Vec V => p i) (fun p => p ≤ z)
    (fun a => a ≤ z i) (fun p hp => hp i) as
  simp only [List.length_map] at hm
  omega

end MeanPayoff

namespace MeanPayoff
namespace RandomTree

theorem probability_map {α β : Type} (t : RandomTree α) (f : α → β) (P : β → Prop) :
    (t.map f).probability P = t.probability (fun a => P (f a)) := by
  classical
  simp only [probability, expect_map, Function.comp_def]

theorem probability_mono_all {α : Type} (t : RandomTree α) {P Q : α → Prop}
    (h : t.All (fun a => P a → Q a)) : t.probability P ≤ t.probability Q := by
  classical
  apply expect_mono_all
  apply all_mono _ h
  intro a ha
  by_cases hp : P a <;> by_cases hq : Q a <;> simp_all

theorem probability_union {α : Type} (t : RandomTree α) (P Q : α → Prop) :
    t.probability (fun a => P a ∨ Q a) ≤ t.probability P + t.probability Q := by
  classical
  unfold probability
  rw [← expect_add]
  apply expect_mono
  intro a
  by_cases hp : P a <;> by_cases hq : Q a <;> norm_num [hp, hq]

theorem probability_of_all_not {α : Type} (t : RandomTree α) (P : α → Prop)
    (h : t.All (fun a => ¬P a)) : t.probability P = 0 := by
  apply le_antisymm _ (probability_nonneg _ _)
  classical
  have := expect_mono_all t (fun a => if P a then 1 else 0) (fun _ => 0)
    (all_mono _ h (fun a ha => by simp [ha]))
  simpa only [probability, expect_const] using this

def ask {V : Type} (t : RandomTree (Vec V)) (J : ℕ) : RandomTree (Vec V) :=
  (trials t J).map median

theorem ask_lower {V : Type} (t : RandomTree (Vec V)) {y : Vec V}
    (h : t.probability (fun p => ¬ y ≤ p) ≤ 1 / 16) {J : ℕ} (hJ : 0 < J) :
    (ask t J).probability (fun p => ¬ y ≤ p) ≤ (1 / 2 : ℚ) ^ J := by
  rw [ask, probability_map]
  apply le_trans _ (amplification t (fun p => y ≤ p) h J)
  apply probability_mono_all
  apply all_mono _ (trials_length t J)
  intro as has hf
  rw [← has]
  exact median_lower_failure (by omega) hf

theorem ask_upper {V : Type} (t : RandomTree (Vec V)) {z : Vec V}
    (h : t.probability (fun p => ¬ p ≤ z) ≤ 1 / 16) {J : ℕ} (hJ : 0 < J) :
    (ask t J).probability (fun p => ¬ p ≤ z) ≤ (1 / 2 : ℚ) ^ J := by
  rw [ask, probability_map]
  apply le_trans _ (amplification t (fun p => p ≤ z) h J)
  apply probability_mono_all
  apply all_mono _ (trials_length t J)
  intro as has hf
  rw [← has]
  exact median_upper_failure (by omega) hf

theorem trials_all {α : Type} (t : RandomTree α) {P : α → Prop}
    (h : t.All P) (J : ℕ) : (trials t J).All (fun as => ∀ a ∈ as, P a) := by
  induction J with
  | zero => simp [trials, All]
  | succ j hj =>
    rw [trials, all_bind]
    apply all_mono _ h
    intro a ha
    rw [map, all_bind]
    apply all_mono _ hj
    intro as has
    simpa [All] using (show ∀ b ∈ a :: as, P b by simp_all)

theorem all_and {α : Type} (t : RandomTree α) {P Q : α → Prop}
    (hp : t.All P) (hq : t.All Q) : t.All (fun a => P a ∧ Q a) := by
  induction t with
  | leaf a => exact ⟨hp, hq⟩
  | coin l r hl hr => exact ⟨hl hp.1 hq.1, hr hp.2 hq.2⟩

theorem ask_inBox {V : Type} (t : RandomTree (Vec V)) {a b : Vec V}
    (h : t.All (InBox a b)) {J : ℕ} (hJ : 0 < J) : (ask t J).All (InBox a b) := by
  rw [ask, map, all_bind]
  apply all_mono _ (all_and _ (trials_length t J) (trials_all t h J))
  intro as ha
  exact median_inBox (by omega) ha.2

end RandomTree


def globalG (Bmax : ℕ) : ℕ := 1 + Nat.clog 2 (Bmax + 1)
def sampleExponent (Bmax : ℕ) : ℕ := Nat.clog 2 (2 ^ 17 * (globalG Bmax + 1))
def globalS (Bmax : ℕ) : ℕ := 2 ^ sampleExponent Bmax
def globalJ (n Bmax : ℕ) : ℕ := 2 * (globalS Bmax * (n + 1)) ^ 6 + 1

theorem globalS_lower (Bmax : ℕ) : 2 ^ 17 * (globalG Bmax + 1) ≤ globalS Bmax :=
  Nat.le_pow_clog (by norm_num) _

theorem globalS_minimal (Bmax j : ℕ) (h : 2 ^ 17 * (globalG Bmax + 1) ≤ 2 ^ j) :
    globalS Bmax ≤ 2 ^ j := by
  apply Nat.pow_le_pow_right (by norm_num)
  exact (Nat.clog_le_iff_le_pow (by norm_num)).mpr h

theorem globalS_large (Bmax : ℕ) : 16 ≤ globalS Bmax := by
  have h := globalS_lower Bmax
  have hg : 1 ≤ globalG Bmax := by unfold globalG; omega
  norm_num at h
  omega

theorem globalJ_positive (n Bmax : ℕ) : 0 < globalJ n Bmax := by unfold globalJ; omega

theorem globalJ_odd (n Bmax : ℕ) : Odd (globalJ n Bmax) := by
  exact ⟨(globalS Bmax * (n + 1)) ^ 6, by unfold globalJ; omega⟩

structure SolveBox (n Bmax : ℕ) where
  a : Vec (Fin n)
  b : Vec (Fin n)
  ordered : a ≤ b
  width : ℕ
  positive : 0 < width
  bounded : width ≤ Bmax
  width_bound : ∀ i, b i - a i ≤ (width : ℤ)

abbrev BoxVector {n Bmax : ℕ} (I : SolveBox n Bmax) := {p : Vec (Fin n) // InBox I.a I.b p}

namespace SolveBox

def bottom {n Bmax : ℕ} (I : SolveBox n Bmax) : BoxVector I := ⟨I.a, le_refl _, I.ordered⟩
def top {n Bmax : ℕ} (I : SolveBox n Bmax) : BoxVector I := ⟨I.b, I.ordered, le_refl _⟩

def medianBox {n Bmax : ℕ} (I : SolveBox n Bmax) (as : List (BoxVector I)) : BoxVector I :=
  if h : 0 < as.length then
    ⟨median (as.map Subtype.val), median_inBox (by simpa using h) (by
      intro p hp
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hp
      exact r.property)⟩
  else I.bottom

def repeated {n Bmax : ℕ} (I : SolveBox n Bmax) (t : RandomTree (BoxVector I))
    (J : ℕ) : RandomTree (BoxVector I) := (RandomTree.trials t J).map I.medianBox

theorem repeated_lower {n Bmax : ℕ} (I : SolveBox n Bmax)
    (t : RandomTree (BoxVector I)) {y : Vec (Fin n)}
    (h : t.probability (fun p => ¬y ≤ p.val) ≤ 1 / 16) {J : ℕ} (hJ : 0 < J) :
    (I.repeated t J).probability (fun p => ¬y ≤ p.val) ≤ (1 / 2 : ℚ) ^ J := by
  rw [repeated, RandomTree.probability_map]
  apply le_trans _ (RandomTree.amplification t (fun p => y ≤ p.val) h J)
  apply RandomTree.probability_mono_all
  apply RandomTree.all_mono _ (RandomTree.trials_length t J)
  intro as has hf
  have hlen : 0 < as.length := by omega
  simp only [medianBox, dite_eq_left hlen] at hf
  have hm := median_lower_failure (by simpa using hlen : 0 < (as.map Subtype.val).length) hf
  have hc := RandomTree.badCount_map_le Subtype.val (fun p : BoxVector I => y ≤ p.val)
    (fun p => y ≤ p) (fun _ hp => hp) as
  simp only [List.length_map] at hm
  omega

theorem repeated_upper {n Bmax : ℕ} (I : SolveBox n Bmax)
    (t : RandomTree (BoxVector I)) {z : Vec (Fin n)}
    (h : t.probability (fun p => ¬p.val ≤ z) ≤ 1 / 16) {J : ℕ} (hJ : 0 < J) :
    (I.repeated t J).probability (fun p => ¬p.val ≤ z) ≤ (1 / 2 : ℚ) ^ J := by
  rw [repeated, RandomTree.probability_map]
  apply le_trans _ (RandomTree.amplification t (fun p => p.val ≤ z) h J)
  apply RandomTree.probability_mono_all
  apply RandomTree.all_mono _ (RandomTree.trials_length t J)
  intro as has hf
  have hlen : 0 < as.length := by omega
  simp only [medianBox, dite_eq_left hlen] at hf
  have hm := median_upper_failure (by simpa using hlen : 0 < (as.map Subtype.val).length) hf
  have hc := RandomTree.badCount_map_le Subtype.val (fun p : BoxVector I => p.val ≤ z)
    (fun p => p ≤ z) (fun _ hp => hp) as
  simp only [List.length_map] at hm
  omega

def withFloor {n Bmax : ℕ} (I : SolveBox n Bmax) (p : BoxVector I) : SolveBox n Bmax :=
  { I with
    a := p.val
    ordered := p.property.2
    width_bound := fun i => by
      have hp : I.a i ≤ p.val i := p.property.1 i
      have hi := I.width_bound i
      omega }

def withCeiling {n Bmax : ℕ} (I : SolveBox n Bmax) (p : BoxVector I) : SolveBox n Bmax :=
  { I with
    b := p.val
    ordered := p.property.1
    width_bound := fun i => by
      have hp : p.val i ≤ I.b i := p.property.2 i
      have hi := I.width_bound i
      omega }

def capLow {n Bmax : ℕ} (I : SolveBox n Bmax) (C : ℕ) (hC : 0 < C)
    (hle : C ≤ I.width) : SolveBox n Bmax :=
  { I with
    b := fun i => min (I.b i) (I.a i + C)
    ordered := fun i => by
      have hi : I.a i ≤ I.b i := I.ordered i
      dsimp only
      omega
    width := C
    positive := hC
    bounded := hle.trans I.bounded
    width_bound := fun i => by omega }

def capHigh {n Bmax : ℕ} (I : SolveBox n Bmax) (C : ℕ) (hC : 0 < C)
    (hle : C ≤ I.width) : SolveBox n Bmax :=
  { I with
    a := fun i => max (I.a i) (I.b i - C)
    ordered := fun i => by
      have hi : I.a i ≤ I.b i := I.ordered i
      dsimp only
      omega
    width := C
    positive := hC
    bounded := hle.trans I.bounded
    width_bound := fun i => by omega }

def centered {n Bmax : ℕ} (q : Vec (Fin n)) (A : ℕ) (hA : 0 < A)
    (hmax : 2 * A ≤ Bmax) : SolveBox n Bmax where
  a := fun i => q i - A
  b := fun i => q i + A
  ordered := fun i => by
    dsimp only
    omega
  width := 2 * A
  positive := by omega
  bounded := hmax
  width_bound := fun i => by push_cast; omega

def exactVector (G : Game) {Bmax : ℕ} (I : SolveBox G.n Bmax) : BoxVector I :=
  ⟨(basic G I.a I.b I.ordered).1, (basic_spec G I.a I.b I.ordered).1.1⟩

def smallVector {n Bmax : ℕ} (I : SolveBox n Bmax) (P : Budgets n) : BoxVector I :=
  ⟨smallRankAnswer I.a I.b P, by
    constructor
    · intro i
      unfold smallRankAnswer
      split_ifs <;> first | exact I.ordered i | exact le_refl _
    · intro i
      unfold smallRankAnswer
      split_ifs <;> first | exact I.ordered i | exact le_refl _⟩

def midpoint {n Bmax : ℕ} (I : SolveBox n Bmax) : BoxVector I :=
  ⟨fun i => (I.a i + I.b i) / 2, by
    constructor
    · intro i
      change I.a i ≤ (I.a i + I.b i) / 2
      have hi : I.a i ≤ I.b i := I.ordered i
      omega
    · intro i
      change (I.a i + I.b i) / 2 ≤ I.b i
      have hi : I.a i ≤ I.b i := I.ordered i
      omega⟩

def averageClipped {n Bmax : ℕ} (I : SolveBox n Bmax)
    (r₁ r₂ : Vec (Fin n)) : BoxVector I :=
  ⟨clip I.a I.b (fun i => (r₁ i + r₂ i) / 2), by
    constructor
    · intro i
      dsimp [clip]
      have hi : I.a i ≤ I.b i := I.ordered i
      omega
    · intro i
      dsimp [clip]
      have hi : I.a i ≤ I.b i := I.ordered i
      omega⟩

end SolveBox

namespace RandomTree

def uniformBelow : ℕ → RandomTree ℕ
  | 0 => .leaf 0
  | k + 1 => .coin (uniformBelow k) ((uniformBelow k).map (fun i => i + 2 ^ k))

theorem uniformBelow_lt (k : ℕ) : (uniformBelow k).All (fun i => i < 2 ^ k) := by
  induction k with
  | zero => norm_num [uniformBelow, All]
  | succ k hk =>
    constructor
    · exact all_mono _ hk (fun i hi => by rw [pow_succ]; omega)
    · rw [map, all_bind]
      exact all_mono _ hk (fun i hi => by dsimp [All]; rw [pow_succ]; omega)

theorem expect_uniformBelow (k : ℕ) (f : ℕ → ℚ) :
    (uniformBelow k).expect f = (∑ i ∈ Finset.range (2 ^ k), f i) / (2 ^ k : ℚ) := by
  induction k generalizing f with
  | zero => simp [uniformBelow]
  | succ k hk =>
    simp only [uniformBelow, expect_coin, expect_map, Function.comp_def, hk]
    rw [show 2 ^ (k + 1) = 2 ^ k + 2 ^ k by omega]
    rw [Finset.sum_range_add]
    simp only [pow_succ]
    have hsum : (∑ i ∈ Finset.range (2 ^ k), f (i + 2 ^ k)) =
        ∑ i ∈ Finset.range (2 ^ k), f (2 ^ k + i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Nat.add_comm]
    rw [hsum]
    ring

end RandomTree
end MeanPayoff
end

end OAI
