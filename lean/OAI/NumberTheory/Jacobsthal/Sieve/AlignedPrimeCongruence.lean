import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import OAI.NumberTheory.Jacobsthal.Estimates.FactorDividesAbscissa
import OAI.NumberTheory.Jacobsthal.Primes.PrimeHitRepresentative

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.SievePartition

open scoped BigOperators

variable {α ι : Type*} [DecidableEq α] [LinearOrder ι]

noncomputable def survivors (C : Finset α) (P : Finset ι)
    (bad : ι → α → Prop) : Finset α := by
  classical
  exact C.filter fun x => ∀ p ∈ P, ¬ bad p x

noncomputable def childCell (C : Finset α) (P : Finset ι)
    (bad : ι → α → Prop) (p : ι) : Finset α := by
  classical
  exact C.filter fun x => bad p x ∧ ∀ q ∈ P, q < p → ¬ bad q x

omit [DecidableEq α] [LinearOrder ι] in
@[simp] theorem mem_survivors {C : Finset α} {P : Finset ι}
    {bad : ι → α → Prop} {x : α} :
    x ∈ survivors C P bad ↔ x ∈ C ∧ ∀ p ∈ P, ¬ bad p x := by
  classical
  simp [survivors]

omit [DecidableEq α] in
@[simp] theorem mem_childCell {C : Finset α} {P : Finset ι}
    {bad : ι → α → Prop} {p : ι} {x : α} :
    x ∈ childCell C P bad p ↔
      x ∈ C ∧ bad p x ∧ ∀ q ∈ P, q < p → ¬ bad q x := by
  classical
  simp [childCell]

omit [DecidableEq α] in

theorem exists_childCell {C : Finset α} {P : Finset ι}
    {bad : ι → α → Prop} {x : α}
    (hx : x ∈ C) (hnot : x ∉ survivors C P bad) :
    ∃ p ∈ P, x ∈ childCell C P bad p := by
  classical
  have hbad : ∃ p ∈ P, bad p x := by
    by_contra h
    exact hnot (mem_survivors.mpr ⟨hx, fun p hp hpx => h ⟨p, hp, hpx⟩⟩)
  let B := P.filter fun p => bad p x
  have hB : B.Nonempty := by
    obtain ⟨p, hp, hpx⟩ := hbad
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hpx⟩⟩
  let p := B.min' hB
  have hpB : p ∈ B := Finset.min'_mem B hB
  obtain ⟨hpP, hpx⟩ := Finset.mem_filter.mp hpB
  refine ⟨p, hpP, mem_childCell.mpr ⟨hx, hpx, ?_⟩⟩
  intro q hqP hqp hqx
  have hqB : q ∈ B := Finset.mem_filter.mpr ⟨hqP, hqx⟩
  exact (not_lt_of_ge (Finset.min'_le B q hqB)) hqp

omit [DecidableEq α] in

theorem childCell_disjoint {C : Finset α} {P : Finset ι}
    {bad : ι → α → Prop} {p q : ι}
    (hp : p ∈ P) (hq : q ∈ P) (hne : p ≠ q) :
    Disjoint (childCell C P bad p) (childCell C P bad q) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxp hxq
  obtain ⟨_, hpx, hpmin⟩ := mem_childCell.mp hxp
  obtain ⟨_, hqx, hqmin⟩ := mem_childCell.mp hxq
  rcases lt_or_gt_of_ne hne with hpq | hqp
  · exact hqmin p hp hpq hpx
  · exact hpmin q hq hqp hqx

theorem biUnion_childCell (C : Finset α) (P : Finset ι)
    (bad : ι → α → Prop) :
    P.biUnion (childCell C P bad) = C \ survivors C P bad := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, hxp⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hxC, hpx, _⟩ := mem_childCell.mp hxp
    exact Finset.mem_sdiff.mpr ⟨hxC,
      fun hxs => (mem_survivors.mp hxs).2 p hp hpx⟩
  · intro hx
    obtain ⟨hxC, hxnot⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_biUnion.mpr (exists_childCell hxC hxnot)

theorem sum_card_childCell (C : Finset α) (P : Finset ι)
    (bad : ι → α → Prop) :
    ∑ p ∈ P, (childCell C P bad p).card = (C \ survivors C P bad).card := by
  classical
  rw [← biUnion_childCell C P bad]
  symm
  exact Finset.card_biUnion fun p hp q hq hne => childCell_disjoint hp hq hne

theorem card_survivors_add_sum (C : Finset α) (P : Finset ι)
    (bad : ι → α → Prop) :
    (survivors C P bad).card + ∑ p ∈ P, (childCell C P bad p).card = C.card := by
  rw [sum_card_childCell, Nat.add_comm]
  exact Finset.card_sdiff_add_card_eq_card fun _ hx => (mem_survivors.mp hx).1

theorem card_survivors_eq_sub_sum (C : Finset α) (P : Finset ι)
    (bad : ι → α → Prop) :
    ((survivors C P bad).card : ℤ) =
      (C.card : ℤ) - ∑ p ∈ P, ((childCell C P bad p).card : ℤ) := by
  have h : ((survivors C P bad).card : ℤ) +
      ∑ p ∈ P, ((childCell C P bad p).card : ℤ) = (C.card : ℤ) := by
    exact_mod_cast card_survivors_add_sum C P bad
  linarith

def residueBad (a : ℕ → ℕ) (p n : ℕ) : Prop := n % p = a p % p

instance decidableResidueBad (a : ℕ → ℕ) (p n : ℕ) : Decidable (residueBad a p n) :=
  inferInstanceAs (Decidable (n % p = a p % p))

noncomputable def residueCandidates (Y : ℕ) (H small : Finset ℕ)
    (a : ℕ → ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 Y).filter fun n =>
    (∀ p ∈ H, residueBad a p n) ∧ ∀ q ∈ small, ¬ residueBad a q n

@[simp] theorem mem_residueCandidates {Y : ℕ} {H small : Finset ℕ}
    {a : ℕ → ℕ} {n : ℕ} :
    n ∈ residueCandidates Y H small a ↔
      1 ≤ n ∧ n ≤ Y ∧
        (∀ p ∈ H, residueBad a p n) ∧ ∀ q ∈ small, ¬ residueBad a q n := by
  classical
  simp only [residueCandidates, Finset.mem_filter, Finset.mem_Icc]
  tauto

theorem residueCandidates_insert (Y : ℕ) (H small : Finset ℕ)
    (a : ℕ → ℕ) (p : ℕ) :
    residueCandidates Y (insert p H) small a =
      (residueCandidates Y H small a).filter (residueBad a p) := by
  classical
  ext n
  simp only [mem_residueCandidates, Finset.mem_filter, Finset.mem_insert,
    forall_eq_or_imp]
  tauto

theorem residue_childCell_eq (Y : ℕ) (H small P : Finset ℕ)
    (a : ℕ → ℕ) (p : ℕ) :
    childCell (residueCandidates Y H small a) P (residueBad a) p =
      survivors (residueCandidates Y (insert p H) small a)
        (P.filter fun q => q < p) (residueBad a) := by
  classical
  rw [residueCandidates_insert]
  ext n
  simp only [mem_childCell, mem_survivors, Finset.mem_filter]
  constructor
  · rintro ⟨hn, hpn, hleast⟩
    exact ⟨⟨hn, hpn⟩, fun q hq => hleast q hq.1 hq.2⟩
  · rintro ⟨⟨hn, hpn⟩, hleast⟩
    exact ⟨hn, hpn, fun q hq hqp => hleast q ⟨hq, hqp⟩⟩

theorem residue_tree_identity (Y : ℕ) (H small P : Finset ℕ) (a : ℕ → ℕ) :
    ((survivors (residueCandidates Y H small a) P (residueBad a)).card : ℤ) =
      ((residueCandidates Y H small a).card : ℤ) -
        ∑ p ∈ P,
          ((survivors (residueCandidates Y (insert p H) small a)
            (P.filter fun q => q < p) (residueBad a)).card : ℤ) := by
  classical
  simpa only [residue_childCell_eq] using
    card_survivors_eq_sub_sum (residueCandidates Y H small a) P (residueBad a)

end NumberTheoryLean.SievePartition

end

section

namespace NumberTheoryLean.SieveTree

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

structure Data (V : Type*) [DecidableEq V] where
  children : V → Finset V
  retained : V → Finset V
  retained_subset : ∀ v, retained v ⊆ children v
  mass : V → ℤ
  survivors : V → ℤ
  survivors_nonneg : ∀ v, 0 ≤ survivors v
  partition : ∀ v, survivors v = mass v - ∑ w ∈ children v, survivors w
  stopLower : V → Bool

def bounds (D : Data V) : ℕ → V → ℤ × ℤ
  | 0, v => (D.survivors v, D.mass v)
  | n + 1, v =>
      (if D.stopLower v then D.survivors v
       else D.mass v - ∑ w ∈ D.children v, (bounds D n w).2,
       D.mass v - ∑ w ∈ D.retained v, (bounds D n w).1)

theorem survivors_le_mass (D : Data V) (v : V) :
    D.survivors v ≤ D.mass v := by
  have hsum : 0 ≤ ∑ w ∈ D.children v, D.survivors w :=
    Finset.sum_nonneg fun w _ => D.survivors_nonneg w
  have hid := D.partition v
  linarith

theorem bounds_correct (D : Data V) (n : ℕ) (v : V) :
    (bounds D n v).1 ≤ D.survivors v ∧
    D.survivors v ≤ (bounds D n v).2 := by
  induction n generalizing v with
  | zero =>
      exact ⟨le_refl _, survivors_le_mass D v⟩
  | succ n ih =>
      have hAll : (∑ w ∈ D.children v, D.survivors w) ≤
          ∑ w ∈ D.children v, (bounds D n w).2 :=
        Finset.sum_le_sum fun w _ => (ih w).2
      have hKept : (∑ w ∈ D.retained v, (bounds D n w).1) ≤
          ∑ w ∈ D.retained v, D.survivors w :=
        Finset.sum_le_sum fun w _ => (ih w).1
      have hSubset : (∑ w ∈ D.retained v, D.survivors w) ≤
          ∑ w ∈ D.children v, D.survivors w :=
        Finset.sum_le_sum_of_subset_of_nonneg (D.retained_subset v)
          (fun w _ _ => D.survivors_nonneg w)
      have hid := D.partition v
      constructor
      · simp only [bounds]
        split
        · exact le_refl _
        · linarith
      · simp only [bounds]
        linarith

theorem stopped_tree_lower_bound (D : Data V) (depth : ℕ) (root : V) :
    (bounds D depth root).1 ≤ D.survivors root :=
  (bounds_correct D depth root).1

theorem exact_lower_stop (D : Data V) (n : ℕ) (v : V)
    (h : D.stopLower v = true) :
    (bounds D (n + 1) v).1 = D.survivors v := by
  simp [bounds, h]

theorem leaf_mass_eq (D : Data V) (v : V) (h : D.children v = ∅) :
    D.mass v = D.survivors v := by
  simpa [h] using (D.partition v).symm

end NumberTheoryLean.SieveTree

end

section

namespace NumberTheoryLean.ResidueSieveTree

open scoped BigOperators
open SievePartition

abbrev Vertex := Finset ℕ × Finset ℕ

def child (v : Vertex) (p : ℕ) : Vertex :=
  (insert p v.1, v.2.filter fun q => q < p)

def children (v : Vertex) : Finset Vertex := v.2.image (child v)

noncomputable def retained (admissible : Vertex → ℕ → Prop) (v : Vertex) : Finset Vertex := by
  classical
  exact (v.2.filter (admissible v)).image (child v)

theorem retained_subset (admissible : Vertex → ℕ → Prop) (v : Vertex) :
    retained admissible v ⊆ children v := by
  classical
  exact Finset.image_subset_image (Finset.filter_subset _ _)

theorem child_injOn (v : Vertex) : Set.InjOn (child v) (v.2 : Set ℕ) := by
  intro p hp q hq heq
  have hsets := congrArg Prod.snd heq
  change v.2.filter (fun r => r < p) = v.2.filter (fun r => r < q) at hsets
  by_contra hne
  rcases lt_or_gt_of_ne hne with hpq | hqp
  · have hm : p ∈ v.2.filter (fun r => r < q) := Finset.mem_filter.mpr ⟨hp, hpq⟩
    rw [← hsets] at hm
    exact (lt_irrefl p) (Finset.mem_filter.mp hm).2
  · have hm : q ∈ v.2.filter (fun r => r < p) := Finset.mem_filter.mpr ⟨hq, hqp⟩
    rw [hsets] at hm
    exact (lt_irrefl q) (Finset.mem_filter.mp hm).2

theorem child_card_lt (v : Vertex) {p : ℕ} (hp : p ∈ v.2) :
    (child v p).2.card < v.2.card := by
  apply Finset.card_lt_card
  exact Finset.filter_ssubset.mpr ⟨p, hp, lt_irrefl p⟩

noncomputable def mass (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (v : Vertex) : ℤ :=
  (residueCandidates Y v.1 small a).card

noncomputable def survivorCount (Y : ℕ) (small : Finset ℕ)
    (a : ℕ → ℕ) (v : Vertex) : ℤ :=
  (survivors (residueCandidates Y v.1 small a) v.2 (residueBad a)).card

theorem survivorCount_nonneg (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (v : Vertex) :
    0 ≤ survivorCount Y small a v := Int.natCast_nonneg _

theorem partition (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (v : Vertex) :
    survivorCount Y small a v = mass Y small a v -
      ∑ w ∈ children v, survivorCount Y small a w := by
  classical
  rw [children, Finset.sum_image (child_injOn v)]
  exact residue_tree_identity Y v.1 small v.2 a

noncomputable def data (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (admissible : Vertex → ℕ → Prop) (stop : Vertex → Bool) : SieveTree.Data Vertex where
  children := children
  retained := retained admissible
  retained_subset := retained_subset admissible
  mass := mass Y small a
  survivors := survivorCount Y small a
  survivors_nonneg := survivorCount_nonneg Y small a
  partition := partition Y small a
  stopLower := stop

theorem bounds_correct (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (admissible : Vertex → ℕ → Prop) (stop : Vertex → Bool) (depth : ℕ) (v : Vertex) :
    (SieveTree.bounds (data Y small a admissible stop) depth v).1 ≤
      survivorCount Y small a v ∧
    survivorCount Y small a v ≤
      (SieveTree.bounds (data Y small a admissible stop) depth v).2 :=
  SieveTree.bounds_correct (data Y small a admissible stop) depth v

theorem stopped_tree_lower_bound (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (admissible : Vertex → ℕ → Prop) (stop : Vertex → Bool) (depth : ℕ) (v : Vertex) :
    (SieveTree.bounds (data Y small a admissible stop) depth v).1 ≤
      ((survivors (residueCandidates Y v.1 small a) v.2 (residueBad a)).card : ℤ) :=
  (bounds_correct Y small a admissible stop depth v).1

theorem bounds_succ_eq_of_card_le (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (admissible : Vertex → ℕ → Prop) (stop : Vertex → Bool) (depth : ℕ) (v : Vertex)
    (hdepth : v.2.card ≤ depth) :
    SieveTree.bounds (data Y small a admissible stop) (depth + 1) v =
      SieveTree.bounds (data Y small a admissible stop) depth v := by
  classical
  let D := data Y small a admissible stop
  change SieveTree.bounds D (depth + 1) v = SieveTree.bounds D depth v
  induction depth generalizing v with
  | zero =>
      have hP : v.2 = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hdepth)
      have hc : children v = ∅ := by simp [children, hP]
      have hr : retained admissible v = ∅ := by
        apply Finset.subset_empty.mp
        simpa only [hc] using retained_subset admissible v
      have hS : survivorCount Y small a v = mass Y small a v := by
        simpa only [hc, Finset.sum_empty, sub_zero] using partition Y small a v
      simp [SieveTree.bounds, D, data, hc, hr, hS]
  | succ depth ih =>
      have hchild : ∀ w ∈ D.children v,
          SieveTree.bounds D (depth + 1) w = SieveTree.bounds D depth w := by
        intro w hw
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
        apply ih
        have hlt := child_card_lt v hp
        omega
      have hupper : (∑ w ∈ D.children v, (SieveTree.bounds D (depth + 1) w).2) =
          ∑ w ∈ D.children v, (SieveTree.bounds D depth w).2 := by
        apply Finset.sum_congr rfl
        intro w hw
        exact congrArg Prod.snd (hchild w hw)
      have hlower : (∑ w ∈ D.retained v, (SieveTree.bounds D (depth + 1) w).1) =
          ∑ w ∈ D.retained v, (SieveTree.bounds D depth w).1 := by
        apply Finset.sum_congr rfl
        intro w hw
        exact congrArg Prod.fst (hchild w (D.retained_subset v hw))
      conv_lhs => rw [SieveTree.bounds]
      conv_rhs => rw [SieveTree.bounds]
      rw [hupper, hlower]

theorem bounds_stabilize (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (admissible : Vertex → ℕ → Prop) (stop : Vertex → Bool) (v : Vertex) (extra : ℕ) :
    SieveTree.bounds (data Y small a admissible stop) (v.2.card + extra) v =
      SieveTree.bounds (data Y small a admissible stop) v.2.card v := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      rw [Nat.add_succ, bounds_succ_eq_of_card_le Y small a admissible stop
        (v.2.card + extra) v (Nat.le_add_right _ _)]
      exact ih

end NumberTheoryLean.ResidueSieveTree

end

section

namespace ErdosInverseCounts
open NumberTheoryLean NumberTheoryLean.SievePartition

noncomputable def modulusCandidates (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (m : ℕ) : Finset ℕ :=
  residueCandidates Y m.primeFactors small a

noncomputable def modulusCount (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (m : ℕ) : ℤ :=
  (modulusCandidates Y small a m).card

theorem mem_modulusCandidates (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (m n : ℕ) :
    n ∈ modulusCandidates Y small a m ↔ 1 ≤ n ∧ n ≤ Y ∧
      (∀ p ∈ m.primeFactors,n % p = a p % p) ∧ ∀ p ∈ small,n % p ≠ a p % p := by
  exact mem_residueCandidates

theorem modulusCount_eq_mass (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (m : ℕ) (P : Finset ℕ) :
    modulusCount Y small a m = ResidueSieveTree.mass Y small a (m.primeFactors,P) := rfl

theorem modulusCount_nonneg (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ) (m : ℕ) :
    0 ≤ modulusCount Y small a m := Int.natCast_nonneg _

theorem modulusCandidates_prime_mul (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (p m : ℕ) (hp : Nat.Prime p) (hm : m ≠ 0) :
    modulusCandidates Y small a (p*m) = (modulusCandidates Y small a m).filter (residueBad a p) := by
  classical
  unfold modulusCandidates
  rw [Nat.primeFactors_mul hp.ne_zero hm,hp.primeFactors,Finset.singleton_union]
  exact residueCandidates_insert Y m.primeFactors small a p

theorem primeFactors_product (H : Finset ℕ) (hH : ∀ p ∈ H,Nat.Prime p) :
    (∏ p ∈ H,p).primeFactors = H := by
  classical
  revert hH
  induction H using Finset.induction_on with
  | empty => intro _;simp
  | @insert p H hp ih =>
      intro hH
      have hprime := hH p (Finset.mem_insert_self _ _)
      have hrest : ∀ q ∈ H,Nat.Prime q := fun q hq => hH q (Finset.mem_insert_of_mem hq)
      have hprod : (∏ q ∈ H,q) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun q hq => (hrest q hq).ne_zero)
      rw [Finset.prod_insert hp,Nat.primeFactors_mul hprime.ne_zero hprod,hprime.primeFactors,
        ih hrest,Finset.singleton_union]

theorem modulusCount_product_eq_mass (Y : ℕ) (small : Finset ℕ) (a : ℕ → ℕ)
    (H P : Finset ℕ) (hH : ∀ p ∈ H,Nat.Prime p) :
    modulusCount Y small a (∏ p ∈ H,p) = ResidueSieveTree.mass Y small a (H,P) := by
  rw [modulusCount_eq_mass Y small a _ P,primeFactors_product H hH]

end ErdosInverseCounts

end

section

namespace ErdosAlignedProgression
open ErdosInverseAlignment ErdosInverseHits ErdosInverseCounts

theorem aligned_den_coprime_prime (a : ℕ → ℕ) (r : ℚ) (p : ℕ) (hp : p.Prime)
    (ha : aligns (fun s => (a s : ℤ)) r p) : r.den.Coprime p :=
  (hp.coprime_iff_not_dvd.mpr (aligned_prime_not_dvd_den _ r hp ha)).symm

theorem aligned_den_coprime (a : ℕ → ℕ) (r : ℚ) (d : ℕ) (hd : Squarefree d)
    (ha : ∀ p ∈ d.primeFactors, aligns (fun s => (a s : ℤ)) r p) : r.den.Coprime d := by
  rw [← Nat.prod_primeFactors_of_squarefree hd]
  exact Nat.Coprime.prod_right (fun p hp => aligned_den_coprime_prime a r p
    (Nat.prime_of_mem_primeFactors hp) (ha p hp))

theorem aligned_prime_hit_iff (a : ℕ → ℕ) (r : ℚ) (p t : ℕ) (hp : p.Prime)
    (ha : aligns (fun s => (a s : ℤ)) r p) :
    t % p = a p % p ↔ Int.ModEq (p : ℤ) ((r.den : ℤ)*(t : ℤ)) r.num := by
  let : Fact p.Prime := ⟨hp⟩
  have hD : (r.den : ZMod p) ≠ 0 := by
    intro h
    exact aligned_prime_not_dvd_den _ r hp ha ((ZMod.natCast_eq_zero_iff _ _).mp h)
  change Nat.ModEq p t (a p) ↔ _
  rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.intCast_eq_intCast_iff]
  simp only [Int.cast_mul, Int.cast_natCast]
  change (t : ZMod p) = (a p : ZMod p) ↔ (r.den : ZMod p)*(t : ZMod p) = (r.num : ZMod p)
  have ha' : (r.den : ZMod p)*(a p : ZMod p) = (r.num : ZMod p) := by
    simpa only [aligns, Int.cast_natCast] using ha
  constructor
  · intro ht
    rw [ht]
    exact ha'
  · intro ht
    exact mul_left_cancel₀ hD (ht.trans ha'.symm)

theorem squarefree_int_modEq_iff (d : ℕ) (hd : Squarefree d) (x y : ℤ) :
    Int.ModEq (d : ℤ) x y ↔ ∀ p ∈ d.primeFactors, Int.ModEq (p : ℤ) x y := by
  simp only [Int.modEq_iff_dvd, Int.natCast_dvd]
  have h := modEq_prime_product_iff d.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
    (y-x).natAbs 0
  rw [Nat.prod_primeFactors_of_squarefree hd] at h
  simpa only [Nat.modEq_zero_iff_dvd] using h

theorem required_hits_iff_parameter (a : ℕ → ℕ) (r : ℚ) (d t : ℕ) (hd : Squarefree d)
    (ha : ∀ p ∈ d.primeFactors, aligns (fun s => (a s : ℤ)) r p) :
    (∀ p ∈ d.primeFactors, t % p = a p % p) ↔
      ∃ m : ℤ, (r.den : ℤ)*(t : ℤ) = r.num+(d : ℤ)*m := by
  have hp : (∀ p ∈ d.primeFactors, t % p = a p % p) ↔
      ∀ p ∈ d.primeFactors, Int.ModEq (p : ℤ) ((r.den : ℤ)*(t : ℤ)) r.num := by
    exact forall_congr' (fun p => forall_congr' (fun h =>
      aligned_prime_hit_iff a r p t (Nat.prime_of_mem_primeFactors h) (ha p h)))
  rw [hp, ← squarefree_int_modEq_iff d hd, Int.modEq_comm, Int.modEq_iff_dvd]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by linarith⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by linarith⟩

end ErdosAlignedProgression

end

end Erdos970

end OAI
