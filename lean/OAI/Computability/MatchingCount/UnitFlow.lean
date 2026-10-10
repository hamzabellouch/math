import OAI.Computability.MatchingCount.ListNumeric
import OAI.Combinatorics.PerfectMatching.Main

namespace OAI

section

namespace BinaryMatching.UnitFlow
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Matrix (V : Type*) := V → V → ℤ

def divergence (b : Matrix V) (i : V) : ℤ := ∑ j, b i j

def cutCapacity (c : V → V → ℕ) (S : Finset V) : ℕ :=
  ∑ i ∈ S, ∑ j ∈ Sᶜ, c i j

def cutFlow (b : Matrix V) (S : Finset V) : ℤ :=
  ∑ i ∈ S, ∑ j ∈ Sᶜ, b i j

structure Feasible (c : V → V → ℕ) (a z : V) (b : Matrix V) : Prop where
  antisymm : ∀ i j, b i j = -b j i
  capacity : ∀ i j, b i j ≤ c i j
  conservation : ∀ i, i ≠ a → i ≠ z → divergence b i = 0

omit [DecidableEq V] in
lemma feasible_zero (c : V → V → ℕ) (a z : V) :
    Feasible c a z (fun _ _ => 0) where
  antisymm _ _ := by simp
  capacity _ _ := by positivity
  conservation _ _ _ := by simp [divergence]

omit [Fintype V] [DecidableEq V] in
lemma antisymm_internal (b : Matrix V) (h : ∀ i j, b i j = -b j i)
    (S : Finset V) : (∑ i ∈ S, ∑ j ∈ S, b i j) = 0 := by
  have hh : (∑ i ∈ S, ∑ j ∈ S, b i j) = -(∑ i ∈ S, ∑ j ∈ S, b i j) := by
    calc
      _ = ∑ i ∈ S, ∑ j ∈ S, -b j i := by
        apply sum_congr rfl; intro i hi
        apply sum_congr rfl; intro j hj
        exact h i j
      _ = -(∑ i ∈ S, ∑ j ∈ S, b j i) := by simp
      _ = _ := by rw [sum_comm]
  omega

lemma divergence_cut (b : Matrix V) (h : ∀ i j, b i j = -b j i)
    (S : Finset V) : (∑ i ∈ S, divergence b i) = cutFlow b S := by
  have split : ∀ i, divergence b i = (∑ j ∈ S, b i j) + ∑ j ∈ Sᶜ, b i j := by
    intro i
    exact (sum_add_sum_compl S (fun j => b i j)).symm
  simp_rw [split]
  rw [sum_add_distrib, antisymm_internal b h S, zero_add]
  rfl

lemma source_cut {c : V → V → ℕ} {a z : V} {b : Matrix V}
    (h : Feasible c a z b) (S : Finset V) (ha : a ∈ S) (hz : z ∉ S) :
    cutFlow b S = divergence b a := by
  rw [← divergence_cut b h.antisymm]
  exact sum_eq_single a (fun i hi hia => h.conservation i hia (by intro e; subst i; exact hz hi))
    (fun hna => (hna ha).elim)

lemma cutFlow_le_capacity {c : V → V → ℕ} {b : Matrix V}
    (h : ∀ i j, b i j ≤ c i j) (S : Finset V) :
    cutFlow b S ≤ cutCapacity c S := by
  simp only [cutFlow, cutCapacity, Nat.cast_sum]
  exact sum_le_sum (fun i _ => sum_le_sum (fun j _ => h i j))

lemma weak_duality {c : V → V → ℕ} {a z : V} {b : Matrix V}
    (h : Feasible c a z b) (S : Finset V) (ha : a ∈ S) (hz : z ∉ S) :
    divergence b a ≤ cutCapacity c S := by
  rw [← source_cut h S ha hz]
  exact cutFlow_le_capacity h.capacity S

lemma saturated_minimum {c : V → V → ℕ} {a z : V} {b : Matrix V}
    (h : Feasible c a z b) (S : Finset V) (ha : a ∈ S) (hz : z ∉ S)
    (hsat : ∀ i ∈ S, ∀ j ∉ S, b i j = c i j) :
    ∀ T : Finset V, a ∈ T → z ∉ T → cutCapacity c S ≤ cutCapacity c T := by
  have heq : cutFlow b S = cutCapacity c S := by
    simp only [cutFlow, cutCapacity, Nat.cast_sum]
    apply sum_congr rfl; intro i hi
    apply sum_congr rfl; intro j hj
    exact hsat i hi j (mem_compl.mp hj)
  intro T hTa hTz
  have := weak_duality h T hTa hTz
  rw [← source_cut h S ha hz, heq] at this
  exact_mod_cast this

omit [DecidableEq V] in
lemma source_bound {c : V → V → ℕ} {a z : V} {b : Matrix V}
    (h : Feasible c a z b) : divergence b a ≤ ∑ j, (c a j : ℤ) :=
  sum_le_sum (fun j _ => h.capacity a j)

def arc (u v : V) : Matrix V := fun i j =>
  (if i=u ∧ j=v then 1 else 0) - (if i=v ∧ j=u then 1 else 0)

omit [Fintype V] in
lemma arc_antisymm (u v i j : V) : arc u v i j = -arc u v j i := by
  simp only [arc]
  have h₁ : (i=u ∧ j=v) ↔ (j=v ∧ i=u) := and_comm
  have h₂ : (i=v ∧ j=u) ↔ (j=u ∧ i=v) := and_comm
  simp only [h₁, h₂]
  ring

lemma arc_divergence (u v i : V) : divergence (arc u v) i =
    (if i=u then 1 else 0) - (if i=v then 1 else 0) := by
  simp only [divergence, arc, sum_sub_distrib]
  simp_rw [ite_and]
  simp

def pathFlow : List V → Matrix V
  | [] => fun _ _ => 0
  | [_] => fun _ _ => 0
  | v::u::p => fun i j => pathFlow (u::p) i j + arc u v i j

omit [Fintype V] in
lemma pathFlow_antisymm (p : List V) (i j : V) :
    pathFlow p i j = -pathFlow p j i := by
  induction p using List.twoStepInduction with
  | nil => simp [pathFlow]
  | singleton v => simp [pathFlow]
  | cons_cons v u p _ ih =>
    simp only [pathFlow]
    rw [ih, arc_antisymm]
    ring

lemma pathFlow_divergence (p : List V) (i : V) :
    divergence (pathFlow p) i =
      (if p.getLast? = some i then 1 else 0) -
      (if p.head? = some i then 1 else 0) := by
  induction p using List.twoStepInduction with
  | nil => simp [pathFlow, divergence]
  | singleton v => simp [pathFlow, divergence]
  | cons_cons v u p _ ih =>
    rw [show divergence (pathFlow (v::u::p)) i =
        divergence (pathFlow (u::p)) i + divergence (arc u v) i by
      simp [divergence, pathFlow, sum_add_distrib]]
    rw [ih, arc_divergence]
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_cons_cons]
    by_cases hiu : i=u <;> by_cases hiv : i=v <;> simp_all [eq_comm, sub_eq_add_neg]

omit [Fintype V] in
lemma pathFlow_zero_of_not_mem (p : List V) (i j : V) (hi : i ∉ p) :
    pathFlow p i j = 0 := by
  induction p using List.twoStepInduction with
  | nil => rfl
  | singleton v => rfl
  | cons_cons v u p _ ih =>
    have hiv : i ≠ v := by intro hh; exact hi (by simp [hh])
    have hit : i ∉ u::p := by intro hh; exact hi (List.mem_cons_of_mem _ hh)
    have hiu : i ≠ u := by intro hh; exact hit (by simp [hh])
    simp [pathFlow, ih u hit, arc, hiv, hiu]

omit [Fintype V] in
lemma pathFlow_le_one (p : List V) (hp : p.Nodup) (i j : V) : pathFlow p i j ≤ 1 := by
  induction p using List.twoStepInduction with
  | nil => simp [pathFlow]
  | singleton v => simp [pathFlow]
  | cons_cons v u p _ ih =>
    have hv : v ∉ u::p := hp.notMem
    have htail := ih u hp.of_cons
    by_cases hiv : i = v
    · subst i
      simp only [pathFlow]
      rw [pathFlow_zero_of_not_mem _ _ _ hv]
      simp only [arc]
      split_ifs <;> omega
    · by_cases hjv : j = v
      · subst j
        have hz : pathFlow (u::p) i v = 0 := by
          rw [pathFlow_antisymm, pathFlow_zero_of_not_mem _ _ _ hv, neg_zero]
        simp only [pathFlow]
        rw [hz]
        simp only [arc]
        split_ifs <;> omega
      · simpa [pathFlow, arc, hiv, hjv] using htail

omit [Fintype V] in
lemma pathFlow_pos_relation (R : V → V → Prop) (p : List V) (hp : p.Nodup)
    (hc : p.IsChain (fun v u => R u v)) (i j : V) (hij : 0 < pathFlow p i j) :
    R i j := by
  induction p using List.twoStepInduction with
  | nil => simp [pathFlow] at hij
  | singleton v => simp [pathFlow] at hij
  | cons_cons v u p _ ih =>
    have hv : v ∉ u::p := hp.notMem
    have huv : u ≠ v := by intro e; exact hv (by simp [e])
    have ht : (u::p).IsChain (fun v u => R u v) := hc.tail
    have hr : R u v := (List.isChain_cons_cons.mp hc).1
    by_cases hiv : i = v
    · subst i
      simp only [pathFlow] at hij
      rw [pathFlow_zero_of_not_mem _ _ _ hv] at hij
      simp only [arc] at hij
      by_cases hju : j=u <;> simp [huv, huv.symm, hju] at hij
    · by_cases hjv : j = v
      · subst j
        have hz : pathFlow (u::p) i v = 0 := by
          rw [pathFlow_antisymm, pathFlow_zero_of_not_mem _ _ _ hv, neg_zero]
        simp only [pathFlow] at hij
        rw [hz] at hij
        by_cases hiu : i=u
        · simpa [hiu] using hr
        · simp [arc, hiu, hiv] at hij
      · apply ih u hp.of_cons ht
        simpa [pathFlow, arc, hiv, hjv] using hij

lemma augment_feasible {c : V → V → ℕ} {a z : V} {b : Matrix V}
    (hb : Feasible c a z b) (p : List V) (hp : p.Nodup)
    (hc : p.IsChain (fun v u => b u v < c u v))
    (hhead : p.head? = some z) (hlast : p.getLast? = some a) :
    Feasible c a z (fun i j => b i j + pathFlow p i j) where
  antisymm i j := by rw [hb.antisymm, pathFlow_antisymm]; ring
  capacity i j := by
    have hcap := hb.capacity i j
    by_cases hpos : 0 < pathFlow p i j
    · have hres := pathFlow_pos_relation (fun u v => b u v < c u v) p hp hc i j hpos
      have hle := pathFlow_le_one p hp i j
      omega
    · omega
  conservation i hia hiz := by
    simp only [divergence, sum_add_distrib]
    change divergence b i + divergence (pathFlow p) i = 0
    rw [hb.conservation i hia hiz, pathFlow_divergence, hhead, hlast]
    simp [Ne.symm hia, Ne.symm hiz]

lemma augment_value {a z : V} (haz : a ≠ z) (b : Matrix V) (p : List V)
    (hhead : p.head? = some z) (hlast : p.getLast? = some a) :
    divergence (fun i j => b i j + pathFlow p i j) a = divergence b a + 1 := by
  simp only [divergence, sum_add_distrib]
  change divergence b a + divergence (pathFlow p) a = _
  rw [pathFlow_divergence, hhead, hlast]
  simp [Ne.symm haz, divergence]

end BinaryMatching.UnitFlow
end

end OAI
