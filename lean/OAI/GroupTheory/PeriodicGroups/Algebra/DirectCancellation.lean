import Mathlib
import OAI.GroupTheory.PeriodicGroups.Algebra.PacketIntervals

namespace OAI

section
universe u v w
namespace SourceBurnside.DirectCancellation
open scoped BigOperators
open Classical
noncomputable section

variable {α T A : Type*} [Ring A]

lemma eval_ne_zero_nodup (f : α → A) (w : List α)
    (hc : ∀ x ∈ w, ∀ y ∈ w, Commute (f x) (f y))
    (hsq : ∀ x ∈ w, f x * f x = 0) (hne : eval f w ≠ 0) : w.Nodup := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have ht : eval f w ≠ 0 := by
      intro hz
      apply hne
      simp [eval, show (w.map f).prod = 0 from hz]
    refine List.nodup_cons.mpr ⟨?_, ih (fun x hx y hy => hc x (by simp [hx]) y (by simp [hy]))
      (fun x hx => hsq x (by simp [hx])) ht⟩
    intro ha
    obtain ⟨p,q,rfl⟩ := List.mem_iff_append.mp ha
    have hcp : Commute (f a) (eval f p) := by
      apply Commute.list_prod_right
      intro z hz
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
      exact hc a (by simp) x (by simp [hx])
    apply hne
    have hsq' := hsq a (by simp)
    change f a * eval f (p ++ a :: q) = 0
    rw [eval_append]
    change f a * (eval f p * (f a * eval f q)) = 0
    rw [← mul_assoc, hcp.eq, mul_assoc, ← mul_assoc (f a), hsq', zero_mul, mul_zero]

lemma interval_eval_ne_zero (f : α → A) (w : List α) (a e : ℕ)
    (hn : eval f w ≠ 0) : eval f ((w.drop a).take (e-a)) ≠ 0 := by
  intro hz
  apply hn
  have he : w = w.take a ++ (w.drop a).take (e-a) ++ (w.drop a).drop (e-a) := by
    rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  rw [he, eval_append, eval_append, hz, mul_zero, zero_mul]

def EligibleInterval (eligible : T → Prop) (q : ℕ) (v : List T) (a e : ℕ) : Prop :=
  a < e ∧ e ≤ v.length ∧ q ≤ 100*(e-a) ∧
    ∃ t, eligible t ∧ ((v.drop a).take (e-a) = List.replicate (e-a) t) ∧
      (v.take a).getLast? ≠ some t ∧ (v.drop e).head? ≠ some t

def firstLongRun (eligible : T → Prop) (q : ℕ) (v : List T) : ℕ × ℕ :=
  if h : ∃ a, ∃ e, EligibleInterval eligible q v a e then
    let a := Nat.find h
    (a, Nat.find (Nat.find_spec h))
  else (0,0)

lemma firstLongRun_spec (eligible : T → Prop) (q : ℕ) (v : List T)
    (h : ∃ a e, EligibleInterval eligible q v a e) :
    EligibleInterval eligible q v (firstLongRun eligible q v).1
      (firstLongRun eligible q v).2 := by
  simp only [firstLongRun, dite_eq_left h]
  exact Nat.find_spec (Nat.find_spec h)

lemma firstLongRun_first (eligible : T → Prop) (q : ℕ) (v : List T)
    (h : ∃ a e, EligibleInterval eligible q v a e) (a e : ℕ)
    (ha : EligibleInterval eligible q v a e) : (firstLongRun eligible q v).1 ≤ a := by
  simp only [firstLongRun, dite_eq_left h]
  exact Nat.find_min' h ⟨e,ha⟩

lemma eligibleInterval_uniform (erase : α → T) (eligible : T → Prop) (q : ℕ)
    (w : List α) (a e : ℕ) (h : EligibleInterval eligible q (w.map erase) a e) :
    ∃ t, eligible t ∧ ∀ x ∈ (w.drop a).take (e-a), erase x=t := by
  obtain ⟨_,_,_,t,ht,he,_,_⟩ := h
  refine ⟨t,ht,?_⟩
  intro x hx
  have hm : erase x ∈ ((w.drop a).take (e-a)).map erase := List.mem_map_of_mem hx
  have hmap : ((w.drop a).take (e-a)).map erase = List.replicate (e-a) t := by
    simpa only [List.map_take, List.map_drop] using he
  rw [hmap] at hm
  exact (List.mem_replicate.mp hm).2

variable {Γ K : Type*} [Fintype Γ] [CommRing K] [CharP K 2] [Algebra K A]

theorem direct_cancellation {d b q N : ℕ}
    (label : Γ → List α) (hne : ∀ c, label c ≠ [])
    (hb : ∀ c, (label c).length ≤ b)
    (erase : α → T) (eligible : T → Prop) (f : α → A)
    (hcomm : ∀ t, eligible t → ∀ x y, erase x=t → erase y=t → Commute (f x) (f y))
    (hsquare : ∀ x, eligible (erase x) → f x*f x=0)
    (hlong : ∀ w : List α, N ≤ w.length → eval f w ≠ 0 →
      ∃ a e, EligibleInterval eligible q (w.map erase) a e)
    (hbound : 100*b*(d^2+3) < q)
    (W : Γ → Matrix (Fin d) (Fin d) K) (n : ℕ) (hn : N ≤ n) (i j : Fin d) :
    chunkSum label W f n i j = 0 := by
  apply chunkSum_eq_zero_of_ranges label hne hb erase (firstLongRun eligible q) W f
  intro s hlen hval
  have hs := firstLongRun_spec eligible q ((spell label s).map erase)
    (hlong _ (hlen ▸ hn) hval)
  obtain ⟨t,ht,hu⟩ := eligibleInterval_uniform erase eligible q (spell label s) _ _ hs
  obtain ⟨ha,he,hq,_⟩ := hs
  refine ⟨?_,?_,?_,t,hu,hcomm t ht⟩
  · simpa only [List.length_map] using he
  · nlinarith
  · apply eval_ne_zero_nodup f _
    · intro x hx y hy
      exact hcomm t ht x y (hu x hx) (hu y hy)
    · intro x hx
      exact hsquare x ((hu x hx).symm ▸ ht)
    · exact interval_eval_ne_zero f _ _ _ hval

end
end SourceBurnside.DirectCancellation

namespace SourceBurnside.Automaton
open scoped BigOperators
noncomputable section
open Classical

variable {Γ : Type u} {S : Type v} [Semiring S]

abbrev State (Γ : Type u) (b : ℕ) := { w : List Γ // w.length < b }

def stateCode {b : ℕ} (p : State Γ b) : Σ i : Fin b, Fin i.val → Γ :=
  ⟨⟨p.val.length, p.property⟩, p.val.get⟩

lemma stateCode_injective {b : ℕ} : Function.Injective (@stateCode Γ b) := by
  intro p q h
  have hp : List.ofFn (stateCode p).2 = p.val := List.ofFn_get _
  have hq : List.ofFn (stateCode q).2 = q.val := List.ofFn_get _
  apply Subtype.ext
  calc
    p.val = List.ofFn (stateCode p).2 := hp.symm
    _ = List.ofFn (stateCode q).2 := congrArg (fun z : (Σ i : Fin b, Fin i.val → Γ) => List.ofFn z.2) h
    _ = q.val := hq

instance [Fintype Γ] (b : ℕ) : Fintype (State Γ b) := Fintype.ofInjective stateCode stateCode_injective

lemma card_state [Fintype Γ] [Nonempty Γ] (b : ℕ) :
    Fintype.card (State Γ b) ≤ b * Fintype.card Γ ^ b := by
  calc
    _ ≤ Fintype.card (Σ i : Fin b, Fin i.val → Γ) := Fintype.card_le_of_injective _ stateCode_injective
    _ = ∑ i : Fin b, Fintype.card Γ ^ i.val := by simp
    _ ≤ ∑ _i : Fin b, Fintype.card Γ ^ b := Finset.sum_le_sum (fun i _ => by
      exact Nat.pow_le_pow_right Fintype.card_pos i.isLt.le)
    _ = b * Fintype.card Γ ^ b := by simp

def root {b : ℕ} (hb : 0 < b) : State Γ b := ⟨[], hb⟩

def transition {b : ℕ} (W : List Γ → S) (a : Γ) : Matrix (State Γ b) (State Γ b) S :=
  fun p q => (if q.val = p.val ++ [a] then 1 else 0) +
    (if q.val = [] then W (p.val ++ [a]) else 0)

def scan (b : ℕ) (W : List Γ → S) (p : List Γ) : List Γ → S
  | [] => if p = [] then 1 else 0
  | a :: w => (if (p ++ [a]).length < b then scan b W (p ++ [a]) w else 0) +
      W (p ++ [a]) * scan b W [] w

lemma transition_mul [Fintype Γ] {b : ℕ} (hb : 0 < b)
    (W : List Γ → S) (a : Γ) (p : State Γ b) (f : State Γ b → S) :
    (∑ q, transition W a p q * f q) =
      (if h : (p.val ++ [a]).length < b then f ⟨p.val ++ [a], h⟩ else 0) +
        W (p.val ++ [a]) * f (root hb) := by
  simp only [transition, add_mul, Finset.sum_add_distrib]
  congr 1
  · by_cases h : (p.val ++ [a]).length < b
    · rw [dite_eq_left h]
      have he : ∀ q : State Γ b, q.val = p.val ++ [a] ↔ q = ⟨p.val ++ [a], h⟩ :=
        fun _ => ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
      simp only [he, ite_mul, zero_mul, one_mul]
      simp
    · rw [dite_eq_right h]
      apply Finset.sum_eq_zero
      intro q _
      have hq : q.val ≠ p.val ++ [a] := by
        intro heq
        exact h (heq ▸ q.property)
      simp [hq]
  · have he : ∀ q : State Γ b, q.val = [] ↔ q = root hb :=
      fun _ => ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    simp only [he, ite_mul, zero_mul]
    simp

theorem product_transition [Fintype Γ] {b : ℕ} (hb : 0 < b)
    (W : List Γ → S) (w : List Γ) (p : State Γ b) :
    (w.map (transition (b := b) W)).prod p (root hb) = scan b W p.val w := by
  induction w generalizing p with
  | nil =>
    simp only [List.map_nil, List.prod_nil, Matrix.one_apply, scan]
    congr 1
    exact propext Subtype.ext_iff
  | cons a w ih =>
    simp only [List.map_cons, List.prod_cons, Matrix.mul_apply]
    rw [transition_mul hb W a p]
    simp only [scan]
    split_ifs with h
    · rw [ih ⟨p.val ++ [a], h⟩, ih (root hb)]
      rfl
    · rw [ih (root hb)]
      rfl

def freeScan (W : List Γ → S) (p : List Γ) : List Γ → S
  | [] => if p = [] then 1 else 0
  | a :: w => freeScan W (p ++ [a]) w + W (p ++ [a]) * freeScan W [] w

lemma freeScan_long {b : ℕ} (hb : 0 < b) (W : List Γ → S)
    (hW : ∀ v, b < v.length → W v = 0) (p w : List Γ) (hp : b ≤ p.length) :
    freeScan W p w = 0 := by
  induction w generalizing p with
  | nil =>
    have hn : p ≠ [] := by intro h; simp [h] at hp; omega
    simp [freeScan, hn]
  | cons a w ih =>
    have hlen : b < (p ++ [a]).length := by simp; omega
    rw [freeScan, ih _ hlen.le, hW _ hlen, zero_mul, add_zero]

lemma scan_eq_freeScan {b : ℕ} (hb : 0 < b) (W : List Γ → S)
    (hW : ∀ v, b < v.length → W v = 0) (p w : List Γ) :
    scan b W p w = freeScan W p w := by
  induction w generalizing p with
  | nil => rfl
  | cons a w ih =>
    simp only [scan, freeScan, ih]
    split_ifs with h
    · rfl
    · rw [freeScan_long hb W hW (p ++ [a]) w (by omega)]

def partitions : List Γ → List (List (List Γ))
  | [] => [[]]
  | a :: w => (partitions w).flatMap (fun vs =>
      ([a] :: vs) :: (match vs with
        | [] => []
        | v :: rest => [(a :: v) :: rest]))

def partitionWeight (W : List Γ → S) (p : List Γ) : List (List Γ) → S
  | [] => if p = [] then 1 else 0
  | v :: vs => W (p ++ v) * (vs.map W).prod

lemma partitionWeight_empty (W : List Γ → S) (vs : List (List Γ)) :
    partitionWeight W [] vs = (vs.map W).prod := by cases vs <;> simp [partitionWeight]

lemma sum_flatMap {α β : Type*} (l : List α) (f : α → List β) (g : β → S) :
    ((l.flatMap f).map g).sum = (l.map (fun a => ((f a).map g).sum)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

lemma freeScan_eq_partitions (W : List Γ → S) (p w : List Γ) :
    freeScan W p w = ((partitions w).map (partitionWeight W p)).sum := by
  induction w generalizing p with
  | nil => simp [freeScan, partitions, partitionWeight]
  | cons a w ih =>
    rw [freeScan, partitions, sum_flatMap]
    simp_rw [ih]
    have hterm : ∀ vs : List (List Γ),
        ((([a] :: vs) :: (match vs with | [] => [] | v :: rest => [(a :: v) :: rest])).map
          (partitionWeight W p)).sum =
          partitionWeight W (p ++ [a]) vs + W (p ++ [a]) * partitionWeight W [] vs := by
      intro vs
      cases vs with
      | nil => simp [partitionWeight]
      | cons v vs => simp [partitionWeight, List.append_assoc, add_comm]
    simp_rw [hterm]
    rw [List.sum_map_add]
    congr 1
    induction partitions w with
    | nil => simp
    | cons vs l ih => simp only [List.map_cons, List.sum_cons, mul_add, ih]

theorem root_product_eq_partitions [Fintype Γ] {b : ℕ} (hb : 0 < b)
    (W : List Γ → S) (hW : ∀ v, b < v.length → W v = 0) (w : List Γ) :
    (w.map (transition (b := b) W)).prod (root hb) (root hb) =
      ((partitions w).map (fun vs => (vs.map W).prod)).sum := by
  rw [product_transition hb, scan_eq_freeScan hb W hW, freeScan_eq_partitions]
  change ((partitions w).map (partitionWeight W [])).sum = _
  congr 2
  funext vs
  exact partitionWeight_empty W vs

def Segments (vs : List (List Γ)) (w : List Γ) : Prop :=
  vs.flatten = w ∧ ∀ v ∈ vs, v ≠ []

lemma partitions_sound {w : List Γ} {vs : List (List Γ)}
    (h : vs ∈ partitions w) : Segments vs w := by
  induction w generalizing vs with
  | nil =>
    simp only [partitions, List.mem_singleton] at h
    subst vs
    simp [Segments]
  | cons a w ih =>
    obtain ⟨ps, hp, hm⟩ := List.mem_flatMap.mp h
    have hs := ih hp
    cases ps with
    | nil =>
      simp only [List.mem_singleton] at hm
      subst vs
      obtain ⟨rfl, _⟩ := hs
      simp [Segments]
    | cons v ps =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · constructor
        · simpa using congrArg (List.cons a) hs.1
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · simp
          · exact hs.2 z hz
      · constructor
        · simpa using congrArg (List.cons a) hs.1
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · simp
          · exact hs.2 z (List.mem_cons_of_mem _ hz)

lemma partitions_complete {w : List Γ} {vs : List (List Γ)}
    (hs : Segments vs w) : vs ∈ partitions w := by
  induction w generalizing vs with
  | nil =>
    cases vs with
    | nil => exact List.mem_singleton_self _
    | cons v vs =>
      have hv := hs.2 v (by simp)
      have ht : v = [] ∧ vs.flatten = [] := by simpa only [List.flatten_cons, List.append_eq_nil_iff] using hs.1
      have : v = [] := ht.1
      contradiction
  | cons a w ih =>
    cases vs with
    | nil => simp [Segments] at hs
    | cons v vs =>
      cases v with
      | nil => exact (hs.2 [] (by simp) rfl).elim
      | cons z zs =>
        have heq : z = a ∧ zs ++ vs.flatten = w := by simpa using hs.1
        obtain ⟨rfl, heq⟩ := heq
        cases zs with
        | nil =>
          have ht : Segments vs w := ⟨by simpa using heq,
            fun t ht => hs.2 t (List.mem_cons_of_mem _ ht)⟩
          apply List.mem_flatMap.mpr
          exact ⟨vs, ih ht, List.mem_cons_self⟩
        | cons z zs =>
          have ht : Segments ((z :: zs) :: vs) w := by
            constructor
            · exact heq
            · intro t ht
              rcases List.mem_cons.mp ht with rfl | ht
              · simp
              · exact hs.2 t (List.mem_cons_of_mem _ ht)
          apply List.mem_flatMap.mpr
          refine ⟨(z :: zs) :: vs, ih ht, ?_⟩
          simp

theorem mem_partitions_iff {w : List Γ} {vs : List (List Γ)} :
    vs ∈ partitions w ↔ Segments vs w := ⟨partitions_sound, partitions_complete⟩

def children (a : Γ) (vs : List (List Γ)) : List (List (List Γ)) :=
  ([a] :: vs) :: (match vs with | [] => [] | v :: rest => [(a :: v) :: rest])

def parent : List (List Γ) → List (List Γ)
  | [] => []
  | [] :: vs => vs
  | [_] :: vs => vs
  | (_ :: b :: v) :: vs => (b :: v) :: vs

lemma parent_children (a : Γ) (vs : List (List Γ))
    (hs : ∀ v ∈ vs, v ≠ []) {cs : List (List Γ)} (hc : cs ∈ children a vs) :
    parent cs = vs := by
  cases vs with
  | nil => simp only [children, List.mem_singleton] at hc; subst cs; rfl
  | cons v vs =>
    cases v with
    | nil => exact (hs [] (by simp) rfl).elim
    | cons z zs =>
      simp only [children, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> rfl

lemma children_nodup (a : Γ) (vs : List (List Γ))
    (hs : ∀ v ∈ vs, v ≠ []) : (children a vs).Nodup := by
  cases vs with
  | nil => simp [children]
  | cons v vs =>
    have hn := hs v (by simp)
    simp [children, hn]

theorem partitions_nodup (w : List Γ) : (partitions w).Nodup := by
  induction w with
  | nil => simp [partitions]
  | cons a w ih =>
    change ((partitions w).flatMap (children a)).Nodup
    apply List.nodup_flatMap.mpr
    constructor
    · intro vs hv
      exact children_nodup a vs (partitions_sound hv).2
    · apply List.pairwise_iff_get.mpr
      intro i j hij
      apply List.disjoint_left.mpr
      intro cs hci hcj
      have hi := parent_children a ((partitions w).get i)
        (partitions_sound (List.get_mem _ _)).2 hci
      have hj := parent_children a ((partitions w).get j)
        (partitions_sound (List.get_mem _ _)).2 hcj
      have he := (List.nodup_iff_injective_get.mp ih) (hi.symm.trans hj)
      exact (ne_of_lt hij) he

def blockTransition {b : ℕ} [Fintype Γ] {ι : Type*} [Fintype ι]
    (W : List Γ → Matrix ι ι S) (a : Γ) :
    Matrix (State Γ b × ι) (State Γ b × ι) S :=
  Matrix.compRingEquiv _ _ _ (transition W a)

lemma blockTransition_product {b : ℕ} [Fintype Γ] {ι : Type*} [Fintype ι]
    (W : List Γ → Matrix ι ι S) (w : List Γ) :
    (w.map (blockTransition (b := b) W)).prod =
      Matrix.compRingEquiv _ _ _ ((w.map (transition (b := b) W)).prod) := by
  symm
  rw [map_list_prod]
  rw [List.map_map]
  rfl

theorem root_block_eq_partitions {b : ℕ} [Fintype Γ] {ι : Type*} [Fintype ι]
    (hb : 0 < b) (W : List Γ → Matrix ι ι S)
    (hW : ∀ v, b < v.length → W v = 0) (w : List Γ) (i j : ι) :
    (w.map (blockTransition (b := b) W)).prod (root hb, i) (root hb, j) =
      ((partitions w).map (fun vs => (vs.map W).prod)).sum i j := by
  rw [blockTransition_product]
  change ((w.map (transition (b := b) W)).prod (root hb) (root hb)) i j = _
  rw [root_product_eq_partitions hb W hW]

lemma card_blockState [Fintype Γ] [Nonempty Γ] (b d : ℕ) :
    Fintype.card (State Γ b × Fin d) ≤ b * Fintype.card Γ ^ b * d := by
  rw [Fintype.card_prod, Fintype.card_fin]
  exact Nat.mul_le_mul_right d (card_state b)

end
end SourceBurnside.Automaton

namespace SourceBurnside.Automaton
open scoped BigOperators
noncomputable section
open Classical
variable {α Γ S : Type*} [Fintype Γ] [Semiring S]

def combinedWeight (label : Γ → List α) (weight : Γ → S) (w : List α) : S :=
  ∑ c, if label c = w then weight c else 0

lemma combinedWeight_long (label : Γ → List α) (weight : Γ → S) {b : ℕ}
    (hb : ∀ c, (label c).length ≤ b) (w : List α) (hw : b < w.length) :
    combinedWeight label weight w = 0 := by
  apply Finset.sum_eq_zero
  intro c _
  rw [ite_eq_right]
  intro he
  have := hb c
  rw [he] at this
  omega

lemma product_combinedWeight (label : Γ → List α) (weight : Γ → S)
    (vs : List (List α)) :
    (vs.map (combinedWeight label weight)).prod =
      ∑ cs : Fin vs.length → Γ,
        if List.ofFn (label ∘ cs) = vs then (List.ofFn (weight ∘ cs)).prod else 0 := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [List.length_cons]
    rw [← (Fin.consEquiv (fun _ : Fin (vs.length+1) => Γ)).sum_comp]
    simp only [Fintype.sum_prod_type, Fin.consEquiv_apply, List.map_cons, List.prod_cons,
      List.ofFn_succ, Function.comp_def, Fin.cons_zero, Fin.cons_succ, List.cons.injEq]
    rw [ih]
    change (∑ c, if label c = v then weight c else 0) *
      (∑ cs : Fin vs.length → Γ,
        if List.ofFn (label ∘ cs) = vs then (List.ofFn (weight ∘ cs)).prod else 0) = _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro cs _
    split_ifs <;> simp_all [Function.comp_def]

abbrev BoundedSequences (Γ : Type*) (n : ℕ) := Σ r : Fin (n+1), Fin r.val → Γ

def spelled (label : Γ → List α) {n : ℕ} (s : BoundedSequences Γ n) : List α :=
  (List.ofFn (label ∘ s.2)).flatten

def seqWeight (weight : Γ → S) {n : ℕ} (s : BoundedSequences Γ n) : S :=
  (List.ofFn (weight ∘ s.2)).prod

def wordCoefficient (label : Γ → List α) (weight : Γ → S) (w : List α) : S :=
  ∑ s : BoundedSequences Γ w.length,
    if spelled label s = w then seqWeight weight s else 0

lemma length_le_flatten_of_nonempty (vs : List (List α))
    (hv : ∀ v ∈ vs, v ≠ []) : vs.length ≤ vs.flatten.length := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    have hne := hv v (by simp)
    have hp : 0 < v.length := List.length_pos_iff.mpr hne
    have hi := ih (fun t ht => hv t (by simp [ht]))
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

omit [Fintype Γ] in
lemma identifiers_segments (label : Γ → List α) (hn : ∀ c, label c ≠ [])
    {r : ℕ} (cs : Fin r → Γ) :
    Segments (List.ofFn (label ∘ cs)) ((List.ofFn (label ∘ cs)).flatten) := by
  refine ⟨rfl, ?_⟩
  intro v hv
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
  exact hn (cs i)

lemma bounded_product_combinedWeight (label : Γ → List α) (weight : Γ → S)
    (vs : List (List α)) {n : ℕ} (hv : vs.length ≤ n) :
    (∑ s : BoundedSequences Γ n,
      if List.ofFn (label ∘ s.2) = vs then seqWeight weight s else 0) =
      (vs.map (combinedWeight label weight)).prod := by
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single (⟨vs.length, Nat.lt_succ_of_le hv⟩ : Fin (n+1))]
  · exact (product_combinedWeight label weight vs).symm
  · intro r _ hr
    apply Finset.sum_eq_zero
    intro cs _
    rw [ite_eq_right]
    intro he
    have he' := congrArg List.length he
    simp only [List.length_ofFn] at he'
    exact hr (Fin.ext he')
  · simp

omit [Fintype Γ] in
lemma spelled_eq_iff_partition (label : Γ → List α) (hn : ∀ c, label c ≠ [])
    {n : ℕ} (s : BoundedSequences Γ n) (w : List α) :
    spelled label s = w ↔ List.ofFn (label ∘ s.2) ∈ partitions w := by
  rw [mem_partitions_iff]
  constructor
  · intro he
    exact ⟨he, (identifiers_segments label hn s.2).2⟩
  · exact fun he => he.1

theorem wordCoefficient_eq_partitions (label : Γ → List α) (hn : ∀ c, label c ≠ [])
    (weight : Γ → S) (w : List α) :
    wordCoefficient label weight w =
      ((partitions w).map (fun vs => (vs.map (combinedWeight label weight)).prod)).sum := by
  have hnod := partitions_nodup w
  rw [← List.sum_toFinset _ hnod]
  simp only [wordCoefficient]
  have expand (vs : List (List α)) (hvs : vs ∈ (partitions w).toFinset) :
      (vs.map (combinedWeight label weight)).prod =
        ∑ s : BoundedSequences Γ w.length,
          if List.ofFn (label ∘ s.2) = vs then seqWeight weight s else 0 := by
    have hs := partitions_sound (List.mem_toFinset.mp hvs)
    apply (bounded_product_combinedWeight label weight vs ?_).symm
    simpa [hs.1] using length_le_flatten_of_nonempty vs hs.2
  rw [Finset.sum_congr rfl expand, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have he := spelled_eq_iff_partition label hn s w
  simp only [← List.mem_toFinset] at he
  by_cases h : spelled label s = w
  · rw [ite_eq_left h]
    rw [Finset.sum_eq_single (List.ofFn (label ∘ s.2))]
    · simp
    · intro vs _ hvs
      rw [ite_eq_right (Ne.symm hvs)]
    · exact fun hm => (hm (he.mp h)).elim
  · rw [ite_eq_right h]
    symm
    apply Finset.sum_eq_zero
    intro vs hvs
    rw [ite_eq_right]
    intro heq
    exact h (he.mpr (heq ▸ hvs))

theorem root_block_eq_wordCoefficient [Fintype α] {ι : Type*} [Fintype ι]
    {b : ℕ} (hb : 0 < b) (label : Γ → List α)
    (hn : ∀ c, label c ≠ []) (hl : ∀ c, (label c).length ≤ b)
    (weight : Γ → Matrix ι ι S) (w : List α) (i j : ι) :
    (w.map (blockTransition (b := b) (combinedWeight label weight))).prod
      (root hb, i) (root hb, j) = wordCoefficient label weight w i j := by
  rw [root_block_eq_partitions hb _ (combinedWeight_long label weight hl),
    wordCoefficient_eq_partitions label hn]

omit [Fintype Γ] in
lemma sum_words_eq [Fintype α] (v : List α) (n : ℕ) (c : S) :
    (∑ w : Fin n → α, if List.ofFn w = v then c else 0) =
      if v.length = n then c else 0 := by
  by_cases hv : v.length = n
  · subst n
    rw [ite_eq_left rfl, Finset.sum_eq_single v.get]
    · simp
    · intro w _ hw
      rw [ite_eq_right]
      intro he
      have ht : List.ofFn w = List.ofFn v.get := he.trans (List.ofFn_get v).symm
      exact hw (List.ofFn_injective ht)
    · simp
  · rw [ite_eq_right hv]
    apply Finset.sum_eq_zero
    intro w _
    rw [ite_eq_right]
    intro he
    exact hv ((congrArg List.length he).symm.trans (List.length_ofFn (f := w)))

theorem sum_wordCoefficient [Fintype α] (label : Γ → List α)
    (weight : Γ → S) (n : ℕ) (F : List α → S) :
    (∑ w : Fin n → α, wordCoefficient label weight (List.ofFn w) * F (List.ofFn w)) =
      ∑ s : BoundedSequences Γ n,
        if (spelled label s).length = n then seqWeight weight s * F (spelled label s) else 0 := by
  have hc (w : Fin n → α) : wordCoefficient label weight (List.ofFn w) =
      ∑ s : BoundedSequences Γ n,
        if spelled label s = List.ofFn w then seqWeight weight s else 0 := by
    have helper (v : List α) (m : ℕ) (hm : v.length = m) :
        wordCoefficient label weight v = ∑ s : BoundedSequences Γ m,
          if spelled label s = v then seqWeight weight s else 0 := by
      subst m
      rfl
    exact helper _ _ List.length_ofFn
  simp_rw [hc, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have he (w : Fin n → α) :
      (if spelled label s = List.ofFn w then seqWeight weight s else 0) * F (List.ofFn w) =
        if List.ofFn w = spelled label s then seqWeight weight s * F (spelled label s) else 0 := by
    split_ifs <;> simp_all
  simp_rw [he]
  exact sum_words_eq (spelled label s) n _

end
end SourceBurnside.Automaton

end

end OAI
