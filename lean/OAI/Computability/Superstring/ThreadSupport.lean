import OAI.Computability.Superstring.PrefixMatching

namespace OAI

namespace Superstring.ArrayPerm
open BitCode

abbrev Edges := List (ℕ × ℕ)

def Valid (n : ℕ) (E : Edges) : Prop :=
  (E.map Prod.fst).Perm (List.range n) ∧ (E.map Prod.snd).Perm (List.range n)

def next (E : Edges) (i : ℕ) : ℕ :=
  ((E.filter (fun e => equal e.1 i)).headD (0,0)).2

@[fun_prop] theorem poly_next : Poly (fun q : Edges × ℕ => next q.1 q.2) := by
  unfold next
  exact BitCode.Poly.snd.comp ((BitCode.Poly.headD (0,0)).comp (BitCode.Poly.filterFn
    (p := fun q : (Edges × ℕ) × (ℕ × ℕ) => equal q.2.1 q.1.2)
    (by fun_prop) BitCode.Poly.fst))

theorem next_mem {n : ℕ} {E : Edges} (h : Valid n E) {i : ℕ} (hi : i < n) :
    (i,next E i) ∈ E := by
  have hm : i ∈ E.map Prod.fst := h.1.mem_iff.mpr (List.mem_range.mpr hi)
  obtain ⟨e,he,hi'⟩ := List.mem_map.mp hm
  have hx : e ∈ E.filter (fun e => equal e.1 i) := by
    simp only [List.mem_filter, equal, decide_eq_true_eq]
    exact ⟨he,hi'⟩
  have hn : E.filter (fun e => equal e.1 i) ≠ [] := by
    intro he'; rw [he'] at hx; exact List.not_mem_nil hx
  have hh : (E.filter (fun e => equal e.1 i)).headD (0,0) ∈ E.filter (fun e => equal e.1 i) := by
    generalize E.filter (fun e => equal e.1 i) = L at *
    cases L with
    | nil => exact (hn rfl).elim
    | cons a L => simp
  obtain ⟨hh,heq⟩ := List.mem_filter.mp hh
  have heq' : ((E.filter (fun e => equal e.1 i)).headD (0,0)).1 = i := by
    exact of_decide_eq_true heq
  have hh' : (i, next E i) = ((E.filter (fun e => equal e.1 i)).headD (0,0)) :=
    Prod.ext heq'.symm rfl
  rw [hh']
  exact hh

theorem next_lt {n : ℕ} {E : Edges} (h : Valid n E) {i : ℕ} (hi : i < n) : next E i < n := by
  have hm := List.mem_map_of_mem (f := Prod.snd) (next_mem h hi)
  exact List.mem_range.mp (h.2.mem_iff.mp hm)

theorem next_injective {n : ℕ} {E : Edges} (h : Valid n E) {i j : ℕ}
    (hi : i < n) (hj : j < n) (he : next E i = next E j) : i = j := by
  have hn : (E.map Prod.snd).Nodup := h.2.nodup_iff.mpr List.nodup_range
  have hh := List.inj_on_of_nodup_map hn (next_mem h hi) (next_mem h hj) he
  exact congrArg Prod.fst hh

noncomputable def perm {n : ℕ} {E : Edges} (h : Valid n E) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun i => ⟨next E i.val, next_lt h i.isLt⟩)
    ((Fintype.bijective_iff_injective_and_card (f := fun i : Fin n =>
      (⟨next E i.val, next_lt h i.isLt⟩ : Fin n))).mpr ⟨by
        intro i j he
        exact Fin.ext (next_injective h i.isLt j.isLt (congrArg Fin.val he)), rfl⟩)

@[simp] theorem perm_apply {n : ℕ} {E : Edges} (h : Valid n E) (i : Fin n) :
    (perm h i).val = next E i.val := rfl


theorem next_size (E : Edges) (i : ℕ) : bitSize (next E i) ≤ bitSize E + 2 := by
  let L := E.filter (fun e => equal e.1 i)
  by_cases hn : L = []
  · change bitSize (L.headD (0,0)).2 ≤ _
    rw [hn]
    simp only [List.headD_nil, bitSize_nat]
    omega
  · have hm : L.headD (0,0) ∈ L := by
      cases hL : L with
      | nil => exact (hn hL).elim
      | cons a l => simp
    have hb := bitSize_mem ((List.mem_filter.mp hm).1)
    have hh : ∀ a : ℕ × ℕ, bitSize a.2 ≤ bitSize a := by
      rintro ⟨a,b⟩
      simp only [bitSize_prod]
      omega
    change bitSize (L.headD (0,0)).2 ≤ _
    exact (hh _).trans (hb.trans (Nat.le_add_right _ _))

def advance (q : Edges × ℕ) : Edges × ℕ := (q.1,next q.1 q.2)

@[fun_prop] theorem poly_advance : Poly advance := by unfold advance; fun_prop

theorem iterate_advance (E : Edges) (i n : ℕ) :
    advance^[n] (E,i) = (E,(next E)^[n] i) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']; rfl

@[fun_prop] theorem poly_iterate_advance : Poly (fun q : ℕ × (Edges × ℕ) => advance^[q.1] q.2) := by
  apply BitCode.Poly.iterate poly_advance (2 * Polynomial.X + 2)
  rintro n ⟨E,i⟩ j _
  rw [iterate_advance, bitSize_prod]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, bitSize_prod, bitSize_nat]
  cases j with
  | zero => simp only [Function.iterate_zero_apply]; omega
  | succ j =>
    rw [Function.iterate_succ_apply']
    have hh := next_size E ((next E)^[j] i)
    simp only [bitSize_nat] at hh
    omega

def power (E : Edges) (n i : ℕ) : ℕ := (next E)^[n] i

@[fun_prop] theorem poly_power : Poly (fun q : Edges × ℕ × ℕ => power q.1 q.2.1 q.2.2) := by
  have hh : Poly (fun q : Edges × ℕ × ℕ => (advance^[q.2.1] (q.1,q.2.2)).2) := by fun_prop
  simpa only [iterate_advance, power] using hh

theorem power_perm {n : ℕ} {E : Edges} (h : Valid n E) (k : ℕ) (i : Fin n) :
    power E k i.val = ((perm h ^ k) i).val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [power, Function.iterate_succ_apply']
    change next E (power E k i.val) = _
    rw [ih, pow_succ', Equiv.Perm.mul_apply, perm_apply]

theorem power_lt {n : ℕ} {E : Edges} (h : Valid n E) (k i : ℕ) (hi : i < n) :
    power E k i < n := by
  rw [power_perm h k ⟨i,hi⟩]
  exact ((perm h ^ k) ⟨i,hi⟩).isLt

end Superstring.ArrayPerm
namespace Superstring.Computable
open BitCode
variable {α : Type} [Coded α]

@[fun_prop] theorem poly_replicate : Poly (fun q : ℕ × α => List.replicate q.1 q.2) := by
  have hp := BitCode.Poly.mapFn (f := fun q : (ℕ × α) × ℕ => q.1.2)
    (by fun_prop) (BitCode.Poly.range.comp BitCode.Poly.fst)
  simpa only [Function.comp_apply, List.map_const', List.length_range] using hp

def indexed {α : Type} (xs : List (List α)) : List (PrefixGreedy.Token α) :=
  (List.range xs.length).map (fun i => (i,xs[i]?.getD []))

@[fun_prop] theorem poly_indexed : Poly (indexed : List (List α) → _) := by
  unfold indexed
  exact BitCode.Poly.mapFn (f := fun q : List (List α) × ℕ => (q.2,q.1[q.2]?.getD []))
    (by exact BitCode.Poly.snd.pair ((BitCode.Poly.getD []).comp BitCode.Poly.id))
    (by fun_prop)

omit [Coded α] in
theorem indexed_fst (xs : List (List α)) : (indexed xs).map Prod.fst = List.range xs.length := by
  simp only [indexed, List.map_map, Function.comp_def]
  exact List.map_id _

omit [Coded α] in
theorem indexed_snd (xs : List (List α)) : (indexed xs).map Prod.snd = xs := by
  apply List.ext_getElem
  · simp only [indexed, List.length_map, List.length_range]
  · intro i hi hi'
    simp only [indexed, List.getElem_map, List.getElem_range, List.getElem?_eq_getElem hi',
      Option.getD_some]

omit [Coded α] in
theorem indexed_nodup (xs : List (List α)) : (indexed xs).Nodup :=
  List.Nodup.of_map Prod.fst (by rw [indexed_fst]; exact List.nodup_range)

omit [Coded α] in
theorem mem_indexed {xs : List (List α)} {i : ℕ} {w : List α} :
    (i,w) ∈ indexed xs ↔ ∃ h : i < xs.length, xs[i] = w := by
  simp only [indexed, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨j,hj,he,hw⟩
    subst j
    exact ⟨hj, by simpa only [List.getElem?_eq_getElem hj, Option.getD_some] using hw⟩
  · rintro ⟨hi,rfl⟩
    exact ⟨i,hi,rfl,by rw [List.getElem?_eq_getElem hi, Option.getD_some]⟩

variable [DecidableEq α] [Inhabited α]

def downValue (S : List (List α)) (w : List α) : ℕ :=
  lookup (computeCounts S) w - right (dataCode S) (computeCounts S) w

@[fun_prop] theorem poly_downValue : Poly (fun q : List (List α) × List α => downValue q.1 q.2) := by
  unfold downValue
  fun_prop

theorem downValue_eq (S : List (List α)) (w : List α) : downValue S w = (Input.data S).down w := by
  unfold downValue Counts.Data.down
  rw [lookup_computeCounts]
  have hh : right (dataCode S) (computeCounts S) w =
      ∑ c ∈ (Input.data S).alphabet, (Input.data S).count (w++[c]) := by
    have hr : right (dataCode S) (computeCounts S) w =
        (decodeData (dataCode S)).right (lookup (computeCounts S)) w := by
      simp only [right, sum_map_finset _ (show (dataCode S).2.2.Nodup from nodup_unique _), member_eq, Counts.Data.right,
        decodeData, List.mem_toFinset]
    rw [hr, decode_dataCode, ← Counts.Data.right_count]
    unfold Counts.Data.right
    apply Finset.sum_congr rfl
    intro c hc
    split
    · exact lookup_computeCounts S _
    · rfl
  rw [hh]

def downWords (S : List (List α)) : List (List α) :=
  ((vertices S).map (fun w => List.replicate (downValue S w) w)).flatten

@[fun_prop] theorem poly_downWords : Poly (downWords : List (List α) → _) := by
  unfold downWords
  exact BitCode.Poly.flatten.comp (BitCode.Poly.mapFn
    (f := fun q : List (List α) × List α => List.replicate (downValue q.1 q.2) q.2)
    (by fun_prop) poly_vertices)

theorem downWords_count (S : List (List α)) (P : List α → Bool) :
    (downWords S).countP P = ∑ w ∈ (Input.data S).vertices,
      if P w then (Input.data S).down w else 0 := by
  unfold downWords
  rw [List.countP_flatten]
  simp only [List.map_map, Function.comp_def, List.countP_replicate, downValue_eq]
  rw [sum_map_finset _ (show (vertices S).Nodup from nodup_unique _) _, vertices_eq]
  rfl


def requests (xs : List (List α)) : List (PrefixGreedy.Token α) :=
  (indexed xs).map (fun t => (t.1,t.2.tail))

omit [DecidableEq α] [Inhabited α] in
@[fun_prop] theorem poly_requests : Poly (requests : List (List α) → _) := by
  unfold requests
  exact (BitCode.Poly.map (by fun_prop)).comp poly_indexed

omit [Coded α] [DecidableEq α] [Inhabited α] in
theorem requests_fst (xs : List (List α)) : (requests xs).map Prod.fst = List.range xs.length := by
  simp only [requests, List.map_map, Function.comp_def]
  exact indexed_fst xs

omit [Coded α] [DecidableEq α] [Inhabited α] in
theorem requests_snd (xs : List (List α)) : (requests xs).map Prod.snd = xs.map List.tail := by
  rw [requests, List.map_map]
  change (indexed xs).map (List.tail ∘ Prod.snd) = _
  rw [← List.map_map, indexed_snd]

omit [Coded α] [DecidableEq α] [Inhabited α] in
theorem requests_nodup (xs : List (List α)) : (requests xs).Nodup :=
  List.Nodup.of_map Prod.fst (by rw [requests_fst]; exact List.nodup_range)

theorem down_capacity (S : List (List α)) :
    PrefixGreedy.Capacity Prod.snd Prod.snd
      (requests (downWords S)).toFinset (indexed (downWords S)).toFinset := by
  intro w
  rw [(requests_nodup _).card_eq_countP, (indexed_nodup _).card_eq_countP]
  change (requests (downWords S)).countP (fun t => decide (w <+: t.2)) ≤
    (indexed (downWords S)).countP (fun t => decide (w <+: t.2))
  have hr := List.countP_map (l := requests (downWords S)) (f := Prod.snd)
    (p := fun t => decide (w <+: t))
  have hs := List.countP_map (l := indexed (downWords S)) (f := Prod.snd)
    (p := fun t => decide (w <+: t))
  dsimp only [Function.comp_def] at hr hs
  rw [← hr, ← hs, requests_snd, indexed_snd, List.countP_map]
  rw [downWords_count, downWords_count]
  have hh := Counts.Data.DownToken.capacity (Input.data S) (Counts.Data.input_wellFormed S) w
  rw [Counts.Data.DownToken.histogram _ (fun v => w <+: v.tail),
    Counts.Data.DownToken.histogram _ (fun v => w <+: v)] at hh
  simpa only [Function.comp_def, decide_eq_true_eq] using hh

def computePairs (S : List (List α)) : List (PrefixGreedy.Token α × PrefixGreedy.Token α) :=
  PrefixGreedy.compute (requests (downWords S)) (indexed (downWords S))

@[fun_prop] theorem poly_computePairs : Poly (computePairs : List (List α) → _) := by
  unfold computePairs
  fun_prop

theorem computePairs_correct (S : List (List α)) :
    ((computePairs S).map Prod.fst).Perm (requests (downWords S)) ∧
    ((computePairs S).map Prod.snd).Perm (indexed (downWords S)) ∧
    ∀ p ∈ computePairs S, p.1.2 <+: p.2.2 := by
  apply PrefixGreedy.compute_correct _ _ (requests_nodup _) (indexed_nodup _) (down_capacity S)
  simp only [requests, List.length_map]

theorem downWords_mem {S : List (List α)} {w : List α} (h : w ∈ downWords S) :
    w ∈ (Input.data S).vertices ∧ w ≠ [] := by
  simp only [downWords, List.mem_flatten, List.mem_map] at h
  obtain ⟨ws, ⟨v,hv,rfl⟩,hw⟩ := h
  have hwV : w = v := List.eq_of_mem_replicate hw
  subst v
  have hp : 0 < (Input.data S).down w := by
    have hh := List.length_pos_of_mem hw
    simpa only [List.length_replicate, downValue_eq] using hh
  refine ⟨?_, ?_⟩
  · change w ∈ Input.vertices S
    rw [← vertices_eq S]
    exact List.mem_toFinset.mpr hv
  · intro he
    subst w
    have hz := (Input.data S).count_zero [] (Or.inr rfl)
    simp only [Counts.Data.down, hz, Nat.zero_sub] at hp
    omega

theorem downWords_length (S : List (List α)) : (downWords S).length = (Input.data S).weight := by
  have hh := downWords_count S (fun _ => true)
  simp only [List.countP_true, ite_true] at hh
  rw [hh]
  exact (Input.data S).total_down (Counts.Data.input_wellFormed S)

end Superstring.Computable
namespace Superstring.Computable
open BitCode
variable {α : Type} [Coded α] [DecidableEq α] [Inhabited α]

omit [Coded α] [DecidableEq α] [Inhabited α] in
theorem mem_requests {xs : List (List α)} {i : ℕ} {w : List α} :
    (i,w) ∈ requests xs ↔ ∃ h : i < xs.length, xs[i].tail = w := by
  simp only [requests, List.mem_map]
  constructor
  · rintro ⟨⟨j,v⟩,hj,he⟩
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    obtain ⟨h,rfl⟩ := mem_indexed.mp hj
    exact ⟨h,rfl⟩
  · rintro ⟨h,rfl⟩
    exact ⟨(i,xs[i]),mem_indexed.mpr ⟨h,rfl⟩,rfl⟩

def edges (S : List (List α)) : ArrayPerm.Edges :=
  (computePairs S).map (fun p => (p.1.1,p.2.1))

@[fun_prop] theorem poly_edges : Poly (edges : List (List α) → _) := by
  unfold edges
  exact (BitCode.Poly.map (by fun_prop)).comp poly_computePairs

theorem edges_valid (S : List (List α)) : ArrayPerm.Valid (downWords S).length (edges S) := by
  obtain ⟨hl,hr,_⟩ := computePairs_correct S
  have hl' := hl.map Prod.fst
  have hr' := hr.map Prod.fst
  rw [requests_fst] at hl'
  rw [indexed_fst] at hr'
  constructor
  · simpa only [edges, List.map_map, Function.comp_def] using hl'
  · simpa only [edges, List.map_map, Function.comp_def] using hr'

theorem edge_follows (S : List (List α)) {i j : ℕ} (he : (i,j) ∈ edges S) :
    ∃ (hi : i < (downWords S).length) (hj : j < (downWords S).length),
      (downWords S)[i].tail <+: (downWords S)[j] := by
  obtain ⟨p,hp,hp'⟩ := List.mem_map.mp he
  have h1 : p.1.1 = i := congrArg Prod.fst hp'
  have h2 : p.2.1 = j := congrArg Prod.snd hp'
  have h := computePairs_correct S
  have hR := h.1.mem_iff.mp (List.mem_map_of_mem (f := Prod.fst) hp)
  have hS := h.2.1.mem_iff.mp (List.mem_map_of_mem (f := Prod.snd) hp)
  obtain ⟨hi,hw1⟩ := mem_requests.mp hR
  obtain ⟨hj,hw2⟩ := mem_indexed.mp hS
  subst i; subst j
  exact ⟨hi,hj,by rw [hw1,hw2]; exact h.2.2 p hp⟩

/-- The actual polynomially computed greedy matching, used as a mathematical
threading. Only its finite inverse proof is noncomputable; the forward table is code. -/
noncomputable def arrayThreading (S : List (List α)) :
    Hierarchical.Threading ((Input.data S).vertices : Set (List α)) (Fin (downWords S).length) where
  word := fun i => (downWords S)[i.val]
  nonempty := fun i => (downWords_mem (List.getElem_mem i.isLt)).2
  mem := fun i => (downWords_mem (List.getElem_mem i.isLt)).1
  next := ArrayPerm.perm (edges_valid S)
  follows := fun i => by
    obtain ⟨hi,hj,hpre⟩ := edge_follows S (ArrayPerm.next_mem (edges_valid S) i.isLt)
    exact hpre

omit [Coded α] [DecidableEq α] [Inhabited α] in
theorem countP_sum (xs : List α) (P : α → Bool) :
    xs.countP P = (xs.map (fun a => if P a then 1 else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.countP_cons, List.map_cons, List.sum_cons, ih]; omega

omit [Coded α] [DecidableEq α] [Inhabited α] in
theorem card_get_filter (xs : List α) (P : α → Bool) :
    (Finset.univ.filter (fun i : Fin xs.length => P xs[i.val])).card = xs.countP P := by
  rw [Finset.card_filter, countP_sum, ← List.ofFn_getElem_eq_map, List.sum_ofFn]

theorem arrayThreading_histogram (S : List (List α)) (P : List α → Bool) :
    (Finset.univ.filter (fun i => P ((arrayThreading S).word i))).card =
      ∑ w ∈ (Input.data S).vertices, if P w then (Input.data S).down w else 0 := by
  change (Finset.univ.filter (fun i : Fin (downWords S).length => P (downWords S)[i.val])).card = _
  rw [card_get_filter, downWords_count]

theorem arrayThreading_recorded_count (S : List (List α)) {w : List α} (hw : w ≠ []) :
    Fintype.card ((arrayThreading S).Recorded w) = (Input.data S).count w := by
  rw [Hierarchical.Threading.card_recorded]
  have hh := arrayThreading_histogram S (fun v => decide (w <+: v))
  simp only [decide_eq_true_eq] at hh
  rw [hh, ← Finset.sum_filter]
  exact (Input.data S).down_descendants (Counts.Data.input_wellFormed S) hw

theorem arrayThreading_budget (S : List (List α)) :
    ∑ g : (arrayThreading S).Groups,
      (arrayThreading S).groupPeriod g *
        Fintype.card ((arrayThreading S).Aligned ((arrayThreading S).groupText g)) =
      (Input.data S).weight := by
  rw [Hierarchical.Threading.sum_layer_periods, Fintype.card_fin, downWords_length]

end Superstring.Computable
namespace Superstring.Hierarchical.Threading
variable {α ι : Type} {V : Set (List α)} [Fintype ι]

/-- A single orbit, not the (potentially exponentially large) order of the
whole permutation, bounds each stored primitive phase word. -/
theorem short_text_period (C : Threading V ι) (i : ι) :
    ∃ p : ℕ, 0 < p ∧ p ≤ Fintype.card ι ∧ Function.Periodic (C.text i) (p : ℤ) := by
  let p := Function.minimalPeriod C.next i
  have hp : 0 < p := Function.minimalPeriod_pos_of_mem_periodicPts (C.next.injective.mem_periodicPts i)
  have hb : p ≤ Fintype.card ι := Function.minimalPeriod_le_card
  have hf : (C.next ^ p) i = i := Function.isPeriodicPt_minimalPeriod C.next i
  refine ⟨p,hp,hb,?_⟩
  intro x
  rw [← C.text_zpow, zpow_natCast, hf]

theorem primitive_le_card (C : Threading V ι) {i : ι} {p : ℕ}
    (hp : Primitive (C.text i) p) : p ≤ Fintype.card ι := by
  obtain ⟨q,hq,hb,hper⟩ := C.short_text_period i
  exact (hp.least q hq hper).trans hb

def finiteKey (C : Threading V ι) (i : ι) : List α :=
  textWord (C.text i) 0 (2 * Fintype.card ι)

theorem length_finiteKey (C : Threading V ι) (i : ι) :
    (C.finiteKey i).length = 2 * Fintype.card ι := by
  simp only [finiteKey, length_textWord, sub_zero]
  omega

theorem finiteKey_get (C : Threading V ι) (i : ι) {k : ℕ} (hk : k < 2 * Fintype.card ι) :
    (C.finiteKey i)[k]? = some (C.text i (k : ℤ)) := by
  have hk' : k < (C.finiteKey i).length := by rw [length_finiteKey]; exact hk
  rw [List.getElem?_eq_getElem hk']
  simp only [finiteKey, textWord, List.getElem_ofFn, zero_add]

theorem finiteKey_eq_iff (C : Threading V ι) (i j : ι) :
    C.finiteKey i = C.finiteKey j ↔ C.text i = C.text j := by
  constructor
  · intro he
    obtain ⟨p,hp,hpb,hpi⟩ := C.short_text_period i
    obtain ⟨q,hq,hqb,hqj⟩ := C.short_text_period j
    apply eq_of_long_agreement (C.text i) (C.text j) p q hp hq hpi hqj 0
    intro x hx hxp
    have hk : x.toNat < 2 * Fintype.card ι := by omega
    have hx' : (x.toNat : ℤ) = x := by omega
    have hh := congrArg (fun w : List α => w[x.toNat]?) he
    rw [finiteKey_get C i hk, finiteKey_get C j hk, hx'] at hh
    exact Option.some.inj hh
  · intro he
    simp only [finiteKey, he]

theorem sameText_bounded (C : Threading V ι) (i j : ι) :
    C.SameText i j ↔ ∃ r : ℕ, r < Fintype.card ι ∧
      C.finiteKey ((C.next ^ r) i) = C.finiteKey j := by
  constructor
  · rintro ⟨d,hd⟩
    obtain ⟨p,hp,hb,hper⟩ := C.short_text_period i
    have hm0 := Int.emod_nonneg d (show (p : ℤ) ≠ 0 by omega)
    have hml := Int.emod_lt_of_pos d (show (0 : ℤ) < p by omega)
    let r := (d % (p : ℤ)).toNat
    have hr : (r : ℤ) = d % (p : ℤ) := by dsimp only [r]; omega
    refine ⟨r,by omega,(C.finiteKey_eq_iff _ _).mpr ?_⟩
    funext x
    rw [← zpow_natCast, C.text_zpow]
    have hh := hper.int_mul (d / (p : ℤ)) (x + r)
    have hm := Int.emod_add_ediv_mul d (p : ℤ)
    have he : x + r + d / (p : ℤ) * p = x + d := by omega
    simp only [Int.cast_id, he] at hh
    exact hh.symm.trans (hd x)
  · rintro ⟨r,_,he⟩
    have hh := (C.finiteKey_eq_iff _ _).mp he
    refine ⟨(r : ℤ),?_⟩
    intro x
    have hv := congrFun hh x
    simpa only [← zpow_natCast, C.text_zpow] using hv

end Superstring.Hierarchical.Threading


namespace Superstring.ThreadArray
open BitCode Hierarchical
variable {α : Type} [Coded α] [DecidableEq α] [Inhabited α]

abbrev Code (α : Type) := List (List α) × ArrayPerm.Edges

/-- Finite array semantics: no periodic/oracle tests are hidden in the code. -/
structure Represents {V : Set (List α)} (K : Code α)
    (C : Threading V (Fin K.1.length)) : Prop where
  word : ∀ i, C.word i = K.1[i.val]
  next : ∀ i, (C.next i).val = ArrayPerm.next K.2 i.val

def key (K : Code α) (i : ℕ) : List α :=
  (List.range (2 * K.1.length)).map (fun r =>
    ((K.1[ArrayPerm.power K.2 r i]?).getD []).headD default)

omit [DecidableEq α] in
@[fun_prop] theorem poly_key : Poly (fun q : Code α × ℕ => key q.1 q.2) := by
  unfold key
  exact BitCode.Poly.mapFn
    (f := fun q : (Code α × ℕ) × ℕ =>
      ((q.1.1.1[ArrayPerm.power q.1.1.2 q.2 q.1.2]?).getD []).headD default)
    (by
      apply (BitCode.Poly.headD default).comp
      exact (BitCode.Poly.getD ([] : List α)).comp
        (f := fun q : (Code α × ℕ) × ℕ =>
          (q.1.1.1, ArrayPerm.power q.1.1.2 q.2 q.1.2)) (by fun_prop)) (by fun_prop)

omit [Coded α] [DecidableEq α] [Inhabited α] in
theorem power_eq {K : Code α} {V : Set (List α)} {C : Threading V (Fin K.1.length)}
    (h : Represents K C) (k : ℕ) (i : Fin K.1.length) :
    ArrayPerm.power K.2 k i.val = ((C.next ^ k) i).val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [ArrayPerm.power, Function.iterate_succ_apply']
    change ArrayPerm.next K.2 (ArrayPerm.power K.2 k i.val) = _
    rw [ih, pow_succ', Equiv.Perm.mul_apply, h.next]

omit [Coded α] [DecidableEq α] in
theorem key_eq {K : Code α} {V : Set (List α)} {C : Threading V (Fin K.1.length)}
    (h : Represents K C) (i : Fin K.1.length) : key K i.val = C.finiteKey i := by
  apply List.ext_getElem
  · simp only [key, List.length_map, List.length_range, Threading.length_finiteKey,
      Fintype.card_fin]
  · intro k hk hk'
    have hki : k < 2 * K.1.length := by
      simpa only [key, List.length_map, List.length_range] using hk
    have ht := C.finiteKey_get i (by simpa only [Fintype.card_fin] using hki)
    rw [List.getElem?_eq_getElem hk'] at ht
    have hr := Option.some.inj ht
    rw [hr]
    simp only [key, List.getElem_map, List.getElem_range, power_eq h]
    rw [List.getElem?_eq_getElem (((C.next ^ k) i).isLt), Option.getD_some, ← h.word]
    simp only [Threading.text, zpow_natCast]
    rw [List.headD_eq_head?_getD, List.head?_eq_some_head]
    rfl

def compatible (K : Code α) (i j : ℕ) : Bool :=
  (List.range K.1.length).any (fun r => equal (key K (ArrayPerm.power K.2 r i)) (key K j))

@[fun_prop] theorem poly_compatible : Poly (fun q : Code α × ℕ × ℕ => compatible q.1 q.2.1 q.2.2) := by
  unfold compatible
  exact BitCode.Poly.anyFn
    (p := fun q : (Code α × ℕ × ℕ) × ℕ =>
      equal (key q.1.1 (ArrayPerm.power q.1.1.2 q.2 q.1.2.1)) (key q.1.1 q.1.2.2))
    (by fun_prop) (by fun_prop)

omit [Coded α] in
theorem compatible_eq {K : Code α} {V : Set (List α)} {C : Threading V (Fin K.1.length)}
    (h : Represents K C) (i j : Fin K.1.length) : compatible K i.val j.val = true ↔ C.SameText i j := by
  rw [C.sameText_bounded]
  simp only [compatible, List.any_eq_true, List.mem_range, equal, decide_eq_true_eq,
    Fintype.card_fin]
  apply exists_congr
  intro r
  rw [power_eq h, key_eq h, key_eq h]

/-- A bounded first-admissible search. Its proof gives both success and order;
it does not assume a choice primitive in the computational model. -/
def first (n : ℕ) (P : ℕ → Bool) : ℕ := ((List.range n).filter P).headD 0

omit [Coded α] [DecidableEq α] [Inhabited α] in
theorem first_spec {n : ℕ} {P : ℕ → Bool} (hw : ∃ k < n, P k = true) :
    first n P < n ∧ P (first n P) = true ∧ ∀ k < n, P k = true → first n P ≤ k := by
  let L := (List.range n).filter P
  have hn : L ≠ [] := by
    obtain ⟨k,hk,hP⟩ := hw
    have hm : k ∈ L := List.mem_filter.mpr ⟨List.mem_range.mpr hk,hP⟩
    intro he; rw [he] at hm; exact List.not_mem_nil hm
  have hs : L.Pairwise (· ≤ ·) := List.pairwise_le_range.filter P
  have hm : L.headD 0 ∈ L := by
    cases hL : L with
    | nil => exact (hn hL).elim
    | cons a l => simp
  obtain ⟨hm,hP⟩ := List.mem_filter.mp hm
  refine ⟨List.mem_range.mp hm,hP,?_⟩
  intro k hk hkP
  have hkm : k ∈ L := List.mem_filter.mpr ⟨List.mem_range.mpr hk,hkP⟩
  change L.headD 0 ≤ k
  cases hL : L with
  | nil => exact (hn hL).elim
  | cons a l =>
    rw [hL] at hs hkm
    simp only [List.headD_cons]
    rcases List.mem_cons.mp hkm with rfl | hk
    · exact le_rfl
    · exact (List.pairwise_cons.mp hs).1 k hk

def period (K : Code α) (i : ℕ) : ℕ :=
  first (K.1.length+1) (fun p => less 0 p && equal (key K (ArrayPerm.power K.2 p i)) (key K i))

@[fun_prop] theorem poly_period : Poly (fun q : Code α × ℕ => period q.1 q.2) := by
  unfold period first
  exact (BitCode.Poly.headD 0).comp (BitCode.Poly.filterFn
    (p := fun q : (Code α × ℕ) × ℕ => less 0 q.2 &&
      equal (key q.1.1 (ArrayPerm.power q.1.1.2 q.2 q.1.2)) (key q.1.1 q.1.2))
    (by fun_prop) (by fun_prop))

omit [Coded α] in
theorem test_period {K : Code α} {V : Set (List α)} {C : Threading V (Fin K.1.length)}
    (h : Represents K C) (i : Fin K.1.length) (p : ℕ) :
    equal (key K (ArrayPerm.power K.2 p i.val)) (key K i.val) = true ↔
      Function.Periodic (C.text i) (p : ℤ) := by
  rw [power_eq h, key_eq h, key_eq h]
  simp only [equal, decide_eq_true_eq, C.finiteKey_eq_iff, funext_iff]
  simp only [← zpow_natCast, C.text_zpow, Function.Periodic]

omit [Coded α] in
theorem period_spec {K : Code α} {V : Set (List α)} {C : Threading V (Fin K.1.length)}
    (h : Represents K C) (i : Fin K.1.length) :
    Primitive (C.text i) (period K i.val) ∧ period K i.val ≤ K.1.length := by
  obtain ⟨p,hp,hpb,hpt⟩ := C.short_text_period i
  have hex : ∃ k < K.1.length+1,
      (less 0 k && equal (key K (ArrayPerm.power K.2 k i.val)) (key K i.val)) = true := by
    refine ⟨p,by simpa only [Fintype.card_fin, Nat.lt_add_one_iff] using hpb,?_⟩
    simp only [Bool.and_eq_true, less, decide_eq_true_eq, test_period h]
    exact ⟨hp,hpt⟩
  have hh := first_spec hex
  change period K i.val < K.1.length+1 ∧ _ at hh
  have ht := hh.2.1
  simp only [Bool.and_eq_true, less, test_period h] at ht
  refine ⟨⟨of_decide_eq_true ht.1,ht.2,?_⟩,by omega⟩
  intro k hk hkt
  by_cases hkn : k < K.1.length+1
  · apply hh.2.2 k hkn
    simp only [Bool.and_eq_true, less, decide_eq_true_eq, test_period h]
    exact ⟨hk,hkt⟩
  · omega

end Superstring.ThreadArray


namespace Superstring.BitCode.Poly
@[fun_prop] theorem div : Poly (fun q : ℕ × ℕ => q.1 / q.2) := by
  have h : Poly (fun q : ℕ × ℕ =>
      if BitCode.equal q.2 0 then 0 else ThreadArray.first (q.1+1) (fun k => BitCode.less q.1 ((k+1)*q.2))) := by
    apply Poly.ite (by fun_prop) (by fun_prop)
    unfold ThreadArray.first
    exact (Poly.headD 0).comp (Poly.filterFn
      (p := fun q : (ℕ × ℕ) × ℕ => BitCode.less q.1.1 ((q.2+1)*q.1.2)) (by fun_prop) (by fun_prop))
  convert h using 1
  funext q
  by_cases hz : q.2 = 0
  · simp only [hz,BitCode.equal,decide_true,↓reduceIte,Nat.div_zero]
  · have hp : 0 < q.2 := Nat.pos_of_ne_zero hz
    simp only [BitCode.equal,decide_eq_true_eq,ite_eq_right hz]
    have hb : q.1 / q.2 < q.1+1 := by have := Nat.div_le_self q.1 q.2; omega
    have ht : BitCode.less q.1 ((q.1/q.2+1)*q.2) = true := by
      apply decide_eq_true
      simpa only [mul_comm] using Nat.lt_mul_div_succ q.1 hp
    obtain ⟨_,hh,hm⟩ := ThreadArray.first_spec (n := q.1+1) (P := fun k => BitCode.less q.1 ((k+1)*q.2)) ⟨q.1/q.2,hb,ht⟩
    apply le_antisymm
    · have he := (Nat.div_lt_iff_lt_mul hp).mpr (show q.1 < (ThreadArray.first (q.1+1) (fun k => BitCode.less q.1 ((k+1)*q.2))+1)*q.2 from of_decide_eq_true hh)
      omega
    · exact hm _ hb ht
end Superstring.BitCode.Poly

end OAI
