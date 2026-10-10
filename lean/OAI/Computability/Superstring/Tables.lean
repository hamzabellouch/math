import OAI.Computability.Superstring.Computable

namespace OAI

namespace Superstring.Computable
open BitCode
variable {α : Type} [DecidableEq α] [Inhabited α]

theorem stage_zero (D : Counts.Data α) (n : ℕ) (w : List α)
    (hw : w ∉ D.vertices ∨ w = []) : D.stage n w = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Counts.Data.stage, Counts.Data.step]
    split
    · rename_i hh
      exact False.elim (hw.elim (fun h => h hh.1) (fun h => hh.2 h))
    · rfl

theorem input_stage_bound (S : List (List α)) (n : ℕ) (w : List α) :
    (Input.data S).stage n w ≤ S.flatten.length := by
  by_cases he : w = []
  · rw [stage_zero _ _ _ (Or.inr he)]; exact Nat.zero_le _
  · exact ((Input.data S).stage_le_number S.flatten
      (fun _ hw => List.infix_of_mem_flatten ((Input.mem_core.mp hw).1)) n w).trans
        (Counts.number_le_length he)

def stageTable (S : List (List α)) (n : ℕ) : Table α :=
  (vertices S).map (fun w => (w,(Input.data S).stage n w))

theorem lookup_stageTable (S : List (List α)) (n : ℕ) (w : List α) :
    lookup (stageTable S n) w = (Input.data S).stage n w := by
  rw [stageTable, lookup_map]
  split
  · rfl
  · exact (stage_zero _ _ _ (Or.inl (by
      simpa only [Input.data, ← vertices_eq S, List.mem_toFinset] using ‹w ∉ vertices S›))).symm

/-- Only finite materialized tables are passed between consecutive iterations. -/
def rawCountStep (q : List (List α) × Table α) : List (List α) × Table α :=
  (q.1, tableStep (dataCode q.1) q.2)

def initialTable (S : List (List α)) : Table α := (vertices S).map (fun w => (w,0))

theorem rawCountStep_stage (S : List (List α)) (n : ℕ) :
    rawCountStep (S,stageTable S n) = (S,stageTable S (n+1)) := by
  simp only [rawCountStep, tableStep, dataCode, stageTable, Prod.mk.injEq, true_and]
  apply List.map_congr_left
  intro w _
  congr 1
  have hd : (dataCode S).1.Nodup := nodup_unique _
  have ha : (dataCode S).2.2.Nodup := nodup_unique _
  change step (dataCode S) (stageTable S n) w = _
  rw [step_eq (dataCode S) hd ha, decode_dataCode]
  rw [show lookup (stageTable S n) = (Input.data S).stage n from funext (lookup_stageTable S n)]
  rfl

theorem iterate_rawCountStep (S : List (List α)) (n : ℕ) :
    rawCountStep^[n] (S,initialTable S) = (S,stageTable S n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, rawCountStep_stage]

variable [Coded α]

/-- A proved polynomial workspace guard. The cap is part of the implemented
loop; the mathematical bound proves it never fires on an actual input. -/
def countCap (S : List (List α)) : ℕ :=
  bitSize S + 1 + (vertices S).length * (bitSize (vertices S) + S.flatten.length + 2)

def countDepth (S : List (List α)) : ℕ :=
  ((vertices S).map List.length).foldl Max.max 0 + 1

def computeCounts (S : List (List α)) : Table α :=
  (((cappedStep rawCountStep)^[countDepth S] (countCap S,(S,initialTable S))).2).2

theorem stageTable_size (S : List (List α)) (n : ℕ) :
    bitSize (S,stageTable S n) ≤ countCap S := by
  have h := bitSize_map_le (vertices S) (fun w => (w,(Input.data S).stage n w))
    (bitSize (vertices S) + S.flatten.length + 1) (by
      intro w hw
      have hv := bitSize_mem hw
      have hn := input_stage_bound S n w
      simp only [bitSize_prod, bitSize_nat]
      omega)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h
  simp only [stageTable, bitSize_prod, countCap, Nat.add_assoc]
  omega

theorem computeCounts_eq (S : List (List α)) :
    computeCounts S = (vertices S).map (fun w => (w,(Input.data S).count w)) := by
  have he := iterate_cappedStep_eq rawCountStep (countDepth S) (countCap S)
    (S,initialTable S) (fun j _ _ => by rw [iterate_rawCountStep]; exact stageTable_size S j)
  rw [computeCounts, he, iterate_rawCountStep]
  have hd : countDepth S = (Input.data S).depth + 1 := by
    simp only [countDepth, max_map_finset, vertices_eq, Counts.Data.depth, Input.data]
  simp only [hd, stageTable, Counts.Data.count]

theorem lookup_computeCounts (S : List (List α)) (w : List α) :
    lookup (computeCounts S) w = (Input.data S).count w := by
  rw [computeCounts_eq, lookup_map]
  split
  · rfl
  · exact ((Input.data S).count_zero _ (Or.inl (by
      simpa only [Input.data, ← vertices_eq S, List.mem_toFinset] using ‹w ∉ vertices S›))).symm

omit [Inhabited α] in
@[fun_prop] theorem poly_initialTable : Poly (initialTable : List (List α) → Table α) := by
  unfold initialTable
  exact (BitCode.Poly.map (BitCode.Poly.id.pair (BitCode.Poly.const 0))).comp poly_vertices

@[fun_prop] theorem poly_rawCountStep : Poly (rawCountStep : List (List α) × Table α → _) := by
  unfold rawCountStep
  fun_prop

omit [Inhabited α] in
@[fun_prop] theorem poly_countCap : Poly (countCap : List (List α) → ℕ) := by
  unfold countCap
  fun_prop

omit [Inhabited α] in
@[fun_prop] theorem poly_countDepth : Poly (countDepth : List (List α) → ℕ) := by
  have hm : Poly (fun S : List (List α) => ((vertices S).map List.length).foldl Max.max 0) :=
    BitCode.Poly.maxFold.comp ((BitCode.Poly.map BitCode.Poly.length).comp poly_vertices)
  unfold countDepth
  fun_prop

@[fun_prop] theorem poly_computeCounts : Poly (computeCounts : List (List α) → Table α) := by
  have hp := BitCode.Poly.cappedIterate (poly_rawCountStep (α := α))
  exact BitCode.Poly.snd.comp (hp.comp (poly_countDepth.pair (poly_countCap.pair
    (BitCode.Poly.id.pair poly_initialTable))))

end Superstring.Computable

namespace Superstring.PrefixGreedy

variable {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def Capacity (req : β → List α) (sup : γ → List α) (R : Finset β) (S : Finset γ) : Prop :=
  ∀ w, (R.filter (fun a => w <+: req a)).card ≤ (S.filter (fun b => w <+: sup b)).card

omit [DecidableEq β] [DecidableEq γ] in
theorem exists_supply {req : β → List α} {sup : γ → List α} {R : Finset β} {S : Finset γ}
    (h : Capacity req sup R S) {a : β} (ha : a ∈ R) :
    ∃ b ∈ S, req a <+: sup b := by
  have hc := h (req a)
  have hp : 0 < (R.filter (fun r => req a <+: req r)).card :=
    Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, List.prefix_refl _⟩⟩
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (lt_of_lt_of_le hp hc)
  exact ⟨b, Finset.mem_filter.mp hb⟩

/-- Deleting a longest request and any of its extensions preserves all subtree capacities. -/
theorem capacity_erase {req : β → List α} {sup : γ → List α} {R : Finset β} {S : Finset γ}
    (h : Capacity req sup R S) {a : β} {b : γ} (ha : a ∈ R) (hb : b ∈ S)
    (hm : ∀ r ∈ R, (req r).length ≤ (req a).length) (hp : req a <+: sup b) :
    Capacity req sup (R.erase a) (S.erase b) := by
  intro w
  rw [Finset.filter_erase, Finset.filter_erase]
  by_cases hw : w <+: req a
  · have hwa : a ∈ R.filter (fun r => w <+: req r) := Finset.mem_filter.mpr ⟨ha, hw⟩
    have hwb : b ∈ S.filter (fun r => w <+: sup r) := Finset.mem_filter.mpr ⟨hb, hw.trans hp⟩
    rw [Finset.card_erase_of_mem hwa, Finset.card_erase_of_mem hwb]
    exact Nat.sub_le_sub_right (h w) 1
  · by_cases hwb : w <+: sup b
    · have hz : (R.filter (fun r => w <+: req r)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro r hr
        obtain ⟨hr, hwr⟩ := Finset.mem_filter.mp hr
        apply hw
        exact List.prefix_of_prefix_length_le hwb hp (hwr.length_le.trans (hm r hr))
      rw [hz, Finset.erase_empty, Finset.card_empty]
      exact Nat.zero_le _
    · have hna : a ∉ R.filter (fun r => w <+: req r) := by simp only [Finset.mem_filter]; tauto
      have hnb : b ∉ S.filter (fun r => w <+: sup r) := by simp only [Finset.mem_filter]; tauto
      rw [Finset.erase_eq_of_notMem hna, Finset.erase_eq_of_notMem hnb]
      exact h w

end Superstring.PrefixGreedy

namespace Superstring.PrefixGreedy

abbrev Token (α : Type) := ℕ × List α

def prefer {α : Type} (a b : Token α) : Token α := if a.2.length < b.2.length then b else a

def largest {α : Type} (xs : List (Token α)) : Token α := xs.foldl prefer (xs.headD (0,[]))

theorem fold_prefer {α : Type} (xs : List (Token α)) (a : Token α) :
    xs.foldl prefer a ∈ a :: xs ∧ a.2.length ≤ (xs.foldl prefer a).2.length ∧
      ∀ b ∈ xs, b.2.length ≤ (xs.foldl prefer a).2.length := by
  induction xs generalizing a with
  | nil => simp
  | cons b xs ih =>
    simp only [List.foldl_cons]
    obtain ⟨hm, ha, hx⟩ := ih (prefer a b)
    have hp : prefer a b = a ∨ prefer a b = b := by unfold prefer; split <;> simp
    have hal : a.2.length ≤ (prefer a b).2.length := by unfold prefer; split <;> omega
    have hbl : b.2.length ≤ (prefer a b).2.length := by unfold prefer; split <;> omega
    refine ⟨?_, le_trans hal ha, ?_⟩
    · simp only [List.mem_cons] at hm ⊢
      rcases hm with h | h
      · rw [h]; exact hp.elim Or.inl (fun h => Or.inr (Or.inl h))
      · exact Or.inr (Or.inr h)
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact le_trans hbl ha
      · exact hx c hc

theorem largest_spec {α : Type} (xs : List (Token α)) (hne : xs ≠ []) :
    largest xs ∈ xs ∧ ∀ b ∈ xs, b.2.length ≤ (largest xs).2.length := by
  obtain ⟨hm, _, hb⟩ := fold_prefer xs (xs.headD (0,[]))
  have hh : xs.headD (0,[]) ∈ xs := by cases xs with
    | nil => exact (hne rfl).elim
    | cons a xs => simp
  refine ⟨?_, hb⟩
  change xs.foldl prefer (xs.headD (0,[])) ∈ xs
  exact (List.mem_cons.mp hm).elim (fun h => h.symm ▸ hh) id

variable {α : Type} [DecidableEq α]

def prefixB (a b : List α) : Bool := decide (a <+: b)

def remove (a : Token α) (xs : List (Token α)) : List (Token α) :=
  xs.filter (fun b => decide (b ≠ a))

@[simp] theorem mem_remove (a b : Token α) (xs : List (Token α)) :
    b ∈ remove a xs ↔ b ∈ xs ∧ b ≠ a := by simp [remove]

@[simp] theorem toFinset_remove (a : Token α) (xs : List (Token α)) :
    (remove a xs).toFinset = xs.toFinset.erase a := by
  ext b; simp only [List.mem_toFinset, mem_remove, Finset.mem_erase]; tauto

def extension (a : Token α) (S : List (Token α)) : Token α :=
  (S.filter (fun b => prefixB a.2 b.2)).headD (0,[])

theorem extension_spec {a : Token α} {S : List (Token α)}
    (h : ∃ b ∈ S, a.2 <+: b.2) : extension a S ∈ S ∧ a.2 <+: (extension a S).2 := by
  have hm : extension a S ∈ S.filter (fun b => prefixB a.2 b.2) := by
    have hne : S.filter (fun b => prefixB a.2 b.2) ≠ [] := by
      obtain ⟨b, hb, hp⟩ := h
      intro he
      have hm : b ∈ S.filter (fun b => prefixB a.2 b.2) := by simp [hb, prefixB, hp]
      rw [he] at hm
      exact List.not_mem_nil hm
    unfold extension
    generalize S.filter (fun b => prefixB a.2 b.2) = xs at *
    cases xs with
    | nil => exact (hne rfl).elim
    | cons b xs => simp
  simpa only [List.mem_filter, prefixB, decide_eq_true_eq] using hm

abbrev State (α : Type) := List (Token α) × List (Token α) × List (Token α × Token α)

def step (q : State α) : State α :=
  if q.1.isEmpty then q else
    let a := largest q.1
    let b := extension a q.2.1
    (remove a q.1, remove b q.2.1, (a,b)::q.2.2)

end Superstring.PrefixGreedy

namespace Superstring.PrefixGreedy
variable {α : Type} [DecidableEq α]

theorem remove_nodup (a : Token α) {xs : List (Token α)} (h : xs.Nodup) :
    (remove a xs).Nodup := h.filter _

theorem remove_perm {a : Token α} {xs : List (Token α)} (h : xs.Nodup) (ha : a ∈ xs) :
    xs.Perm (a :: remove a xs) := by
  apply (List.perm_ext_iff_of_nodup h (List.nodup_cons.mpr ⟨by simp, remove_nodup a h⟩)).mpr
  intro b
  simp only [List.mem_cons, mem_remove]
  constructor
  · intro hb; by_cases he : b = a
    · exact Or.inl he
    · exact Or.inr ⟨hb,he⟩
  · rintro (rfl | ⟨hb,_⟩)
    · exact ha
    · exact hb

/-- The explicit greedy loop returns a complete matching, with no search over permutations. -/
theorem iterate_correct (n : ℕ) (R S : List (Token α)) (P : List (Token α × Token α))
    (hR : R.Nodup) (hS : S.Nodup) (hc : Capacity Prod.snd Prod.snd R.toFinset S.toFinset)
    (hlen : R.length = S.length) (hn : R.length ≤ n)
    (hP : ∀ p ∈ P, p.1.2 <+: p.2.2) :
    let q := step^[n] (R,S,P)
    q.1 = [] ∧ q.2.1 = [] ∧
      (q.2.2.map Prod.fst).Perm (R ++ P.map Prod.fst) ∧
      (q.2.2.map Prod.snd).Perm (S ++ P.map Prod.snd) ∧
      ∀ p ∈ q.2.2, p.1.2 <+: p.2.2 := by
  induction n generalizing R S P with
  | zero =>
    have hr : R = [] := List.length_eq_zero_iff.mp (by omega)
    have hs : S = [] := List.length_eq_zero_iff.mp (by omega)
    subst R; subst S
    simpa only [Function.iterate_zero_apply, List.nil_append, true_and] using
      And.intro (List.Perm.refl _) (And.intro (List.Perm.refl _) hP)
  | succ n ih =>
    change _ ∧ _ ∧ _ ∧ _ ∧ _
    rw [Function.iterate_succ_apply]
    by_cases hr : R = []
    · subst R
      have hs : S = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst S
      simpa only [step, List.isEmpty_nil, Bool.true_eq, ite_true] using
        ih [] [] P hR hS hc hlen (Nat.zero_le n) hP
    · let a := largest R
      let b := extension a S
      have ha : a ∈ R := (largest_spec R hr).1
      have hm : ∀ r ∈ R.toFinset, r.2.length ≤ a.2.length := by
        intro r hh; exact (largest_spec R hr).2 r (List.mem_toFinset.mp hh)
      have hex : ∃ b ∈ S, a.2 <+: b.2 := by
        simpa only [List.mem_toFinset] using exists_supply hc (List.mem_toFinset.mpr ha)
      obtain ⟨hb, hp⟩ := extension_spec hex
      have hbS : b ∈ S := hb
      have hmatch : a.2 <+: b.2 := hp
      have hc' : Capacity Prod.snd Prod.snd (remove a R).toFinset (remove b S).toFinset := by
        rw [toFinset_remove, toFinset_remove]
        exact capacity_erase hc (List.mem_toFinset.mpr ha) (List.mem_toFinset.mpr hbS) hm hmatch
      have hrp := remove_perm hR ha
      have hsp := remove_perm hS hbS
      have hlr := hrp.length_eq
      have hls := hsp.length_eq
      simp only [List.length_cons] at hlr hls
      have hsub := ih (remove a R) (remove b S) ((a,b)::P)
        (remove_nodup a hR) (remove_nodup b hS) hc' (by omega) (by omega)
        (by intro p hh; rcases List.mem_cons.mp hh with rfl | hh
            · exact hmatch
            · exact hP p hh)
      have he : step (R,S,P) = (remove a R,remove b S,(a,b)::P) := by
        simp only [step, a, b, List.isEmpty_iff, hr, ite_false]
      rw [he]
      refine ⟨hsub.1, hsub.2.1, ?_, ?_, hsub.2.2.2.2⟩
      · have hh := hsub.2.2.1
        simp only [List.map_cons] at hh
        exact hh.trans (List.perm_middle.trans (hrp.symm.append_right _))
      · have hh := hsub.2.2.2.1
        simp only [List.map_cons] at hh
        exact hh.trans (List.perm_middle.trans (hsp.symm.append_right _))

end Superstring.PrefixGreedy

end OAI
