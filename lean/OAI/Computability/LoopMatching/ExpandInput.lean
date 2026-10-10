import OAI.Computability.LoopMatching.Model
import Mathlib.Data.List.Nodup

namespace OAI

/-! Polynomial-time approximation of weighted matchings with singleton loops. -/

namespace LoopMatching

def crossRecord (n : ℕ) (r : LoopRecord) (d : ℕ) : BinaryMatching.Record :=
  ⟨r.vertex, n + d, r.multiplicity⟩

def crossRecords (n j : ℕ) (rs : List LoopRecord) : List BinaryMatching.Record :=
  rs.flatMap fun r => (List.range j).map (crossRecord n r)

lemma mem_crossRecords {n j : ℕ} {rs : List LoopRecord} {e : BinaryMatching.Record} :
    e ∈ crossRecords n j rs ↔ ∃ r ∈ rs, ∃ d < j, crossRecord n r d = e := by
  simp [crossRecords]

lemma crossRecords_length (n j : ℕ) (rs : List LoopRecord) :
    (crossRecords n j rs).length = rs.length * j := by
  induction rs with
  | nil => simp [crossRecords]
  | cons r rs ih =>
    change (((List.range j).map (crossRecord n r)) ++ crossRecords n j rs).length =
      (rs.length + 1) * j
    rw [List.length_append, List.length_map, List.length_range, ih]
    simp [Nat.add_mul, Nat.add_comm]

lemma crossRecords_unique (n j : ℕ) (rs : List LoopRecord)
    (h : (rs.map LoopRecord.vertex).Nodup) :
    ((crossRecords n j rs).map (fun e => (e.left,e.right))).Nodup := by
  induction rs with
  | nil => simp [crossRecords]
  | cons r rs ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp h
    simp only [crossRecords, List.flatMap_cons, List.map_append, List.map_map]
    apply List.nodup_append.mpr
    refine ⟨?_, ih ht, ?_⟩
    · apply (List.nodup_range (n := j)).map
      intro a b hab
      have hh := congrArg Prod.snd hab
      dsimp [Function.comp_def, crossRecord] at hh
      omega
    · intro a ha b hb hab
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp ha
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp hb
      obtain ⟨s,hs,c,hc,rfl⟩ := mem_crossRecords.mp he
      have hv := congrArg Prod.fst hab
      dsimp [Function.comp_def, crossRecord] at hv
      exact hn (List.mem_map.mpr ⟨s,hs,hv.symm⟩)

def expand (G : Input) (j : ℕ) : BinaryMatching.Input where
  n := G.n + j
  records := G.ordinary.records ++ crossRecords G.n j G.loops
  valid := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨hlt,hbound⟩ := G.ordinary.valid e he
      change e.right < G.n at hbound
      exact ⟨hlt,by omega⟩
    · obtain ⟨r,hr,d,hd,rfl⟩ := mem_crossRecords.mp he
      have hrn := G.valid r hr
      change r.vertex < G.n at hrn
      dsimp [crossRecord]
      constructor <;> omega
  unique := by
    rw [List.map_append]
    apply List.nodup_append.mpr
    refine ⟨G.ordinary.unique, crossRecords_unique _ _ _ G.unique, ?_⟩
    intro a ha b hb hab
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp ha
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hb
    obtain ⟨r,hr,d,hd,rfl⟩ := mem_crossRecords.mp hf
    have hn := (G.ordinary.valid e he).2
    change e.right < G.n at hn
    have hh := congrArg Prod.snd hab
    dsimp [crossRecord] at hh
    omega

@[simp] lemma expand_n (G : Input) (j : ℕ) : (expand G j).n = G.n+j := rfl

@[simp] lemma expand_records_length (G : Input) (j : ℕ) :
    (expand G j).records.length = G.ordinary.records.length + G.loops.length*j := by
  simp [expand, crossRecords_length]

lemma expand_records_length_le (G : Input) {j : ℕ} (hj : j ≤ G.n) :
    (expand G j).records.length ≤ G.ordinary.records.length + G.loops.length*G.n := by
  rw [expand_records_length]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hj) _

def oldPair (G : Input) (j : ℕ) (e : BinaryMatching.Pair G.n) :
    BinaryMatching.Pair (expand G j).n :=
  ⟨(⟨e.val.1.val,by have := e.val.1.isLt; simp only [expand_n]; omega⟩,
    ⟨e.val.2.val,by have := e.val.2.isLt; simp only [expand_n]; omega⟩),e.property⟩

def crossPair (G : Input) (j : ℕ) (v : Fin G.n) (d : Fin j) :
    BinaryMatching.Pair (expand G j).n :=
  ⟨(⟨v.val,by have := v.isLt; simp only [expand_n]; omega⟩,
    ⟨G.n+d.val,by have := d.isLt; simp only [expand_n]; omega⟩),by
      change v.val < G.n+d.val
      have := v.isLt
      omega⟩

def dummyPair (G : Input) (j : ℕ) (e : BinaryMatching.Pair j) :
    BinaryMatching.Pair (expand G j).n :=
  ⟨(⟨G.n+e.val.1.val,by have := e.val.1.isLt; simp only [expand_n]; omega⟩,
    ⟨G.n+e.val.2.val,by have := e.val.2.isLt; simp only [expand_n]; omega⟩),by
      change G.n+e.val.1.val < G.n+e.val.2.val
      have := e.property
      exact Nat.add_lt_add_left this _⟩

private lemma find_some_unique {α : Type*} (p : α → Bool) (xs : List α) (a : α)
    (ha : a ∈ xs) (hp : p a = true) (hu : ∀ b ∈ xs, p b = true → b=a) :
    xs.find? p = some a := by
  cases hf : xs.find? p with
  | none => exact False.elim ((List.find?_eq_none.mp hf a ha) hp)
  | some b =>
    have hb := hu b (List.mem_of_find?_eq_some hf) (List.find?_some hf)
    exact congrArg some hb

private lemma find_cross_block (n j i d : ℕ) (r : LoopRecord) (hd : d<j) :
    ((List.range j).map (crossRecord n r)).find?
      (fun e => e.left=i && e.right=n+d) =
      if r.vertex=i then some (crossRecord n r d) else none := by
  by_cases hi : r.vertex=i
  · rw [ite_eq_left hi]
    apply find_some_unique
    · exact List.mem_map.mpr ⟨d,List.mem_range.mpr hd,rfl⟩
    · simp [crossRecord,hi]
    · intro b hb hp
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
      have he : n+c=n+d := by simpa [crossRecord,hi] using hp
      have : c=d := by omega
      subst c
      rfl
  · rw [ite_eq_right hi]
    apply List.find?_eq_none.mpr
    intro b hb
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
    simp [crossRecord,hi]

private lemma find_crossRecords (n j i d : ℕ) (rs : List LoopRecord) (hd : d<j) :
    (crossRecords n j rs).find? (fun e => e.left=i && e.right=n+d) =
      (rs.find? (fun r => r.vertex == i)).map (fun r => crossRecord n r d) := by
  induction rs with
  | nil => simp [crossRecords]
  | cons r rs ih =>
    change ((((List.range j).map (crossRecord n r)) ++ crossRecords n j rs).find?
      (fun e => e.left=i && e.right=n+d)) =
      ((r :: rs).find? (fun r => r.vertex == i)).map (fun r => crossRecord n r d)
    rw [List.find?_append, find_cross_block n j i d r hd]
    by_cases hi : r.vertex=i
    · simp [hi]
    · simp [hi, ih]

lemma multiplicity_expand_old (G : Input) (j : ℕ) (e : BinaryMatching.Pair G.n) :
    BinaryMatching.multiplicity (expand G j) (oldPair G j e) =
      BinaryMatching.multiplicity G.ordinary e := by
  have hn : (crossRecords G.n j G.loops).find?
      (fun r => r.left=e.val.1.val && r.right=e.val.2.val) = none := by
    apply List.find?_eq_none.mpr
    intro r hr
    obtain ⟨s,hs,d,hd,rfl⟩ := mem_crossRecords.mp hr
    have he := e.val.2.isLt
    have hne : G.n+d ≠ e.val.2.val := by omega
    simp [crossRecord,hne]
  change (match (G.ordinary.records ++ crossRecords G.n j G.loops).find?
      (fun r => r.left=e.val.1.val && r.right=e.val.2.val) with
      | none => 0 | some r => r.multiplicity) =
    (match G.ordinary.records.find?
      (fun r => r.left=e.val.1.val && r.right=e.val.2.val) with
      | none => 0 | some r => r.multiplicity)
  rw [List.find?_append, hn]
  cases G.ordinary.records.find? (fun r => r.left=e.val.1.val && r.right=e.val.2.val) <;> rfl

lemma multiplicity_expand_cross (G : Input) (j : ℕ) (v : Fin G.n) (d : Fin j) :
    BinaryMatching.multiplicity (expand G j) (crossPair G j v d) = loopMultiplicity G v := by
  have hn : G.ordinary.records.find?
      (fun r => r.left=v.val && r.right=G.n+d.val) = none := by
    apply List.find?_eq_none.mpr
    intro r hr
    have hb := (G.ordinary.valid r hr).2
    change r.right < G.n at hb
    have hne : r.right ≠ G.n+d.val := by omega
    simp [hne]
  change (match (G.ordinary.records ++ crossRecords G.n j G.loops).find?
      (fun r => r.left=v.val && r.right=G.n+d.val) with
      | none => 0 | some r => r.multiplicity) = loopMultiplicity G v
  rw [List.find?_append, hn]
  change (match (crossRecords G.n j G.loops).find?
      (fun r => r.left=v.val && r.right=G.n+d.val) with
      | none => 0 | some r => r.multiplicity) = _
  rw [find_crossRecords G.n j v.val d.val G.loops d.isLt]
  unfold loopMultiplicity
  cases G.loops.find? (fun r => r.vertex == v.val) <;> rfl

lemma multiplicity_expand_dummy (G : Input) (j : ℕ) (e : BinaryMatching.Pair j) :
    BinaryMatching.multiplicity (expand G j) (dummyPair G j e) = 0 := by
  have hn : (expand G j).records.find?
      (fun r => r.left=G.n+e.val.1.val && r.right=G.n+e.val.2.val) = none := by
    apply List.find?_eq_none.mpr
    intro r hr
    have hb : r.left < G.n := by
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨hlt,hbound⟩ := G.ordinary.valid r hr
        change r.right < G.n at hbound
        omega
      · obtain ⟨s,hs,d,hd,rfl⟩ := mem_crossRecords.mp hr
        exact G.valid s hs
    have hne : r.left ≠ G.n+e.val.1.val := by omega
    simp [hne]
  change (match (expand G j).records.find?
      (fun r => r.left=G.n+e.val.1.val && r.right=G.n+e.val.2.val) with
      | none => 0 | some r => r.multiplicity) = 0
  rw [hn]

end LoopMatching

end OAI
