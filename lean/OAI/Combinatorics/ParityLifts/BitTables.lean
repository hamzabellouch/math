import OAI.Combinatorics.ParityLifts.TableGraphs

namespace OAI

namespace ParityWL.Complexity

abbrev BitFormula := List BitClause
abbrev Name := List Bool

def bitClauseSat (a : Name → Bool) (C : BitClause) : Prop := ∃ l∈C, a l.1=l.2
def bitSat (a : Name → Bool) (F : BitFormula) : Prop := ∀ C∈F, bitClauseSat a C

def names (F : BitFormula) : List Name := F.flatMap (fun C => C.map Prod.fst)

lemma mem_names {F : BitFormula} {v : Name} :
    v∈names F ↔ ∃ C∈F, ∃ l∈C, l.1=v := by simp [names]

lemma idxOf_inj_on {α : Type} [BEq α] [LawfulBEq α] {xs : List α} {a b : α}
    (ha : a∈xs) (hb : b∈xs) (h : xs.idxOf a=xs.idxOf b) : a=b := by
  have hh := congrArg (fun i => xs[i]?) h
  simpa only [List.getElem?_idxOf ha,List.getElem?_idxOf hb,Option.some.injEq] using hh

lemma findIndex_idxOf {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (xs : List α) (a : α) :
    findIndex (fun b => decide (b=a)) xs = xs.idxOf a := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    rw [findIndex_cons,List.idxOf_cons,ih]
    by_cases h : b=a
    · subst b; simp
    · have hb : (b == a) = false := beq_eq_false_iff_ne.mpr h
      simp [h,hb,Nat.add_comm]

def lookupBits (vs : List Name) (bs : List Bool) (v : Name) : Bool :=
  bs[vs.idxOf v]?.getD false

lemma lookupBits_map (vs : List Name) (a : Name → Bool) (xs : List Bool) (v : Name) (hv : v∈vs) :
    lookupBits vs (vs.map a ++ xs) v = a v := by
  have hi := List.idxOf_lt_length_of_mem hv
  unfold lookupBits
  rw [List.getElem?_append_left (by simpa using hi), List.getElem?_map, List.getElem?_idxOf hv]
  rfl

lemma bitSat_congr {F : BitFormula} {a b : Name → Bool}
    (h : ∀ v∈names F, a v=b v) : bitSat a F ↔ bitSat b F := by
  constructor <;> intro hs C hC
  · obtain ⟨l,hl,he⟩ := hs C hC
    exact ⟨l,hl, (h l.1 (mem_names.mpr ⟨C,hC,l,hl,rfl⟩)).symm.trans he⟩
  · obtain ⟨l,hl,he⟩ := hs C hC
    exact ⟨l,hl, (h l.1 (mem_names.mpr ⟨C,hC,l,hl,rfl⟩)).trans he⟩

def satisfyingWords (d : ℕ) (F : BitFormula) : List (List Bool) :=
  (words d).filter (fun bs => F.all (fun C => C.any (fun l => lookupBits (names F) bs l.1 == l.2)))

@[simp] lemma mem_satisfyingWords (d : ℕ) (F : BitFormula) (bs : List Bool) :
    bs∈satisfyingWords d F ↔ bs.length=d ∧ bitSat (lookupBits (names F) bs) F := by
  simp [satisfyingWords,bitSat,bitClauseSat,List.all_eq_true,List.any_eq_true]

/-- The canonical smaller group's variable list fixes the order in a pair key.
The shared-variable mask is identical on the two sides. -/
def pairKey {t : ℕ} (Q : Fin t → BitFormula) (d : ℕ) (i j : Fin t) (bs : List Bool) : List Bool :=
  let lo := names (Q (min i j))
  let hi := names (Q (max i j))
  lo.map (fun v => if v∈hi then lookupBits (names (Q i)) bs v else false) ++
    List.replicate (d-lo.length) false

lemma pairKey_length {t : ℕ} (Q : Fin t → BitFormula) (d : ℕ)
    (hd : ∀ i, (names (Q i)).length≤d) (i j : Fin t) (bs : List Bool) :
    (pairKey Q d i j bs).length=d := by
  simp [pairKey]
  exact Nat.add_sub_of_le (hd _)

lemma pairKey_symm_iff {t : ℕ} (Q : Fin t → BitFormula) (d : ℕ) (i j : Fin t)
    (bs cs : List Bool) : pairKey Q d i j bs = pairKey Q d j i cs ↔
      ∀ v, v∈names (Q i) → v∈names (Q j) →
        lookupBits (names (Q i)) bs v = lookupBits (names (Q j)) cs v := by
  unfold pairKey
  rw [min_comm j i,max_comm j i]
  rw [List.append_cancel_right_eq,List.map_eq_map_iff]
  constructor
  · intro h v hi hj
    rcases le_total i j with hij | hji
    · have hh := h v (by simpa [min_eq_left hij] using hi)
      simpa [max_eq_right hij,hj] using hh
    · have hh := h v (by simpa [min_eq_right hji] using hj)
      simpa [max_eq_left hji,hi] using hh
  · intro h v hv
    by_cases hw : v∈names (Q (max i j))
    · simp only [hw,↓reduceIte]
      apply h v
      · rcases le_total i j with hij | hji
        · simpa [min_eq_left hij] using hv
        · simpa [max_eq_left hji] using hw
      · rcases le_total i j with hij | hji
        · simpa [max_eq_right hij] using hw
        · simpa [min_eq_right hji] using hv
    · simp [hw]

def rowKey {t : ℕ} (Q : Fin t → BitFormula) (d : ℕ) (i : Fin t) (bs : List Bool) : Fin t → ℕ :=
  fun j => (words d).idxOf (pairKey Q d i j bs)

def bitChoiceData {t : ℕ} (Q : Fin t → BitFormula) (d : ℕ) : ChoiceData t :=
  (fun i => (satisfyingWords d (Q i)).map (rowKey Q d i), fun _ _ => (words d).length)

lemma ChoiceData.success_rows {t : ℕ} (D : ChoiceData t) :
    D.system.Successful ↔ ∃ rows : Fin t → Fin t → ℕ,
      (∀ i, rows i∈D.1 i) ∧ ∀ i j, i<j →
        min (rows i j) (D.pairBound i j) = min (rows j i) (D.pairBound j i) := by
  classical
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨fun i => (D.1 i).get (a i),fun i => List.get_mem ..,?_⟩
    intro i j hij
    have hh := congrArg Fin.val (ha ⟨(i,j),hij⟩)
    simp only [ChoiceData.system,label,entry, List.getElem?_eq_getElem (a i).isLt,
      List.getElem?_eq_getElem (a j).isLt, Option.getD_some] at hh
    exact hh

  · rintro ⟨rows,hr,he⟩
    choose a ha using fun i => List.mem_iff_get.mp (hr i)
    refine ⟨a,?_⟩
    intro p
    apply Fin.ext
    have hh := he p.1.1 p.1.2 p.2
    simpa [List.get_eq_getElem,ChoiceData.system,label,entry,← ha,List.getElem?_eq_getElem (a p.1.1).isLt,
      List.getElem?_eq_getElem (a p.1.2).isLt] using hh

lemma bitChoiceData_success_iff {t : ℕ} (Q : Fin t → BitFormula) (d : ℕ)
    (hd : ∀ i, (names (Q i)).length≤d) :
    (bitChoiceData Q d).system.Successful ↔
      ∃ bs : Fin t → List Bool,
        (∀ i, bs i∈satisfyingWords d (Q i)) ∧
        ∀ i j v, v∈names (Q i) → v∈names (Q j) →
          lookupBits (names (Q i)) (bs i) v = lookupBits (names (Q j)) (bs j) v := by
  classical
  rw [ChoiceData.success_rows]
  constructor
  · rintro ⟨rows,hr,he⟩
    choose bs hbs hrow using fun i => List.mem_map.mp (hr i)
    refine ⟨bs,hbs,?_⟩
    have he' (i j : Fin t) (hij : i<j) : pairKey Q d i j (bs i) = pairKey Q d j i (bs j) := by
      have hh := he i j hij
      rw [← hrow i,← hrow j] at hh
      simp only [rowKey,bitChoiceData,ChoiceData.pairBound] at hh
      rw [min_eq_left List.idxOf_le_length,min_eq_left List.idxOf_le_length] at hh
      exact idxOf_inj_on ((mem_words ..).mpr (pairKey_length Q d hd ..))
        ((mem_words ..).mpr (pairKey_length Q d hd ..)) hh
    intro i j v hi hj
    rcases lt_trichotomy i j with hij | hij | hij
    · exact (pairKey_symm_iff Q d i j (bs i) (bs j)).mp (he' i j hij) v hi hj
    · subst j; rfl
    · exact ((pairKey_symm_iff Q d j i (bs j) (bs i)).mp (he' j i hij) v hj hi).symm
  · rintro ⟨bs,hbs,he⟩
    refine ⟨fun i => rowKey Q d i (bs i),fun i => List.mem_map.mpr ⟨bs i,hbs i,rfl⟩,?_⟩
    intro i j hij
    have hh := (pairKey_symm_iff Q d i j (bs i) (bs j)).mpr (he i j)
    simp only [rowKey,bitChoiceData,ChoiceData.pairBound,hh]

/-- The finite unary tables implement SAT gluing, including empty clauses and
empty groups; no promise of nonempty domains is introduced. -/
theorem bitChoiceData_correct {t : ℕ} (Q : Fin t → BitFormula) (d : ℕ)
    (hd : ∀ i, (names (Q i)).length≤d) :
    (bitChoiceData Q d).system.Successful ↔ ∃ a : Name → Bool, ∀ i, bitSat a (Q i) := by
  classical
  rw [bitChoiceData_success_iff Q d hd]
  constructor
  · rintro ⟨bs,hbs,he⟩
    let a : Name → Bool := fun v => if h : ∃ i, v∈names (Q i) then
      lookupBits (names (Q h.choose)) (bs h.choose) v else false
    refine ⟨a,?_⟩
    intro i
    have hi := (mem_satisfyingWords d (Q i) (bs i)).mp (hbs i)
    apply (bitSat_congr (fun v hv => ?_)).mp hi.2
    dsimp [a]
    rw [dite_eq_left ⟨i,hv⟩]
    exact he _ _ _ hv (Exists.choose_spec (show ∃ j, v∈names (Q j) from ⟨i,hv⟩))
  · rintro ⟨a,ha⟩
    let bs := fun i => (names (Q i)).map a ++ List.replicate (d-(names (Q i)).length) false
    have hb (i : Fin t) (v : Name) (hv : v∈names (Q i)) :
        lookupBits (names (Q i)) (bs i) v=a v := lookupBits_map _ _ _ _ hv
    refine ⟨bs,?_,?_⟩
    · intro i
      rw [mem_satisfyingWords]
      refine ⟨?_, (bitSat_congr (hb i)).mpr (ha i)⟩
      simp [bs]
      exact Nat.add_sub_of_le (hd i)
    · intro i j v hi hj
      exact (hb i v hi).trans (hb j v hj).symm

end ParityWL.Complexity

end OAI
