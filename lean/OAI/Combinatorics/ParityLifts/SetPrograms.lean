import OAI.Combinatorics.ParityLifts.SetLists

namespace OAI

namespace ParityWL.Complexity

noncomputable def PolyProgram.clauseSubset (α : Type) [TreeCodec α] [DecidableEq α] :
    PolyProgram (List α × List α) Bool (fun x => decide (x.1.toFinset⊆x.2.toFinset)) :=
  (PolyProgram.subset α).congr (by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,Finset.subset_iff,List.mem_toFinset])

noncomputable def PolyProgram.minimalClause (α : Type) [TreeCodec α] [DecidableEq α] :
    PolyProgram (List α × ClauseList α) Bool
      (fun x => x.2.all (fun D => !decide (D.toFinset⊆x.1.toFinset) || decide (x.1.toFinset⊆D.toFinset))) := by
  let sw : PolyProgram (List α × List α) (List α × List α) (fun x => (x.2,x.1)) :=
    .expr (.pair TExpr.input.right TExpr.input.left) (by intro x; rfl)
  let P := (((PolyProgram.clauseSubset α).comp PolyProgram.not).pair
    (sw.comp (PolyProgram.clauseSubset α))).comp PolyProgram.or
  let sw' : PolyProgram (List α × ClauseList α) (ClauseList α × List α) (fun x => (x.2,x.1)) :=
    .expr (.pair TExpr.input.right TExpr.input.left) (by intro x; rfl)
  exact (sw'.comp (P.mapWith.comp (PolyProgram.id Bool).all)).congr
    (by intro x; simp only [Function.comp_def,List.all_map,id_eq])

noncomputable def PolyProgram.minimizeList (α : Type) [TreeCodec α] [DecidableEq α] :
    PolyProgram (ClauseList α) (ClauseList α) Complexity.minimizeList :=
  (((PolyProgram.compactCNF α).pair (PolyProgram.id (ClauseList α))).comp
    (PolyProgram.minimalClause α).filterWith).congr (by intro F; rfl)

noncomputable def PolyProgram.keepClause (α : Type) [TreeCodec α] [DecidableEq α] :
    PolyProgram (List α × ClauseList α) Bool
      (fun x => !(x.2.any (fun D => decide (D.toFinset⊆x.1.toFinset)))) := by
  let sw : PolyProgram (List α × ClauseList α) (ClauseList α × List α) (fun x => (x.2,x.1)) :=
    .expr (.pair TExpr.input.right TExpr.input.left) (by intro x; rfl)
  exact ((sw.comp ((PolyProgram.clauseSubset α).mapWith.comp (PolyProgram.id Bool).any)).comp
    PolyProgram.not).congr (by intro x; simp only [Function.comp_def,List.any_map,id_eq])

noncomputable def PolyProgram.pruneList (α : Type) [TreeCodec α] [DecidableEq α] :
    PolyProgram (ClauseList α × ClauseList α) (ClauseList α) (fun x => Complexity.pruneList x.1 x.2) := by
  let P := (PolyProgram.keepClause α).filterWith
  exact (((P.pair (PolyProgram.snd (ClauseList α) (ClauseList α))).comp (PolyProgram.append (List α))).comp
    (PolyProgram.compactCNF α)).congr (by intro x; rfl)

def allTuples {α : Type} : ℕ → List α → List (List α)
  | 0, _ => [[]]
  | n+1, xs => xs.flatMap (fun a => (allTuples n xs).map (a::·))

lemma mem_allTuples {α : Type} (n : ℕ) (xs bs : List α) :
    bs∈allTuples n xs ↔ bs.length=n ∧ bs⊆xs := by
  induction n generalizing bs with
  | zero => simp only [allTuples,List.mem_singleton,List.length_eq_zero_iff]
            exact ⟨fun h => ⟨h,by simp [h]⟩,fun h => h.1⟩
  | succ n ih =>
    cases bs with
    | nil => simp [allTuples]
    | cons a bs =>
      simp only [allTuples,List.mem_flatMap,List.mem_map,List.cons.injEq]
      constructor
      · rintro ⟨b,hb,cs,hcs,rfl,rfl⟩
        obtain ⟨hn,hs⟩ := (ih cs).mp hcs
        exact ⟨by simp [hn],by simpa using (show b∈xs ∧ cs⊆xs from ⟨hb,hs⟩)⟩
      · rintro ⟨hn,hs⟩
        have hmem : a∈xs := hs (by simp)
        have hsub : bs⊆xs := fun b hb => hs (by simp [hb])
        exact ⟨a,hmem,bs,(ih bs).mpr ⟨by simpa using hn,hsub⟩,rfl,rfl⟩

lemma allTuples_length {α : Type} (n : ℕ) (xs : List α) :
    (allTuples n xs).length=xs.length^n := by
  induction n with
  | zero => simp [allTuples]
  | succ n ih =>
    simp only [allTuples,List.length_flatMap,List.length_map,ih,pow_succ]
    rw [List.map_const',List.sum_replicate]
    change xs.length * xs.length ^ n = xs.length ^ n * xs.length
    exact Nat.mul_comm ..

def PolyProgram.prependAll (α : Type) [TreeCodec α] :
    PolyProgram (α × List (List α)) (List (List α)) (fun x => x.2.map (x.1::·)) := by
  let sw : PolyProgram (List α × α) (α × List α) (fun x => (x.2,x.1)) :=
    .expr (.pair TExpr.input.right TExpr.input.left) (by intro x; rfl)
  let sw' : PolyProgram (α × List (List α)) (List (List α) × α) (fun x => (x.2,x.1)) :=
    .expr (.pair TExpr.input.right TExpr.input.left) (by intro x; rfl)
  exact sw'.comp (sw.comp (PolyProgram.cons α)).mapWith

def PolyProgram.allTuples (α : Type) [TreeCodec α] :
    (n : ℕ) → PolyProgram (List α) (List (List α)) (Complexity.allTuples n)
  | 0 => PolyProgram.const [[]]
  | n+1 => (((PolyProgram.id (List α)).pair (PolyProgram.allTuples α n)).comp
      (PolyProgram.prependAll α).mapWith |>.comp (PolyProgram.flatten (List α))).congr
        (by intro xs; simp only [Complexity.allTuples,Function.comp_def,List.flatMap_def,id_eq])

noncomputable def clauseDiff {α : Type} [DecidableEq α] (C D : List α) : List α :=
  C.filter (fun a => decide (a∉D))

@[simp] lemma clauseDiff_set {α : Type} [DecidableEq α] (C D : List α) :
    (clauseDiff C D).toFinset=C.toFinset\D.toFinset := by
  ext a
  simp [clauseDiff]

noncomputable def PolyProgram.clauseDiff (α : Type) [TreeCodec α] [DecidableEq α] :
    PolyProgram (List α × List α) (List α) (fun x => Complexity.clauseDiff x.1 x.2) :=
  ((PolyProgram.mem α).comp PolyProgram.not).filterWith.congr (by intro x; simp [Complexity.clauseDiff])

noncomputable def PolyProgram.clauseDisjoint (α : Type) [TreeCodec α] [DecidableEq α] :
    PolyProgram (List α × List α) Bool (fun x => decide (Disjoint x.1.toFinset x.2.toFinset)) := by
  refine (((PolyProgram.mem α).mapWith.comp (PolyProgram.id Bool).any).comp PolyProgram.not).congr ?_
  intro x
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_def,id_eq,List.any_map,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,List.any_eq_true,decide_eq_true_eq]
  simp only [Finset.disjoint_left,List.mem_toFinset,not_exists,not_and]

end ParityWL.Complexity

end OAI
