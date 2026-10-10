import OAI.Combinatorics.ParityLifts.Words

namespace OAI

namespace ParityWL.Complexity

def PolyProgram.recode {α β γ : Type} [TreeCodec α] [TreeCodec β] [TreeCodec γ]
    {f : α → β} {g : α → γ} (P : PolyProgram α β f)
    (h : ∀ x, treeEncode (f x) = treeEncode (g x)) : PolyProgram α γ g where
  program := {
    code := P.program.code
    time := P.program.time
    run := fun x => by rw [← h x]; exact P.program.run x }
  coefficient := P.coefficient
  degree := P.degree
  bound := P.bound

def PolyProgram.tabulate {α β : Type} [TreeCodec α] [TreeCodec β] {n : ℕ}
    {f : Fin n × α → β} (P : PolyProgram (Fin n × α) β f) :
    PolyProgram α (Fin n → β) (fun x i => f (i,x)) := by
  let Q := ((PolyProgram.const (List.ofFn (_root_.id : Fin n → Fin n))).pair (PolyProgram.id α)).comp P.mapWith
  refine Q.recode ?_
  intro x
  change treeEncode ((List.ofFn (_root_.id : Fin n → Fin n)).map (fun i => f (i,x))) = _
  simp only [List.map_ofFn]
  rfl

def PolyProgram.filterWith {α γ : Type} [TreeCodec α] [TreeCodec γ] {f : α × γ → Bool}
    (P : PolyProgram (α × γ) Bool f) :
    PolyProgram (List α × γ) (List α) (fun x => x.1.filter (fun a => f (a,x.2))) := by
  let R := (PolyProgram.fst α γ).pair P
  let Q : PolyProgram (α × Bool) Bool Prod.snd := PolyProgram.snd α Bool
  refine (R.mapWith.comp Q.filter |>.comp (PolyProgram.fst α Bool).map).congr ?_
  intro x
  simp [List.filter_map, Function.comp_def]

noncomputable def PolyProgram.mem (α : Type) [TreeCodec α] [DecidableEq α] :
    PolyProgram (α × List α) Bool (fun x => decide (x.1∈x.2)) := by
  let swap : PolyProgram (α × List α) (List α × α) (fun x => (x.2,x.1)) :=
    .expr (.pair TExpr.input.right TExpr.input.left) (by intro x; rfl)
  refine (swap.comp (PolyProgram.equal α).mapWith |>.comp (PolyProgram.id Bool).any).congr ?_
  intro x
  simp only [Function.comp_apply, List.any_map]
  change x.2.any (fun a => decide (a=x.1)) = decide (x.1∈x.2)
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨a,ha,he⟩ => he ▸ ha, fun h => ⟨x.1,h,rfl⟩⟩

noncomputable def PolyProgram.subset (α : Type) [TreeCodec α] [DecidableEq α] :
    PolyProgram (List α × List α) Bool (fun x => decide (∀ a∈x.1, a∈x.2)) := by
  refine ((PolyProgram.mem α).mapWith.comp (PolyProgram.id Bool).all).congr ?_
  intro x
  apply Bool.eq_iff_iff.mpr
  simp [List.all_map, List.all_eq_true]

lemma fold_dedup_append {α : Type} [DecidableEq α] (xs acc : List α) :
    (xs.foldl (fun s a => if a∈s then s else a::s) acc).toFinset = xs.toFinset ∪ acc.toFinset := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
    rw [List.foldl_cons, ih]
    by_cases ha : a∈acc
    · simp [ha, Finset.insert_union, Finset.insert_eq_of_mem (Finset.mem_union_right _ (List.mem_toFinset.mpr ha))]
    · simp [ha, Finset.union_insert, Finset.insert_union]

noncomputable def dedupList {α : Type} [DecidableEq α] (xs : List α) : List α :=
  xs.foldl (fun s a => if a∈s then s else a::s) []

@[simp] lemma dedupList_toFinset {α : Type} [DecidableEq α] (xs : List α) :
    (dedupList xs).toFinset = xs.toFinset := by simp [dedupList,fold_dedup_append]

noncomputable def PolyProgram.dedup (α : Type) [TreeCodec α] [DecidableEq α] :
    PolyProgram (List α) (List α) dedupList := by
  let P := (PolyProgram.mem α).ite (PolyProgram.snd α (List α)) (PolyProgram.cons α)
  have hg (a : α) (xs : List α) :
      (treeEncode (if decide (a∈xs) then xs else a::xs)).size ≤
        (treeEncode xs).size+1*((treeEncode a).size+1)^1 := by
    split <;> simp [DataTree.size]
    all_goals omega
  let F := P.foldlGrowing 1 1 hg
  refine (((PolyProgram.id (List α)).pair (PolyProgram.const ([]:List α))).comp F).congr ?_
  intro xs
  simp only [decide_eq_true_eq]
  rfl

/-- First-index search, expressed by one polynomial fold rather than an oracle. -/
def findIndex {α : Type} (p : α → Bool) (xs : List α) : ℕ := xs.takeWhile (fun x => !p x) |>.length

lemma findIndex_nil {α : Type} (p : α → Bool) : findIndex p []=0 := rfl
lemma findIndex_cons {α : Type} (p : α → Bool) (a : α) (xs : List α) :
    findIndex p (a::xs) = if p a then 0 else 1+findIndex p xs := by
  cases h : p a <;> simp [findIndex, h, Nat.add_comm]

lemma fold_findIndex {α : Type} (p : α → Bool) (xs : List α) (n : ℕ) :
    xs.foldr (fun a n => if p a then 0 else n+1) n =
      if xs.any p then findIndex p xs else n+xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases h : p a <;> cases h' : xs.any p <;>
      simp [h,h',List.foldr_cons,ih,findIndex_cons] <;> omega

lemma findIndex_eq_length {α : Type} (p : α → Bool) (xs : List α) (h : xs.any p=false) :
    findIndex p xs=xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have hp : p a=false ∧ xs.any p=false := by simpa using h
    simp [findIndex_cons,hp.1,ih hp.2,Nat.add_comm]

lemma findIndex_le {α : Type} (p : α → Bool) (xs : List α) : findIndex p xs≤xs.length := by
  exact (List.takeWhile_sublist ..).length_le

noncomputable def PolyProgram.findIndexWith {α γ : Type} [TreeCodec α] [TreeCodec γ]
    {p : α × γ → Bool} (P : PolyProgram (α × γ) Bool p) :
    PolyProgram (List α × γ) ℕ (fun x => findIndex (fun a => p (a,x.2)) x.1) := by
  let S := (PolyProgram.fst Bool ℕ).ite (PolyProgram.const 0)
    ((PolyProgram.snd Bool ℕ).comp PolyProgram.natSucc)
  have hg (b : Bool) (n : ℕ) :
      (treeEncode (if b then 0 else n+1)).size ≤ (treeEncode n).size+2*((treeEncode b).size+1)^0 := by
    cases b <;> simp
    all_goals omega
  let F := S.foldlGrowing 2 0 hg
  let Q := ((P.mapWith.comp (PolyProgram.reverse Bool)).pair (PolyProgram.const 0)).comp F
  refine Q.congr ?_
  intro x
  change ((x.1.map (fun a => p (a,x.2))).reverse.foldl (fun n b => if b then 0 else n+1) 0)=_
  rw [← List.foldr_eq_foldl_reverse]
  rw [List.foldr_map]
  rw [fold_findIndex]
  split
  · rfl
  · rename_i h
    have hh : x.1.any (fun a => p (a,x.2))=false := Bool.eq_false_iff.mpr h
    simpa using (findIndex_eq_length _ _ hh).symm

end ParityWL.Complexity

end OAI
