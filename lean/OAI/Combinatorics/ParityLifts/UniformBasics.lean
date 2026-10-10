import OAI.Combinatorics.ParityLifts.FixedETH

namespace OAI

namespace ParityWL.Complexity

def TreeProgram.mapWith {α β γ : Type} [TreeCodec α] [TreeCodec β] [TreeCodec γ]
    {f : α × γ → β} (P : TreeProgram (α × γ) β f) :
    TreeProgram (List α × γ) (List β) (fun x => x.1.map (fun a => f (a,x.2))) := by
  let a := TreeProgram.fst α (List β × γ)
  let bs := (TreeProgram.snd α (List β × γ)).comp (TreeProgram.fst (List β) γ)
  let c := (TreeProgram.snd α (List β × γ)).comp (TreeProgram.snd (List β) γ)
  let step := ((((a.pair c).comp P).pair bs).comp (PolyProgram.cons β).program).pair c
  let init := (TreeProgram.fst (List α) γ).pair
    ((TreeProgram.const ([] : List β)).pair (TreeProgram.snd (List α) γ))
  refine (init.comp step.foldl |>.comp (TreeProgram.fst (List β) γ) |>.comp
    (PolyProgram.reverse β).program).congr ?_
  intro x
  change (x.1.foldl (fun s a => (f (a,s.2)::s.1,s.2)) ([],x.2)).1.reverse=_
  simp [list_fold_map_context]

def TreeProgram.map {α β : Type} [TreeCodec α] [TreeCodec β] {f : α → β}
    (P : TreeProgram α β f) : TreeProgram (List α) (List β) (List.map f) := by
  let Q := (TreeProgram.fst α Bool).comp P
  exact (((TreeProgram.id (List α)).pair (TreeProgram.const false)).comp Q.mapWith).congr (by intro x; rfl)

def TreeProgram.sublists (α : Type) [TreeCodec α] :
    TreeProgram (List α) (List (List α)) List.sublists := by
  let Q : PolyProgram (List α × α) (List (List α)) (fun x => [x.1,x.2::x.1]) :=
    .expr (.pair TExpr.input.left (.pair (.pair TExpr.input.right TExpr.input.left) .nil)) (by intro x; rfl)
  let sw : PolyProgram (α × List (List α)) (List (List α) × α) (fun x => (x.2,x.1)) :=
    .expr (.pair TExpr.input.right TExpr.input.left) (by intro x; rfl)
  let step := (sw.comp Q.mapWith |>.comp (PolyProgram.flatten (List α))).program
  let init := (PolyProgram.reverse α).program.pair (TreeProgram.const ([[]] : List (List α)))
  refine (init.comp step.foldl).congr ?_
  intro xs
  change xs.reverse.foldl (fun s a => (s.map (fun l => [l,a::l])).flatten) [[]]=xs.sublists
  rw [List.foldl_reverse]
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.foldr_cons,List.sublists_cons,ih]
    rfl

def PolyProgram.product (α β : Type) [TreeCodec α] [TreeCodec β] :
    PolyProgram (List α × List β) (List (α × β)) (fun x => x.1.product x.2) := by
  let sw : PolyProgram (β × α) (α × β) (fun x => (x.2,x.1)) :=
    .expr (.pair TExpr.input.right TExpr.input.left) (by intro x; rfl)
  let input : PolyProgram (α × List β) (List β × α) (fun x => (x.2,x.1)) :=
    .expr (.pair TExpr.input.right TExpr.input.left) (by intro x; rfl)
  exact ((input.comp sw.mapWith).mapWith.comp (PolyProgram.flatten (α × β))).congr (by intro x; rfl)

def PolyProgram.natLt : PolyProgram (ℕ × ℕ) Bool (fun x => decide (x.1<x.2)) :=
  ((((PolyProgram.fst ℕ ℕ).comp PolyProgram.natSucc).pair (PolyProgram.snd ℕ ℕ)).comp PolyProgram.natLe).congr
    (by intro x; rfl)

def PolyProgram.natModTwo : PolyProgram ℕ ℕ (fun n => n%2) := by
  let Q := (((PolyProgram.natDivPos 2 (by omega)).pair (PolyProgram.const 2)).comp PolyProgram.natMul)
  exact (((PolyProgram.id ℕ).pair Q).comp PolyProgram.natSub).congr (by intro n; change n-(n/2)*2=n%2; omega)

def PolyProgram.natDiv : PolyProgram (ℕ × ℕ) ℕ (fun x => x.1/x.2) := by
  let P := (PolyProgram.snd Bool ((ℕ × ℕ) × ℕ)).comp PolyProgram.divStep
  have hg (u : Bool) (s : (ℕ × ℕ) × ℕ) :
      (treeEncode (Complexity.divStep s)).size ≤ (treeEncode s).size+2*((treeEncode u).size+1)^0 := by
    simp only [Complexity.divStep]
    split <;> simp [DataTree.size]
    all_goals omega
  let F := P.foldlGrowing 2 0 hg
  let init : PolyProgram (ℕ × ℕ) ((ℕ × ℕ) × ℕ) (fun x => ((0,0),x.2)) :=
    .expr (.pair (.pair .nil .nil) TExpr.input.right) (by intro x; rfl)
  let I := ((PolyProgram.fst ℕ ℕ).comp PolyProgram.ticks).pair init
  let R := (I.comp F).comp ((PolyProgram.fst (ℕ × ℕ) ℕ).comp (PolyProgram.snd ℕ ℕ))
  let Z := (PolyProgram.snd ℕ ℕ).comp PolyProgram.natZero
  refine (Z.ite (PolyProgram.const 0) R).congr ?_
  intro ⟨n,t⟩
  by_cases ht : t=0
  · simp [ht]
  · simp only [Function.comp_apply,decide_eq_true_eq,ht,↓reduceIte]
    have he := fold_divStep (List.replicate n false) 0 t (by omega)
    simpa [R,I,init,Function.comp_def] using congrArg (fun s => s.1.2) he

end ParityWL.Complexity

end OAI
