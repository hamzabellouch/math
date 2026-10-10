import OAI.Combinatorics.ParityLifts.ParameterPolynomial

namespace OAI

namespace ParityWL.Complexity

lemma TreeProgram.poly_comp_at {α β γ : Type} [TreeCodec α] [TreeCodec β] [TreeCodec γ]
    {f : α → β} {g : β → γ} (P : TreeProgram α β f) (Q : TreeProgram β γ g)
    (x : α) (A a B b : ℕ) (hp : P.time x≤A*((treeEncode x).size+1)^a)
    (hq : Q.time (f x)≤B*((treeEncode (f x)).size+1)^b) :
    (P.comp Q).time x≤(A+B*(A+1)^b+1)*((treeEncode x).size+1)^(a+a*b) := by
  let X := (treeEncode x).size+1
  have hx : 1≤X := by dsimp [X]; omega
  have hs := (P.run x).bounds.2.1
  have ht : Q.time (f x)≤B*(A+1)^b*X^(a*b) := by
    calc
      _ ≤ B*(A*X^a+1)^b := by apply hq.trans; gcongr; exact hs.trans hp
      _ ≤ _ := nat_poly_substitute X A B a b hx
  exact (Nat.add_le_add_right (Nat.add_le_add hp ht) 1).trans (nat_poly_add X _ _ _ _ hx)

def ParamPolyProgram.congr {ρ α β : Type} [TreeCodec ρ] [TreeCodec α] [TreeCodec β]
    {f g : ρ → α → β} (P : ParamPolyProgram ρ α β f) (h : ∀ r x, f r x=g r x) :
    ParamPolyProgram ρ α β g := by
  have : f=g := funext (fun r => funext (h r))
  subst g
  exact P

def ParamPolyProgram.reindex {ρ σ α β : Type} [TreeCodec ρ] [TreeCodec σ] [TreeCodec α] [TreeCodec β]
    {f : ρ → α → β} {g : σ → ρ} (P : ParamPolyProgram ρ α β f) (Q : PolyProgram σ ρ g) :
    ParamPolyProgram σ α β (fun s x => f (g s) x) := by
  let I := (((PolyProgram.fst σ α).comp Q).pair (PolyProgram.snd σ α))
  exact {
    program := I.program.comp P.program
    coefficient := fun s => I.coefficient+P.coefficient (g s)*(I.coefficient+1)^(P.degree (g s))+1
    degree := fun s => I.degree+I.degree*P.degree (g s)
    bound := fun s x => TreeProgram.poly_comp_at I.program P.program (s,x) _ _ _ _ (I.bound _) (P.bound (g s) x)
  }

def ParamPolyProgram.ite {ρ α β : Type} [TreeCodec ρ] [TreeCodec α] [TreeCodec β]
    {p : ρ → α → Bool} {f g : ρ → α → β}
    (P : ParamPolyProgram ρ α Bool p) (F : ParamPolyProgram ρ α β f) (G : ParamPolyProgram ρ α β g) :
    ParamPolyProgram ρ α β (fun r x => if p r x then f r x else g r x) where
  program := P.program.ite F.program G.program
  coefficient := fun r => P.coefficient r+(F.coefficient r+G.coefficient r+1)+1
  degree := fun r => P.degree r+(F.degree r+G.degree r)
  bound := by
    intro r x
    have hfg := nat_poly_add ((treeEncode (r,x)).size+1) (F.coefficient r) (G.coefficient r)
      (F.degree r) (G.degree r) (by omega)
    have h : (if p r x then F.program.time (r,x) else G.program.time (r,x)) ≤
        (F.coefficient r+G.coefficient r+1)*((treeEncode (r,x)).size+1)^(F.degree r+G.degree r) := by
      split
      · exact (F.bound r x).trans (by omega)
      · exact (G.bound r x).trans (by omega)
    exact (Nat.add_le_add_right (Nat.add_le_add (P.bound r x) h) 1).trans (nat_poly_add _ _ _ _ _ (by omega))

noncomputable def ParamPolyProgram.foldTimes {α : Type} [TreeCodec α]
    {f : Bool × α → α} (P : PolyProgram (Bool × α) α f) :
    ParamPolyProgram ℕ α α (fun n x => (List.replicate n false).foldl (fun a b => f (b,a)) x) := by
  let I := ((PolyProgram.fst ℕ α).comp PolyProgram.ticks).pair (PolyProgram.snd ℕ α)
  choose C d h using TreeProgram.fixed_fold_polynomial P
  have hf (n : ℕ) (x : α) : P.program.foldl.time (List.replicate n false,x) ≤
      (2*C n+1)*((treeEncode (List.replicate n false,x)).size+1)^(d n) := by
    have hh := h n (List.replicate n false) x (by simp)
    have hout := (P.program.foldLoop_run (List.replicate n false) x).bounds.2.1
    have h1 := Nat.one_le_pow (d n) ((treeEncode (List.replicate n false,x)).size+1) (by omega)
    change P.program.foldWork _ _+(treeEncode (([] : List Bool),_)).size+1≤_
    nlinarith only [hh,hout,h1]
  exact {
    program := I.program.comp P.program.foldl
    coefficient := fun n => I.coefficient+(2*C n+1)*(I.coefficient+1)^(d n)+1
    degree := fun n => I.degree+I.degree*d n
    bound := fun n x => TreeProgram.poly_comp_at I.program P.program.foldl (n,x) _ _ _ _ (I.bound _) (hf n x)
  }

noncomputable def ParamPolyProgram.allTuples (α : Type) [TreeCodec α] :
    ParamPolyProgram ℕ (List α) (List (List α)) (fun n xs => Complexity.allTuples n xs) := by
  let U := ((PolyProgram.prependAll α).mapWith).comp (PolyProgram.flatten (List α))
  let step := (PolyProgram.snd Bool (List α × List (List α))).comp
    ((PolyProgram.fst (List α) (List (List α))).pair U)
  let init : PolyProgram (ℕ × List α) (List α × List (List α)) (fun x => (x.2,[[]])) :=
    .expr (.pair TExpr.input.right (.pair .nil .nil)) (by intro x; rfl)
  let out : PolyProgram (ℕ × (List α × List (List α))) (List (List α)) (fun x => x.2.2) :=
    .expr TExpr.input.right.right (by intro x; rfl)
  let P := (ParamPolyProgram.ofPoly (f := fun (_ : ℕ) (xs : List α) => (xs,[[]])) init).comp (ParamPolyProgram.foldTimes step) |>.comp (ParamPolyProgram.ofPoly (f := fun (_ : ℕ) (x : List α × List (List α)) => x.2) out)
  refine P.congr ?_
  intro n xs
  change ((List.replicate n false).foldl
    (fun s (_ : Bool) => (s.1,(s.1.map (fun a => s.2.map (a::·))).flatten)) (xs,[[]])).2=Complexity.allTuples n xs
  have h : (List.replicate n false).foldl
      (fun s (_ : Bool) => (s.1,(s.1.map (fun a => s.2.map (a::·))).flatten)) (xs,[[]])=
        (xs,Complexity.allTuples n xs) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.replicate_succ',List.foldl_append,ih]
      simp only [List.foldl_cons,List.foldl_nil,Complexity.allTuples,List.flatMap_def]
  exact congrArg Prod.snd h

end ParityWL.Complexity

end OAI
