import OAI.Combinatorics.ParityLifts.ParameterLoops

namespace OAI

namespace ParityWL.Complexity

lemma foldl_replicate_iterate {α β : Type} (f : α → α) (b : β) (n : ℕ) (x : α) :
    (List.replicate n b).foldl (fun a _ => f a) x=f^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,List.foldl_cons,ih,Function.iterate_succ_apply]

lemma TreeProgram.foldWork_replicate_bound {α : Type} [TreeCodec α] {f : α → α}
    (P : TreeProgram (Bool × α) α (fun x => f x.2)) (n : ℕ) (x : α) (S B : ℕ)
    (hs : ∀ i≤n, (treeEncode (f^[i] x)).size≤S)
    (hp : ∀ i<n, P.time (false,f^[i] x)≤B) :
    P.foldWork (List.replicate n false) x≤(n+1)*(10*(2*n+S+4)+B+1) := by
  induction n generalizing x with
  | zero =>
    have h := hs 0 (by omega)
    simp only [Function.iterate_zero, id_eq] at h
    simp only [List.replicate_zero,TreeProgram.foldWork,treeEncode_pair,treeEncode_nil,DataTree.size]
    omega
  | succ n ih =>
    have h0 := hs 0 (by omega)
    have hb := hp 0 (by omega)
    simp only [Function.iterate_zero,id_eq] at h0 hb
    have ht := ih (f x) (by
      intro i hi
      simpa only [Function.iterate_succ_apply] using hs (i+1) (by omega)) (by
      intro i hi
      simpa only [Function.iterate_succ_apply] using hp (i+1) (by omega))
    have hsz : (treeEncode (List.replicate (n+1) false,x)).size≤2*(n+1)+S+2 := by
      simp only [treeEncode_pair,treeEncode_list_size,List.map_replicate,List.sum_replicate,
        treeEncode_false,DataTree.size,smul_eq_mul]
      omega
    rw [List.replicate_succ,TreeProgram.foldWork]
    have hsz' : (treeEncode (false::List.replicate n false,x)).size≤2*(n+1)+S+2 := by
      simpa only [List.replicate_succ] using hsz
    nlinarith

def smallSizeConstant (M : Machine) : ℕ :=
  2*M.extraStates+(M.tapes+1)*(4*M.extraSymbols+16)+4

def boundedConfiguration (M : Machine) (n : ℕ) (bs : List Bool) : SmallConfiguration M :=
  (smallStep M)^[n] (smallInitial M bs)

def boundedAnswer (M : Machine) (n : ℕ) (bs : List Bool) : Bool × Bool :=
  (decide ((M.output (boundedConfiguration M n bs).1).isSome),
    (M.output (boundedConfiguration M n bs).1).getD false)

def TreeProgram.boundedConfiguration (M : Machine) :
    TreeProgram (ℕ × List Bool) (SmallConfiguration M)
      (fun x => Complexity.boundedConfiguration M x.1 x.2) := by
  let I := (((PolyProgram.fst ℕ (List Bool)).comp PolyProgram.ticks).pair
    ((PolyProgram.snd ℕ (List Bool)).comp (smallInitialProgram M)))
  let step : TreeProgram (Bool × SmallConfiguration M) (SmallConfiguration M) (fun x => smallStep M x.2) :=
    (PolyProgram.expr (TExpr.smallStep M TExpr.input.right) (by intro x; exact TExpr.smallStep_eval M _ _ _ rfl)).program
  exact (I.program.comp step.foldl).congr (by
    intro x
    simp only [Function.comp_def,foldl_replicate_iterate,Complexity.boundedConfiguration])

lemma boundedConfiguration_time_bound (M : Machine) : ∃ C d : ℕ, ∀ x : ℕ × List Bool,
    (TreeProgram.boundedConfiguration M).time x≤C*((treeEncode x).size+1)^d := by
  let I := (((PolyProgram.fst ℕ (List Bool)).comp PolyProgram.ticks).pair
    ((PolyProgram.snd ℕ (List Bool)).comp (smallInitialProgram M)))
  let e := TExpr.smallStep M TExpr.input.right
  let P : TreeProgram (Bool × SmallConfiguration M) (SmallConfiguration M) (fun x => smallStep M x.2) :=
    (PolyProgram.expr e (by intro x; exact TExpr.smallStep_eval M _ _ _ rfl)).program
  let K := smallSizeConstant M
  let A := 10*(K+6)+e.cost*(K+3)+K+10
  refine ⟨I.coefficient+A+1,I.degree+2,?_⟩
  rintro ⟨n,bs⟩
  let X := (treeEncode (n,bs)).size+1
  have hX : 1≤X := by dsimp [X]; omega
  have hn : n+1≤X := by dsimp [X]; simp only [numTree_size,DataTree.size]; omega
  have hl : bs.length+n+1≤X := by
    have hb := treeEncode_list_length bs
    dsimp [X]
    simp only [numTree_size,DataTree.size]
    omega
  let S := K*X
  let B := e.cost*(S+3)
  have hs (i : ℕ) (hi : i≤n) : (treeEncode ((smallStep M)^[i] (smallInitial M bs))).size≤S := by
    exact (smallRun_size M bs i).trans (Nat.mul_le_mul_left K (by omega))
  have hp (i : ℕ) (hi : i<n) : P.time (false,(smallStep M)^[i] (smallInitial M bs))≤B := by
    have h := hs i (by omega)
    change e.cost*((treeEncode (false,(smallStep M)^[i] (smallInitial M bs))).size+1)≤_
    simp only [treeEncode_pair,treeEncode_false,DataTree.size]
    exact Nat.mul_le_mul_left _ (by omega)
  have hw := TreeProgram.foldWork_replicate_bound P n (smallInitial M bs) S B hs hp
  have hout := hs n (by omega)
  have hfold : P.foldl.time (List.replicate n false,smallInitial M bs)≤A*X^2 := by
    change P.foldWork _ _+(treeEncode (([]:List Bool),_)).size+1≤_
    simp only [foldl_replicate_iterate,treeEncode_pair,treeEncode_nil,DataTree.size]
    have hmul := Nat.mul_le_mul hn (show 10*(2*n+S+4)+B+1≤(10*(K+6)+e.cost*(K+3)+1)*X by
      dsimp only [S,B]
      nlinarith [Nat.mul_le_mul_left e.cost (show K*X+3≤(K+3)*X by nlinarith)])
    dsimp only [A,S] at *
    nlinarith [Nat.mul_le_mul_left K (show X≤X^2 by nlinarith)]
  have ht := I.bound (n,bs)
  have ha := nat_poly_add X I.coefficient A I.degree 2 hX
  unfold TreeProgram.boundedConfiguration
  dsimp only
  erw [TreeProgram.congr_time]
  change I.program.time (n,bs)+P.foldl.time (List.replicate n false,smallInitial M bs)+1≤_
  exact (Nat.add_le_add_right (Nat.add_le_add ht hfold) 1).trans ha

noncomputable def PolyProgram.boundedConfiguration (M : Machine) :
    PolyProgram (ℕ × List Bool) (SmallConfiguration M)
      (fun x => Complexity.boundedConfiguration M x.1 x.2) := by
  choose C d h using boundedConfiguration_time_bound
  exact ⟨TreeProgram.boundedConfiguration M,C M,d M,h M⟩

def PolyProgram.smallAnswerPair (M : Machine) : PolyProgram (SmallConfiguration M) (Bool × Bool)
    (fun x => (decide (M.output x.1).isSome,(M.output x.1).getD false)) := by
  let e := TExpr.caseFin (M.extraStates+1) TExpr.input.left (fun q => .const (treeEncode
    (decide (M.output q).isSome,(M.output q).getD false))) .nil
  exact .expr e (by
    intro x
    apply TExpr.caseFin_eval x.1 TExpr.input.left _ .nil (treeEncode x)
    rfl)

noncomputable def PolyProgram.boundedAnswer (M : Machine) : PolyProgram (ℕ × List Bool) (Bool × Bool)
    (fun x => Complexity.boundedAnswer M x.1 x.2) :=
  (PolyProgram.boundedConfiguration M).comp (PolyProgram.smallAnswerPair M)

end ParityWL.Complexity

end OAI
