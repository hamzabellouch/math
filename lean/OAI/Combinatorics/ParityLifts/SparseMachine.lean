import OAI.Combinatorics.ParityLifts.SparseBounds

namespace OAI

namespace ParityWL.Complexity

abbrev DFSState (α : Type) := List (ClauseList α) × List (ClauseList α)

def dfsHead {α : Type} (s : DFSState α) : ClauseList α := s.1.headD []

def dfsMerge {α : Type} (x : SparseResult α × DFSState α) : DFSState α :=
  if x.1.1 then (x.2.1.tail,dfsHead x.2::x.2.2)
  else (x.1.2.1::x.1.2.2::x.2.1.tail,x.2.2)

noncomputable def dfsStep {α : Type} [DecidableEq α] (r : ℕ) (s : DFSState α) : DFSState α :=
  dfsMerge (sparseStep r (dfsHead s),s)

def dfsHeadExpr : TExpr := TExpr.input.left.left

def dfsMergeExpr : TExpr :=
  let res := TExpr.input.left
  let old := TExpr.input.right
  .cond res.left
    (.pair (.pair res.right.left (.pair res.right.right old.left.right)) old.right)
    (.pair old.left.right (.pair old.left.left old.right))

lemma dfsHeadExpr_eval {α : Type} [TreeCodec α] (s : DFSState α) :
    dfsHeadExpr.eval (treeEncode s)=treeEncode (dfsHead s) := by
  rcases s with ⟨xs,ys⟩
  cases xs <;> rfl

lemma dfsMergeExpr_eval {α : Type} [TreeCodec α] (x : SparseResult α × DFSState α) :
    dfsMergeExpr.eval (treeEncode x)=treeEncode (dfsMerge x) := by
  rcases x with ⟨⟨b,F,G⟩,⟨xs,ys⟩⟩
  cases xs <;> cases b <;> rfl

noncomputable def dfsProgram (α : Type) [TreeCodec α] [DecidableEq α] (r : ℕ) :
    TreeProgram (DFSState α) (DFSState α) (dfsStep r) where
  code := .seq (.pair (.seq dfsHeadExpr.compile (PolyProgram.sparseStep α r).program.code) .id)
    dfsMergeExpr.compile
  time := fun s => 1000*((treeEncode s).size+(PolyProgram.sparseStep α r).program.time (dfsHead s)+1)
  run := by
    intro s
    let P := (PolyProgram.sparseStep α r).program
    have hh : BEval dfsHeadExpr.compile (treeEncode s)
        (dfsHeadExpr.cost*((treeEncode s).size+1)) (treeEncode (dfsHead s)) := by
      simpa only [dfsHeadExpr_eval] using dfsHeadExpr.run (treeEncode s)
    have hc := hh.seq (P.run (dfsHead s))
    have hm := hc.pair (BEval.id (treeEncode s))
    have hf : BEval dfsMergeExpr.compile (treeEncode (sparseStep r (dfsHead s),s))
        (dfsMergeExpr.cost*((treeEncode (sparseStep r (dfsHead s),s)).size+1))
        (treeEncode (dfsStep r s)) := by
      simpa only [dfsMergeExpr_eval,dfsStep] using dfsMergeExpr.run (treeEncode (sparseStep r (dfsHead s),s))
    have hsize := (P.run (dfsHead s)).bounds.2.1
    apply (hm.seq hf).mono
    simp only [dfsHeadExpr,dfsMergeExpr,TExpr.cost,treeEncode_pair,DataTree.size]
    change (treeEncode (sparseStep r (dfsHead s))).size≤P.time (dfsHead s) at hsize
    dsimp only [P] at hsize ⊢
    omega

lemma SparseTree.All.root {α : Type} {P : ClauseList α → Prop} {T : SparseTree α} (h : T.All P) : P T.root := by
  cases T with
  | leaf F => exact h
  | branch F l t => exact h.1

lemma SparseTree.All.leaf {α : Type} {P : ClauseList α → Prop} {T : SparseTree α} (h : T.All P) :
    ∀ F∈T.leaves, P F := by
  induction T with
  | leaf F => simpa [SparseTree.leaves, SparseTree.All] using h
  | branch F l t hl ht =>
    intro G hG
    rcases List.mem_append.mp hG with hG | hG
    · exact hl h.2.1 G hG
    · exact ht h.2.2 G hG

lemma SparseTree.nodes_pos {α : Type} (T : SparseTree α) : 0<T.nodes := by
  cases T <;> simp [SparseTree.nodes]

lemma forest_roots_length {α : Type} (ts : List (SparseTree α)) : ts.length≤(ts.map SparseTree.nodes).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp only [List.length_cons,List.map_cons,List.sum_cons]; have := t.nodes_pos; omega

lemma dfsState_size {α : Type} [TreeCodec α] (ts : List (SparseTree α)) (acc : List (ClauseList α))
    (S A : ℕ) (ht : ∀ t∈ts, t.All (fun F => (treeEncode F).size≤S))
    (ha : ∀ F∈acc, (treeEncode F).size≤S) (hN : (ts.map SparseTree.nodes).sum+acc.length≤A) :
    (treeEncode (ts.map SparseTree.root,acc)).size≤3+A*(S+1) := by
  have hr : (treeEncode (ts.map SparseTree.root)).size≤1+ts.length*(S+1) := by
    rw [treeEncode_list_size]
    have hs := list_sum_map_le (ts.map SparseTree.root) (fun F => (treeEncode F).size+1) (S+1) (by
      intro F hF
      obtain ⟨t,ht',rfl⟩ := List.mem_map.mp hF
      have := (ht t ht').root
      omega)
    simpa only [List.length_map] using Nat.add_le_add_left hs 1
  have har : (treeEncode acc).size≤1+acc.length*(S+1) := by
    rw [treeEncode_list_size]
    apply Nat.add_le_add_left
    exact list_sum_map_le acc (fun F => (treeEncode F).size+1) (S+1) (by intro F hF; have := ha F hF; omega)
  have hn := forest_roots_length ts
  have hm := Nat.mul_le_mul_right (S+1) (show ts.length+acc.length≤A by omega)
  simp only [treeEncode_pair,DataTree.size]
  nlinarith

lemma dfsLoop_run {α : Type} [TreeCodec α] [DecidableEq α] (r S A B : ℕ)
    (hb : ∀ F : ClauseList α, (treeEncode F).size≤S → (PolyProgram.sparseStep α r).program.time F≤B)
    (ts : List (SparseTree α)) (acc : List (ClauseList α))
    (hv : ∀ t∈ts, t.Valid r) (ht : ∀ t∈ts, t.All (fun F => (treeEncode F).size≤S))
    (ha : ∀ F∈acc, (treeEncode F).size≤S) (hN : (ts.map SparseTree.nodes).sum+acc.length≤A) :
    BEval (.loop (dfsProgram α r).code) (treeEncode (ts.map SparseTree.root,acc))
      (((ts.map SparseTree.nodes).sum+1)*(1002*(4+A*(S+1)+B)))
      (treeEncode (([]:List (ClauseList α)),(ts.flatMap SparseTree.leaves).reverse++acc)) := by
  generalize he : (ts.map SparseTree.nodes).sum=n
  induction n using Nat.strong_induction_on generalizing ts acc with
  | h n ih =>
    have hsize := dfsState_size ts acc S A ht ha hN
    cases ts with
    | nil =>
      have hh := BEval.loop_stop (dfsProgram α r).code (treeEncode (([]:List (ClauseList α)),acc)) rfl
      have hz : n=0 := by simpa using he.symm
      subst n
      simp only [List.map_nil] at hsize
      simpa using hh.mono (by
        simp only [treeEncode_pair,treeEncode_nil] at hsize ⊢
        nlinarith)
    | cons t ts =>
      have hts : ∀ t∈ts, t.Valid r := fun t ht => hv t (by simp [ht])
      have hss : ∀ t∈ts, t.All (fun F => (treeEncode F).size≤S) := fun t hu => ht t (by simp [hu])
      have htv := hv t (by simp)
      have htt := ht t (by simp)
      have hh := (dfsProgram α r).run ((t::ts).map SparseTree.root,acc)
      have htime := hb t.root htt.root
      have hhead : dfsHead ((t::ts).map SparseTree.root,acc)=t.root := rfl
      change BEval _ _ (1000*((treeEncode ((t::ts).map SparseTree.root,acc)).size+
        (PolyProgram.sparseStep α r).program.time (dfsHead ((t::ts).map SparseTree.root,acc))+1)) _ at hh
      rw [hhead] at hh
      have hbnd : 1000*((treeEncode ((t::ts).map SparseTree.root,acc)).size+
          (PolyProgram.sparseStep α r).program.time t.root+1)≤1000*(4+A*(S+1)+B) := by omega
      have hnil : (treeEncode ((t::ts).map SparseTree.root,acc)).child false≠.nil := by simp [DataTree.child]
      cases t with
      | leaf F =>
        change (sparseStep r F).1=true at htv
        have hout : dfsStep r ((SparseTree.leaf F::ts).map SparseTree.root,acc)=(ts.map SparseTree.root,F::acc) := by
          simp only [dfsStep,dfsHead,List.map_cons,List.headD_cons,dfsMerge,htv,
            SparseTree.root,↓reduceIte,List.tail_cons]
        have hn : (ts.map SparseTree.nodes).sum<n := by simp only [List.map_cons,List.sum_cons,SparseTree.nodes] at he; omega
        have hn' : (ts.map SparseTree.nodes).sum+(F::acc).length≤A := by
          simpa only [List.map_cons,List.sum_cons,SparseTree.nodes,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hN
        have har : ∀ C∈F::acc, (treeEncode C).size≤S := by
          intro C hC; rcases List.mem_cons.mp hC with rfl | hC
          · exact htt
          · exact ha C hC
        obtain hrec := ih _ hn ts (F::acc) hts hss har hn' rfl
        rw [hout] at hh
        have hrun := BEval.loop_next hnil (hh.mono hbnd) hrec
        convert hrun.mono (show _≤(n+1)*(1002*(4+A*(S+1)+B)) from by
          simp only [List.map_cons,List.sum_cons,SparseTree.nodes] at he
          generalize 4+A*(S+1)+B=D at *
          nlinarith) using 1; simp [SparseTree.leaves,List.reverse_cons,List.append_assoc]
      | branch F l t =>
        obtain ⟨hf,hl,hr,hlv,htv⟩ := htv
        have hout : dfsStep r ((SparseTree.branch F l t::ts).map SparseTree.root,acc)=((l::t::ts).map SparseTree.root,acc) := by
          simp only [dfsStep,dfsHead,List.map_cons,List.headD_cons,dfsMerge,SparseTree.root,hf,hl,hr,
            Bool.false_eq_true,↓reduceIte,List.tail_cons]
        have hn : ((l::t::ts).map SparseTree.nodes).sum<n := by
          simp only [List.map_cons,List.sum_cons,SparseTree.nodes] at he ⊢; omega
        have hn' : ((l::t::ts).map SparseTree.nodes).sum+acc.length≤A := by
          simp only [List.map_cons,List.sum_cons,SparseTree.nodes] at hN ⊢; omega
        have hv' : ∀ u∈l::t::ts, u.Valid r := by
          intro u hu; rcases List.mem_cons.mp hu with rfl | hu
          · exact hlv
          · rcases List.mem_cons.mp hu with rfl | hu
            · exact htv
            · exact hts u hu
        have ht' : ∀ u∈l::t::ts, u.All (fun F => (treeEncode F).size≤S) := by
          intro u hu; rcases List.mem_cons.mp hu with rfl | hu
          · exact htt.2.1
          · rcases List.mem_cons.mp hu with rfl | hu
            · exact htt.2.2
            · exact hss u hu
        obtain hrec := ih _ hn (l::t::ts) acc hv' ht' ha hn' rfl
        rw [hout] at hh
        have hrun := BEval.loop_next hnil (hh.mono hbnd) hrec
        convert hrun.mono (show _≤(n+1)*(1002*(4+A*(S+1)+B)) from by
          simp only [List.map_cons,List.sum_cons,SparseTree.nodes] at he ⊢
          generalize 4+A*(S+1)+B=D at *
          nlinarith) using 1; simp [SparseTree.leaves,List.append_assoc]

lemma SparseTree.All.mono {α : Type} {P Q : ClauseList α → Prop} {T : SparseTree α}
    (h : T.All P) (hp : ∀ F, P F → Q F) : T.All Q := by
  induction T with
  | leaf F => exact hp F h
  | branch F l t hl ht => exact ⟨hp F h.1,hl h.2.1,ht h.2.2⟩

def dfsInitExpr : TExpr := .pair (.pair .input .nil) .nil

noncomputable def sparseCode (α : Type) [TreeCodec α] [DecidableEq α] (r : ℕ) : FCode :=
  .seq dfsInitExpr.compile (.seq (.loop (dfsProgram α r).code) .right)

lemma sparseCode_run {α : Type} [TreeCodec α] [DecidableEq α] (r S B : ℕ)
    (hb : ∀ F : ClauseList α, (treeEncode F).size≤S → (PolyProgram.sparseStep α r).program.time F≤B)
    (T : SparseTree α) (hv : T.Valid r) (ht : T.All (fun F => (treeEncode F).size≤S)) :
    BEval (sparseCode α r) (treeEncode T.root)
      (2010*(T.nodes+1)^2*(S+B+5)) (treeEncode T.leaves.reverse) := by
  have hinit : BEval dfsInitExpr.compile (treeEncode T.root)
      (dfsInitExpr.cost*((treeEncode T.root).size+1))
      (treeEncode ([T.root],([]:List (ClauseList α)))) := dfsInitExpr.run _
  have hloop := dfsLoop_run r S T.nodes B hb [T] []
    (by intro t ht; simpa using (List.mem_singleton.mp ht) ▸ hv)
    (by intro t ht'; simpa using (List.mem_singleton.mp ht') ▸ ht)
    (by simp) (by simp)
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,
    List.flatMap_cons,List.flatMap_nil,List.append_nil] at hloop
  have hr := BEval.right (treeEncode (([]:List (ClauseList α)),T.leaves.reverse))
  change BEval _ _ _ (treeEncode T.leaves.reverse) at hr
  have hs := hloop.bounds.2.1
  have hroot := ht.root
  apply (hinit.seq (hloop.seq hr)).mono
  simp only [dfsInitExpr,TExpr.cost,DataTree.size] at *
  have hn := T.nodes_pos
  generalize T.nodes=n at *
  generalize (treeEncode T.root).size=sz at *
  generalize (treeEncode (([]:List (ClauseList α)),T.leaves.reverse)).size=z at *
  let X := (n+1)^2*(S+B+5)
  have hc : (n+1)*(1002*(4+n*(S+1)+B))≤1002*X := by
    calc
      _ ≤ (n+1)*(1002*((n+1)*(S+B+5))) := by gcongr; nlinarith
      _ = _ := by dsimp [X]; ring
  have hX : S+B+5≤X := Nat.le_mul_of_pos_left _ (by positivity)
  calc
    _ ≤ 2010*X := by omega
    _ = _ := by dsimp [X]; ring

end ParityWL.Complexity

end OAI
