import OAI.Combinatorics.ParityLifts.UniformFlower

namespace OAI

namespace ParityWL.Complexity

abbrev RuntimeDFSState (α : Type) := List (ClauseList α) × List (ClauseList α) × ℕ

def runtimeDfsHead {α : Type} (s : RuntimeDFSState α) : ClauseList α := s.1.headD []

def runtimeDfsMerge {α : Type} (x : SparseResult α × RuntimeDFSState α) : RuntimeDFSState α :=
  if x.1.1 then (x.2.1.tail,dfsHead (x.2.1,x.2.2.1)::x.2.2.1,x.2.2.2)
  else (x.1.2.1::x.1.2.2::x.2.1.tail,x.2.2)

noncomputable def runtimeDfsStep {α : Type} [DecidableEq α] (s : RuntimeDFSState α) : RuntimeDFSState α :=
  runtimeDfsMerge (sparseStep s.2.2 (runtimeDfsHead s),s)

def runtimeDfsHeadExpr : TExpr := .pair TExpr.input.right.right TExpr.input.left.left

def runtimeDfsMergeExpr : TExpr :=
  let res := TExpr.input.left
  let old := TExpr.input.right
  .cond res.left
    (.pair (.pair res.right.left (.pair res.right.right old.left.right)) old.right)
    (.pair old.left.right (.pair (.pair old.left.left old.right.left) old.right.right))

lemma runtimeDfsHeadExpr_eval {α : Type} [TreeCodec α] (s : RuntimeDFSState α) :
    runtimeDfsHeadExpr.eval (treeEncode s)=treeEncode (s.2.2,runtimeDfsHead s) := by
  rcases s with ⟨xs,ys,r⟩
  cases xs <;> rfl

lemma runtimeDfsMergeExpr_eval {α : Type} [TreeCodec α] (x : SparseResult α × RuntimeDFSState α) :
    runtimeDfsMergeExpr.eval (treeEncode x)=treeEncode (runtimeDfsMerge x) := by
  rcases x with ⟨⟨b,F,G⟩,⟨xs,ys,r⟩⟩
  cases xs <;> cases b <;> rfl

noncomputable def runtimeDfsProgram (α : Type) [TreeCodec α] [DecidableEq α] :
    TreeProgram (RuntimeDFSState α) (RuntimeDFSState α) runtimeDfsStep where
  code := .seq (.pair (.seq runtimeDfsHeadExpr.compile (ParamPolyProgram.sparseStep α).program.code) .id)
    runtimeDfsMergeExpr.compile
  time := fun s => 1000*((treeEncode s).size+(ParamPolyProgram.sparseStep α).program.time (s.2.2,runtimeDfsHead s)+1)
  run := by
    intro s
    let P := (ParamPolyProgram.sparseStep α).program
    have hh : BEval runtimeDfsHeadExpr.compile (treeEncode s)
        (runtimeDfsHeadExpr.cost*((treeEncode s).size+1)) (treeEncode (s.2.2,runtimeDfsHead s)) := by
      simpa only [runtimeDfsHeadExpr_eval] using runtimeDfsHeadExpr.run (treeEncode s)
    have hc := hh.seq (P.run (s.2.2,runtimeDfsHead s))
    have hm := hc.pair (BEval.id (treeEncode s))
    have hf : BEval runtimeDfsMergeExpr.compile (treeEncode (sparseStep s.2.2 (runtimeDfsHead s),s))
        (runtimeDfsMergeExpr.cost*((treeEncode (sparseStep s.2.2 (runtimeDfsHead s),s)).size+1))
        (treeEncode (runtimeDfsStep s)) := by
      simpa only [runtimeDfsMergeExpr_eval,runtimeDfsStep] using runtimeDfsMergeExpr.run (treeEncode (sparseStep s.2.2 (runtimeDfsHead s),s))
    have hsize := (P.run (s.2.2,runtimeDfsHead s)).bounds.2.1
    apply (hm.seq hf).mono
    simp only [runtimeDfsHeadExpr,runtimeDfsMergeExpr,TExpr.cost,treeEncode_pair,DataTree.size]
    change (treeEncode (sparseStep s.2.2 (runtimeDfsHead s))).size≤P.time (s.2.2,runtimeDfsHead s) at hsize
    dsimp only [P] at hsize ⊢
    omega

lemma runtimeDfsState_size {α : Type} [TreeCodec α] (ts : List (SparseTree α)) (acc : List (ClauseList α))
    (r S A : ℕ) (ht : ∀ t∈ts, t.All (fun F => (treeEncode F).size≤S))
    (ha : ∀ F∈acc, (treeEncode F).size≤S) (hN : (ts.map SparseTree.nodes).sum+acc.length≤A) :
    (treeEncode (ts.map SparseTree.root,acc,r)).size≤4+A*(S+1)+(treeEncode r).size := by
  have h := dfsState_size ts acc S A ht ha hN
  simp only [treeEncode_pair,DataTree.size] at *
  omega

lemma runtimeDfsLoop_run {α : Type} [TreeCodec α] [DecidableEq α] (r S A B : ℕ)
    (hb : ∀ F : ClauseList α, (treeEncode F).size≤S → (ParamPolyProgram.sparseStep α).program.time (r,F)≤B)
    (ts : List (SparseTree α)) (acc : List (ClauseList α))
    (hv : ∀ t∈ts, t.Valid r) (ht : ∀ t∈ts, t.All (fun F => (treeEncode F).size≤S))
    (ha : ∀ F∈acc, (treeEncode F).size≤S) (hN : (ts.map SparseTree.nodes).sum+acc.length≤A) :
    BEval (.loop (runtimeDfsProgram α).code) (treeEncode (ts.map SparseTree.root,acc,r))
      (((ts.map SparseTree.nodes).sum+1)*(1002*(5+A*(S+1)+(treeEncode r).size+B)))
      (treeEncode (([]:List (ClauseList α)),(ts.flatMap SparseTree.leaves).reverse++acc,r)) := by
  generalize he : (ts.map SparseTree.nodes).sum=n
  induction n using Nat.strong_induction_on generalizing ts acc with
  | h n ih =>
    have hsize := runtimeDfsState_size ts acc r S A ht ha hN
    cases ts with
    | nil =>
      have hh := BEval.loop_stop (runtimeDfsProgram α).code (treeEncode (([]:List (ClauseList α)),acc,r)) rfl
      have hz : n=0 := by simpa using he.symm
      subst n
      simp only [List.map_nil] at hsize
      simpa using hh.mono (by
        simp only [treeEncode_pair,treeEncode_nil,treeEncode_nat,numTree_size] at hsize ⊢
        nlinarith)
    | cons t ts =>
      have hts : ∀ t∈ts, t.Valid r := fun t ht => hv t (by simp [ht])
      have hss : ∀ t∈ts, t.All (fun F => (treeEncode F).size≤S) := fun t hu => ht t (by simp [hu])
      have htv := hv t (by simp)
      have htt := ht t (by simp)
      have hh := (runtimeDfsProgram α).run ((t::ts).map SparseTree.root,acc,r)
      have htime := hb t.root htt.root
      have hhead : runtimeDfsHead ((t::ts).map SparseTree.root,acc,r)=t.root := rfl
      change BEval _ _ (1000*((treeEncode ((t::ts).map SparseTree.root,acc,r)).size+
        (ParamPolyProgram.sparseStep α).program.time (r,runtimeDfsHead ((t::ts).map SparseTree.root,acc,r))+1)) _ at hh
      rw [hhead] at hh
      have hbnd : 1000*((treeEncode ((t::ts).map SparseTree.root,acc,r)).size+
          (ParamPolyProgram.sparseStep α).program.time (r,t.root)+1)≤1000*(5+A*(S+1)+(treeEncode r).size+B) := by omega
      have hnil : (treeEncode ((t::ts).map SparseTree.root,acc,r)).child false≠.nil := by simp [DataTree.child]
      cases t with
      | leaf F =>
        change (sparseStep r F).1=true at htv
        have hout : runtimeDfsStep ((SparseTree.leaf F::ts).map SparseTree.root,acc,r)=(ts.map SparseTree.root,F::acc,r) := by
          simp only [runtimeDfsStep,runtimeDfsHead,dfsHead,List.map_cons,List.headD_cons,runtimeDfsMerge,htv,
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
        convert hrun.mono (show _≤(n+1)*(1002*(5+A*(S+1)+(treeEncode r).size+B)) from by
          simp only [List.map_cons,List.sum_cons,SparseTree.nodes] at he
          generalize 5+A*(S+1)+(treeEncode r).size+B=D at *
          nlinarith) using 1; simp [SparseTree.leaves,List.reverse_cons,List.append_assoc]
      | branch F l t =>
        obtain ⟨hf,hl,hr,hlv,htv⟩ := htv
        have hout : runtimeDfsStep ((SparseTree.branch F l t::ts).map SparseTree.root,acc,r)=((l::t::ts).map SparseTree.root,acc,r) := by
          simp only [runtimeDfsStep,runtimeDfsHead,List.map_cons,List.headD_cons,runtimeDfsMerge,SparseTree.root,hf,hl,hr,
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
        convert hrun.mono (show _≤(n+1)*(1002*(5+A*(S+1)+(treeEncode r).size+B)) from by
          simp only [List.map_cons,List.sum_cons,SparseTree.nodes] at he ⊢
          generalize 5+A*(S+1)+(treeEncode r).size+B=D at *
          nlinarith) using 1; simp [SparseTree.leaves,List.append_assoc]


def runtimeDfsInitExpr : TExpr :=
  .pair (.pair TExpr.input.right .nil) (.pair .nil TExpr.input.left)

noncomputable def runtimeSparseCode (α : Type) [TreeCodec α] [DecidableEq α] : FCode :=
  .seq runtimeDfsInitExpr.compile (.seq (.loop (runtimeDfsProgram α).code) (.seq .right .left))

lemma runtimeSparseCode_run {α : Type} [TreeCodec α] [DecidableEq α] (r S B : ℕ)
    (hb : ∀ F : ClauseList α, (treeEncode F).size≤S → (ParamPolyProgram.sparseStep α).program.time (r,F)≤B)
    (T : SparseTree α) (hv : T.Valid r) (ht : T.All (fun F => (treeEncode F).size≤S)) :
    BEval (runtimeSparseCode α) (treeEncode (r,T.root))
      (4000*(T.nodes+1)^2*(S+B+(treeEncode r).size+6)) (treeEncode T.leaves.reverse) := by
  have hinit : BEval runtimeDfsInitExpr.compile (treeEncode (r,T.root))
      (runtimeDfsInitExpr.cost*((treeEncode (r,T.root)).size+1))
      (treeEncode ([T.root],([]:List (ClauseList α)),r)) := runtimeDfsInitExpr.run _
  have hloop := runtimeDfsLoop_run r S T.nodes B hb [T] []
    (by intro t ht; simpa using (List.mem_singleton.mp ht) ▸ hv)
    (by intro t ht'; simpa using (List.mem_singleton.mp ht') ▸ ht)
    (by simp) (by simp)
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,
    List.flatMap_cons,List.flatMap_nil,List.append_nil] at hloop
  have hr := (BEval.right (treeEncode (([]:List (ClauseList α)),T.leaves.reverse,r))).seq
    (BEval.left (treeEncode (T.leaves.reverse,r)))
  change BEval _ _ _ (treeEncode T.leaves.reverse) at hr
  have hs := hloop.bounds.2.1
  have hroot := ht.root
  apply (hinit.seq (hloop.seq hr)).mono
  simp only [runtimeDfsInitExpr,TExpr.cost,treeEncode_pair,DataTree.size] at *
  have hn := T.nodes_pos
  generalize T.nodes=n at *
  generalize (treeEncode T.root).size=sz at *
  generalize (treeEncode T.leaves.reverse).size=z at *
  generalize (treeEncode r).size=R at *
  let X := (n+1)^2*(S+B+R+6)
  have hc : (n+1)*(1002*(5+n*(S+1)+R+B))≤1002*X := by
    calc
      _ ≤ (n+1)*(1002*((n+1)*(S+B+R+6))) := by gcongr; nlinarith
      _ = _ := by dsimp [X]; ring
  have hX : S+B+R+6≤X := Nat.le_mul_of_pos_left _ (by positivity)
  calc
    _ ≤ 4000*X := by omega
    _ = _ := by dsimp [X]; ring

end ParityWL.Complexity

end OAI
