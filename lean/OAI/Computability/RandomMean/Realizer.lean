import OAI.Computability.RandomMean.RandomTables

namespace OAI

section
namespace MeanPayoff.Realizer
open RegisterBits BinaryData TreeDevice TreeDevice.Certified
noncomputable def preTail : Program 5 := Sequence5.program (moveCode 1 0) Preparation.device.program
noncomputable def pre : Program 5 := Sequence5.program Box5.program preTail
noncomputable def preCost (d : Digits) : ℕ :=
  (2*d.bits.length+2+feedCost d.bits+1)+(6*treeSize (encode d)+3+Preparation.device.limit d+2)+2
 theorem pre_quiet : CoinFree pre :=
  Sequence5.quiet _ _ Box5.quiet (Sequence5.quiet _ _ (by intro q top b; rfl) Preparation.device.quiet)
 theorem pre_runs (d : Digits) (bits : ℕ→Bool) :
    advance pre bits ⟨some pre.start,core d.bits [] [],[]⟩ (preCost d)=
      ⟨none,store (encode (Preparation.value d)) [],[]⟩ := by
  have hd : (encode d : Data)=listData d.bits := Halve.listTree_boolData _
  apply Sequence5.runs Box5.program preTail (core d.bits [] []) (core [] (BinaryData.encode (encode d)) [])
    (store (encode (Preparation.value d)) []) [] [] _ _ ?_ ?_ bits
  · intro cs; rw [hd]; exact Box5.runs d.bits [] cs
  · intro cs
    apply Sequence5.runs (moveCode 1 0) Preparation.device.program _ (store (encode d) []) _ [] [] _ _ ?_ ?_ cs
    · intro ds
      convert move10 (encode d) [] [] [] [] ds using 1 <;> simp only [store,core,List.append_nil]
    · exact Preparation.device.correct d [] []
noncomputable def post : Program 5 := Sequence5.program PostCode.run.device.program Emit.program
noncomputable def postCost (z : PostCode.Input) : ℕ := PostCode.run.device.limit z+Emit.cost (PostCode.run z).bits+2
 theorem post_quiet : CoinFree post := Sequence5.quiet _ _ PostCode.run.device.quiet Emit.quiet
 theorem post_runs (z : PostCode.Input) (bits : ℕ→Bool) :
    advance post bits ⟨some post.start,store (encode z) [],[]⟩ (postCost z)=
      ⟨none,core [] [] [],(PostCode.run z).bits⟩ := by
  apply Sequence5.runs PostCode.run.device.program Emit.program _ (store (encode (PostCode.run z)) []) _ [] _ _ _
    (PostCode.run.device.correct z [] []) ?_ bits
  intro cs
  have hd : (encode (PostCode.run z) : Data)=listData (PostCode.run z).bits := Halve.listTree_boolData _
  convert Emit.runs (PostCode.run z).bits [] [] cs using 1 <;> simp only [List.nil_append,hd] ; rfl
 theorem digits_length (d : Digits) : d.bits.length≤treeSize (encode d) := by
  have h := list_length_le_size boolData d.bits
  change d.bits.length≤treeSize (listTree boolData d.bits)
  omega
 theorem post_polynomial : ∃ K e, ∀ z, postCost z≤K*(treeSize (encode z)+1)^e := by
  have hi := PolyBound.base (fun z : PostCode.Input => treeSize (encode z))
  have hc := polynomial_limit PostCode.run.polynomial _ (fun z : PostCode.Input => z) hi
  have ho := polynomial_output PostCode.run.device _ (fun z : PostCode.Input => z) hi hc
  have he := ((PolyBound.const _ 4).mul ho).add (PolyBound.const _ 2)
  have hb : PolyBound (fun z : PostCode.Input => treeSize (encode z)) (fun z => Emit.cost (PostCode.run z).bits) :=
    he.mono (fun z => (Emit.bound _).trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 (digits_length _)) 2))
  exact (hc.add hb).add (PolyBound.const _ 2)
end MeanPayoff.Realizer

end

section
namespace MeanPayoff.TreeDevice.Certified.RawControl
open SourceControl RandomTree
 theorem halted_value {G : Game} {B : ℕ} {R : Result G B}
    (s : SourceControl.State G B R) (z : State) (h : StateRep s z) (hh : s.halted)
    (F : Pack→ℚ) (f : R.Value→ℚ) (hf : ∀ v p, ValueRep R v p → F p=f v) :
    F z.1.2=s.denote.erase.expect f := by
  cases s with
  | call j k => exact hh.elim
  | ret k v =>
    cases k with
    | push frame k => exact hh.elim
    | done =>
      cases h with
      | ret tag value stack =>
        change F _=f v
        exact hf v _ value
 theorem loop_expect {G : Game} {B : ℕ} {R : Result G B}
    (n : ℕ) (s : SourceControl.State G B R) (z : State) (h : StateRep s z)
    (e : Env) (he : EnvRep G B e) (hn : s.rank≤n)
    (F : Pack→ℚ) (f : R.Value→ℚ) (hf : ∀ v p, ValueRep R v p → F p=f v) :
    (drawSamples (sampleExponent B) n).expect (fun cs => F (loop ((e,z),cs)).2.1.2)=
      s.denote.erase.expect f := by
  have hh := (samples_fold_all n s (fun s => s.halted)).mpr
    ((sampledRun_all n s _).mpr (run_halts n s hn))
  calc
    _ = (drawSamples (sampleExponent B) n).expect
        (fun cs => (cs.foldl (fun s c => sampledStep c.length s) s).denote.erase.expect f) := by
      apply expect_congr_all
      exact all_mono _ hh (fun cs hc => halted_value _ _ (loop_rep s z h e he cs) hc F f hf)
    _ = (SourceControl.sampledRun n s).expect (fun s => s.denote.erase.expect f) := samples_fold_expect n s (fun s => s.denote.erase.expect f)
    _ = (SourceControl.run n s).tree.expect (fun p => p.1.denote.erase.expect f) := sampledRun_expect n s _
    _ = ((SourceControl.run n s).bind SourceControl.State.denote).erase.expect f := by
      simp only [Counted.erase,Counted.bind,expect_map,expect_bind,Function.comp_def]
    _ = s.denote.erase.expect f := by rw [run_denote]
end MeanPayoff.TreeDevice.Certified.RawControl
namespace MeanPayoff.SourceControl
 theorem root_rank (G : Game) :
    (State.call (Job.solve (rootBudgets G) (rootBox G)) .done).rank≤rootControlBound G := by
  simp only [State.rank, State.credit, Job.credit, Kont.credit, Nat.zero_add,
    State.denote, Job.denote, Kont.denote, Counted.bind_pure]
  exact Nat.mul_le_mul_left _ ((Counted.maximum_le_iff _ _).mpr
    (CountedAlgorithm.bounded_solve G _ _))
end MeanPayoff.SourceControl
namespace MeanPayoff.Realizer
open TreeDevice TreeDevice.Certified BinaryData RandomTree
 theorem classify_rep (G : Game) (w : W) (hw : w.val=topWidth G)
    (v : BoxVector (rootBox G)) (p : RawControl.Pack) (hp : RawControl.ValueRep (.vector (rootBox G)) v p) :
    PostCode.classify (w,p.q)=List.ofFn (fun i => decide (topWidth G/2<v.val i)) := by
  obtain ⟨ws,hws,hval⟩ := hp
  rw [PostCode.classify_eval,hws,List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_def,hw,hval]
 theorem root_loop_law (G : Game) (N : ℕ) (hN : SourceControl.rootControlBound G≤N)
    (f : List Bool→ℚ) :
    (RawControl.drawSamples (sampleExponent (topWidth G).toNat) N).expect
      (fun cs => f (PostCode.classify (InputCode.width (InputCode.game G),
        (RawControl.loop ((RootCode.env (InputCode.game G),RootCode.state (InputCode.game G)),cs)).2.1.2.q))) =
    (gameSolve G).expect (fun out => f (List.ofFn out)) := by
  have h := RawControl.loop_expect N _ _ (RootCode.state_rep G) _ (RootCode.env_rep G)
    ((SourceControl.root_rank G).trans hN)
    (fun p => f (PostCode.classify (InputCode.width (InputCode.game G),p.q)))
    (fun v => f (List.ofFn (fun i => decide (topWidth G/2<v.val i))))
    (fun v p hp => congrArg f (classify_rep G _ (InputCode.width_val G) v p hp))
  convert h using 1
  simp only [SourceControl.State.denote,SourceControl.Job.denote,SourceControl.Kont.denote,
    Counted.bind_pure,CountedAlgorithm.erase_solve,gameSolve,expect_map,Function.comp_def]
end MeanPayoff.Realizer

end

section
namespace MeanPayoff.Realizer
open RegisterBits BinaryData TreeDevice TreeDevice.Certified
noncomputable def program : Program 5 := RandomTable.program pre post
noncomputable def aux (d : Digits) : Preparation.Aux := (Preparation.value d).2
noncomputable def amount (d : Digits) : ℕ := (Preparation.value d).1.length
noncomputable def answer (d : Digits) (bs : List Bool) : List Bool := (PostCode.run (⟨bs⟩,aux d)).bits
 theorem pre_cost_bound : PolyBound Preparation.resource preCost := by
  have hi := Preparation.input_bound
  have hl := hi.mono digits_length
  have hb : PolyBound Preparation.resource
      (fun d => 2*d.bits.length+2+feedCost d.bits+1) :=
    (((PolyBound.const _ 7).mul hl).add (PolyBound.const _ 3)).mono (fun d => Box.boxes_bound d.bits)
  exact (((hb.add ((PolyBound.const _ 6).mul hi)).add (PolyBound.const _ 3)).add
    Preparation.cost_bound).add (PolyBound.const _ 4) |>.mono (by intro d; unfold preCost; omega)
 theorem amount_bound : PolyBound Preparation.resource amount :=
  Preparation.output_bound.mono (fun d => (Size.length _).trans (Size.fst (Preparation.value d)))
 theorem aux_bound : PolyBound Preparation.resource (fun d => treeSize (encode (aux d))) :=
  Preparation.output_bound.mono (fun d => Size.snd (Preparation.value d))
 noncomputable def postBudget (K e : ℕ) (d : Digits) : ℕ :=
   K*(4*amount d+treeSize (encode (aux d))+3)^e
 theorem input_size (d : Digits) (bs : List Bool) :
    treeSize (encode ((⟨bs⟩ : Digits),aux d))≤4*bs.length+treeSize (encode (aux d))+2 := by
  change treeSize (.pair (listTree boolData bs) (encode (aux d)))≤_
  rw [Halve.listTree_boolData,treeSize_pair]
  have h := RandomTable.list_size bs
  omega
 theorem post_budget (K e : ℕ) (h : ∀ z, postCost z≤K*(treeSize (encode z)+1)^e)
    (d : Digits) (bs : List Bool) (hl : bs.length=amount d) :
    postCost (⟨bs⟩,aux d)≤postBudget K e d := by
  apply (h _).trans
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  have hi := input_size d bs
  rw [hl] at hi
  omega
 theorem budget_bound (K e : ℕ) : PolyBound Preparation.resource (postBudget K e) :=
  (PolyBound.const _ K).mul (((((PolyBound.const _ 4).mul amount_bound).add aux_bound).add
    (PolyBound.const _ 3)).pow e)
 noncomputable def limit (K e : ℕ) (d : Digits) : ℕ := preCost d+36*amount d+postBudget K e d+20
 theorem limit_bound (K e : ℕ) : PolyBound Preparation.resource (limit K e) :=
  ((pre_cost_bound.add ((PolyBound.const _ 36).mul amount_bound)).add (budget_bound K e)).add (PolyBound.const _ 20)
 theorem trace (K e : ℕ) (h : ∀ z, postCost z≤K*(treeSize (encode z)+1)^e) (d : Digits) :
    ∃ t : RandomTree (Config program), Traces program (RegisterBits.initial program d.bits) t ∧
      t.All (fun c => c.control=none) ∧ t.bitDepth≤limit K e d ∧
      ∀ f : Config program→ℚ, t.expect f=(FairBits.acc (amount d) []).expect
        (fun bs => f ⟨none,core [] [] [],answer d bs⟩) := by
  have hu : (Preparation.value d).1=List.replicate (amount d) () :=
    List.eq_replicate_of_mem (fun _ _ => Subsingleton.elim _ _)
  have hp : ∀ bits, advance pre bits ⟨some pre.start,core d.bits [] [],[]⟩ (preCost d)=
      ⟨none,store (.pair (listTree (fun _ : Unit => Data.nil) (List.replicate (amount d) ())) (encode (aux d))) [],[]⟩ := by
    intro bits
    have hv : encode (Preparation.value d)=Data.pair
        (listTree (fun _ : Unit => Data.nil) (List.replicate (amount d) ())) (encode (aux d)) := by
      change Data.pair (encode (Preparation.value d).1) (encode (aux d))=_
      rw [hu]
      rfl
    simpa only [hv] using pre_runs d bits
  have hq : ∀ bs, bs.length=amount d → ∀ bits,
      advance post bits ⟨some post.start,store (.pair (listData bs) (encode (aux d))) [],[]⟩ (postBudget K e d)=
      ⟨none,core [] [] [],answer d bs⟩ := by
    intro bs hl bits
    have hr := post_runs (⟨bs⟩,aux d) bits
    apply advance_pad _ _ _ bits (post_budget K e h d bs hl) ?_ rfl
    have hv : encode ((⟨bs⟩ : Digits),aux d)=Data.pair (listData bs) (encode (aux d)) := by
      change Data.pair (listTree boolData bs) _=_
      rw [Halve.listTree_boolData]
    simpa only [hv,answer] using hr
  obtain ⟨t,ht,hh,hd,he⟩ := RandomTable.complete_trace pre post pre_quiet post_quiet d.bits
    (encode (aux d)) (answer d) (amount d) (preCost d) (postBudget K e d) hp hq
  refine ⟨t,?_,hh,hd,he⟩
  have hi : RegisterBits.initial program d.bits=RandomTable.cfg pre post 0 d.bits [] [] := by
    apply BinaryData.Take.config_ext <;> (try rfl)
    funext i; fin_cases i <;> rfl
  rw [hi]
  exact ht
end MeanPayoff.Realizer

end

end OAI
