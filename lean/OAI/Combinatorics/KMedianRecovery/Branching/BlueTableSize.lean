import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.BluePlan

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueSize
open WordOperations WordList RationalHeight
variable {n m : ℕ} {R : Type*} [LinearOrder R]
lemma states_bounds (U : Finset (Fin m)) (N : ℕ) (hN : (encode ((BlueDP.states U).map BinaryFinSet.encode)).length≤N) :
    U.card≤N ∧ 2^U.card≤N ∧ ∀ W⊆U,(BinaryFinSet.encode W).length≤N := by
  have hw (W : Finset (Fin m)) (hW : W⊆U) : (BinaryFinSet.encode W).length≤N :=
    (length_member_le_encode (List.mem_map.mpr ⟨W,(BlueDP.mem_states U W).mpr hW,rfl⟩)).trans hN
  have hc : U.card≤(BinaryFinSet.encode U).length := by
    simpa only [BinaryFinSet.encode_eq,List.length_map,Finset.length_sort] using
      length_le_encode ((U.sort (·≤·)).map (fun i=>i.val.bits))
  refine ⟨hc.trans (hw U le_rfl),?_,hw⟩
  have hp : 2^U.card≤(encode ((BlueDP.states U).map BinaryFinSet.encode)).length := by
    simpa only [List.length_map,BlueDP.states_length] using length_le_encode ((BlueDP.states U).map BinaryFinSet.encode)
  exact hp.trans hN
lemma table_length (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m)
    (q : R→Fin n→ℚ) (U : Finset (Fin m)) (t N : ℕ)
    (hr : (BinaryBlueItem.records (fun i=>i.val.bits) er B label q).length≤N)
    (hs : (encode ((BlueDP.states U).map BinaryFinSet.encode)).length≤N) :
    (BinaryBlueLookup.encode BinaryFinSet.encode (BinaryBlueItem.atomEnc (fun i : Fin m=>i.val.bits) er)
      (BlueDP.tables (BlueDP.block B F label q) U t)).length≤102*(N+1)^3 := by
  obtain ⟨hu,hpow,hw⟩:=states_bounds U N hs
  rw [BlueDP.tables_eq,BinaryBlueLookup.encode,List.map_map]
  have hb : ∀ W∈BlueDP.states U,
      (pairBits (BinaryFinSet.encode W,BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (BinaryBlueItem.atomEnc (fun i : Fin m=>i.val.bits) er))
        (BlueDP.recurrence (BlueDP.block B F label q) t W))).length≤50*(N+1)^2 := by
    intro W hW
    have hWU:=(BlueDP.mem_states U W).mp hW
    have hc:=(Finset.card_le_card hWU).trans hu
    have hkey:=hw W hWU
    have hx:=candidate_bound (fun i : Fin m=>i.val.bits) er B F label q W t _ (BlueDP.recurrence_spec B F label q t W)
    have hy : 40*(W.card+1)*((BinaryBlueItem.records (fun i : Fin m=>i.val.bits) er B label q).length+1)≤40*(N+1)^2 := by
      calc
        _ ≤40*(N+1)*(N+1) := by gcongr
        _ = _ := by ring
    have hxy:=hx.trans hy
    simp only [pairBits_length]
    nlinarith
  have ht:=Subsets.encode_bound ((BlueDP.states U).map (fun W=>
      pairBits (BinaryFinSet.encode W,BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (BinaryBlueItem.atomEnc (fun i : Fin m=>i.val.bits) er))
        (BlueDP.recurrence (BlueDP.block B F label q) t W)))) (50*(N+1)^2) (by
          intro z hz
          obtain ⟨W,hW,rfl⟩:=List.mem_map.mp hz
          exact hb W hW)
  simp only [List.length_map,BlueDP.states_length] at ht
  apply ht.trans
  calc
    _ ≤N*(2*(50*(N+1)^2)+2) := Nat.mul_le_mul_right _ hpow
    _ ≤_ := by nlinarith
lemma tableRun_best_bound (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m)
    (q : R→Fin n→ℚ) (U : Finset (Fin m)) (t N : ℕ)
    (hr : (BinaryBlueItem.records (fun i=>i.val.bits) er B label q).length≤N)
    (hs : (encode ((BlueDP.states U).map BinaryFinSet.encode)).length≤N) :
    (BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (BinaryBlueItem.atomEnc (fun i : Fin m=>i.val.bits) er))
      (BlueDP.tableRun (BlueDP.block B F label q) U t).2).length≤40*(N+1)^2 := by
  rw [BlueDP.tableRun_spec]
  dsimp only
  have hp : BlueDP.Spec B F label q U t (BlueDP.select ((List.range t).map (fun j=>BlueDP.recurrence (BlueDP.block B F label q) (j+1) U))) := by
    apply BlueDP.select_spec _ _ trivial
    intro z hz
    obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hz
    exact BlueDP.spec_mono B F label q U (j+1) t (by have hh:=List.mem_range.mp hj;omega) _ (BlueDP.recurrence_spec B F label q (j+1) U)
  apply (candidate_bound (fun i : Fin m=>i.val.bits) er B F label q U t _ hp).trans
  have hu := (states_bounds U N hs).1
  calc
    _ ≤40*(N+1)*(N+1) := by gcongr
    _ = _ := by ring
end MetricKMedianRecovery.BitMachine.BinaryBlueSize

namespace MetricKMedianRecovery.BitMachine.BinaryBlueLoop
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n m : ℕ} {R : Type*} [LinearOrder R]
def pack (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U : Finset (Fin m)) (c : ℕ) : List Bool :=
  encode [BinaryBlueItem.records (fun i=>i.val.bits) er B label q,BinaryFinSet.encode F,
    encode ((BlueDP.states U).map BinaryFinSet.encode),BinaryFinSet.encode U,List.replicate c true]
def statePack (er : R→List Bool) (cfg : List Bool)
    (s : BlueDP.Table (Fin m) (BlueDP.Atom (Fin m) R (Fin n))×BlueDP.Candidate (List (BlueDP.Atom (Fin m) R (Fin n)))) : List Bool :=
  pairBits (cfg,pairBits (BinaryBlueLookup.encode BinaryFinSet.encode (BinaryBlueCell.atomEnc er) s.1,
    BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (BinaryBlueCell.atomEnc er)) s.2))
noncomputable def oldTable (x : List Bool) : List Bool := extractPrefix (discardPrefix x)
noncomputable def oldTable_computes : PolyComputes oldTable := discardPrefix_computes.comp extractPrefix_computes
noncomputable def oldBest (x : List Bool) : List Bool := discardPrefix (discardPrefix x)
noncomputable def oldBest_computes : PolyComputes oldBest := discardPrefix_computes.comp discardPrefix_computes
noncomputable def nextCtx (x : List Bool) : List Bool := encode
  [field 0 (extractPrefix x),field 1 (extractPrefix x),field 2 (extractPrefix x),oldTable x]
noncomputable def nextCtx_computes : PolyComputes nextCtx :=
  cons_computes (extractPrefix_computes.comp (field_computes 0)) (cons_computes (extractPrefix_computes.comp (field_computes 1))
    (cons_computes (extractPrefix_computes.comp (field_computes 2)) (cons_computes oldTable_computes (const_computes []))))
noncomputable def newTable (x : List Bool) : List Bool := BinaryBlueTable.next (nextCtx x)
noncomputable def newTable_computes : PolyComputes newTable := by
  unfold newTable
  have computes := nextCtx_computes.comp BinaryBlueTable.next_computes
  simpa only [Function.comp_def] using computes
noncomputable def newBest (x : List Bool) : List Bool := BinaryBlueChoice.run
  (pairBits (oldBest x,BinaryBlueLookup.run (pairBits (field 3 (extractPrefix x),newTable x))))
noncomputable def newBest_computes : PolyComputes newBest :=
  (oldBest_computes.pair (((extractPrefix_computes.comp (field_computes 3)).pair newTable_computes).comp BinaryBlueLookup.run_computes)).comp
    BinaryBlueChoice.run_computes
noncomputable def step (x : List Bool) : List Bool := pairBits (extractPrefix x,pairBits (newTable x,newBest x))
noncomputable def step_computes : PolyComputes step := extractPrefix_computes.pair (newTable_computes.pair newBest_computes)
lemma step_pack (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U : Finset (Fin m)) (c : ℕ) (s : BlueDP.Table (Fin m) (BlueDP.Atom (Fin m) R (Fin n))×BlueDP.Candidate (List (BlueDP.Atom (Fin m) R (Fin n)))) :
    step (statePack er (pack er B F label q U c) s)=
      statePack er (pack er B F label q U c) (BlueDP.tableStep (BlueDP.block B F label q) U s) := by
  have hc : nextCtx (statePack er (pack er B F label q U c) s)=BinaryBlueCell.ctxPack er B F label q U s.1 := by
    simp only [nextCtx,statePack,oldTable,extractPrefix_pairBits,discardPrefix_pairBits,pack,field_encode,
      List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryBlueCell.ctxPack]
  have hn : newTable (statePack er (pack er B F label q U c) s)=
      BinaryBlueLookup.encode BinaryFinSet.encode (BinaryBlueCell.atomEnc er) (BlueDP.nextTable (BlueDP.block B F label q) U s.1) := by
    rw [newTable,hc,BinaryBlueTable.next_pack]
  unfold step newBest
  rw [hn]
  simp only [statePack,oldBest,extractPrefix_pairBits,discardPrefix_pairBits,pack,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [BinaryBlueLookup.run_pack _ _ BinaryFinSet.encode_injective,BinaryBlueChoice.run_pack]
  rfl
lemma iterate_pack (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U : Finset (Fin m)) (c t : ℕ) :
    step^[t] (statePack (n:=n) (m:=m) er (pack er B F label q U c) (BlueDP.initialTable U,none))=
      statePack er (pack er B F label q U c) (BlueDP.tableRun (BlueDP.block B F label q) U t) := by
  induction t with
  | zero=>rfl
  | succ t ih=>
    rw [Function.iterate_succ_apply',ih,step_pack]
    simp only [BlueDP.tableRun,Function.iterate_succ_apply']
noncomputable def initial (x : List Bool) : List Bool := pairBits (x,pairBits (BinaryBlueTable.initial (field 2 x),[]))
noncomputable def initial_computes : PolyComputes initial := by
  unfold initial
  have computes := id_computes.pair (((field_computes 2).comp BinaryBlueTable.initial_computes).pair (const_computes []))
  simpa only [Function.comp_def,id_eq] using computes
lemma initial_pack (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U : Finset (Fin m)) (c : ℕ) : initial (pack er B F label q U c)=statePack (n:=n) (m:=m) er (pack er B F label q U c) (BlueDP.initialTable U,none) := by
  simp only [initial,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    BinaryBlueTable.initial_pack (n:=n) er,statePack,BinaryBlueChoice.encode]
noncomputable def capPoly : Polynomial ℕ := 1000*(Polynomial.X+1)^4
noncomputable def cap : PolynomialCounter capPoly := PolynomialCounter.choose _
lemma iterate_length (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U : Finset (Fin m)) (c t : ℕ) :
    (step^[t] (initial (pack er B F label q U c))).length≤(cap.word (pack er B F label q U c)).length := by
  rw [initial_pack,iterate_pack,cap.word_length]
  have hr : (BinaryBlueItem.records (fun i=>i.val.bits) er B label q).length≤(pack er B F label q U c).length := member_length (by simp)
  have hs : (encode ((BlueDP.states U).map BinaryFinSet.encode)).length≤(pack er B F label q U c).length := member_length (by simp)
  have ht:=BinaryBlueSize.table_length er B F label q U t _ hr hs
  have hb:=BinaryBlueSize.tableRun_best_bound er B F label q U t _ hr hs
  simp only [statePack,pairBits_length,BlueDP.tableRun_spec] at ⊢
  simp only [BlueDP.tableRun_spec] at hb
  simp only [capPoly,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  nlinarith
noncomputable def loop (x : List Bool) : List Bool := BoundedIteration.run step
  (pairBits (field 4 x,pairBits (cap.word x,initial x)))
noncomputable def loop_computes : PolyComputes loop :=
  ((field_computes 4).pair (cap.computes.pair initial_computes)).comp (BoundedIteration.run_computes step_computes)
lemma loop_pack (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U : Finset (Fin m)) (c : ℕ) : loop (pack er B F label q U c)=
      statePack er (pack er B F label q U c) (BlueDP.tableRun (BlueDP.block B F label q) U c) := by
  unfold loop
  rw [BoundedIteration.run_eq]
  · rw [show field 4 (pack er B F label q U c)=List.replicate c true by
      simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some],List.length_replicate,
      initial_pack,iterate_pack]
  · intro t _
    exact iterate_length er B F label q U c t
noncomputable def run (x : List Bool) : List Bool := if field 3 x=[] then BinaryBlueChoice.encode id (some (0,[])) else oldBest (loop x)
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [decide_eq_true_eq,Function.comp_def] using ((field_computes 3).comp isEmpty_computes).cond
    (const_computes (BinaryBlueChoice.encode id (some (0,[])))) (loop_computes.comp oldBest_computes)
lemma run_pack (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U : Finset (Fin m)) (c : ℕ) : run (pack er B F label q U c)=
      BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (BinaryBlueCell.atomEnc er)) (BlueDP.best (BlueDP.block B F label q) c U) := by
  rw [run,show field 3 (pack er B F label q U c)=BinaryFinSet.encode U by
    simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]]
  simp only [BinaryBlueStates.key_empty]
  rw [←BlueDP.tableBest_eq,BlueDP.tableBest]
  split_ifs
  · rfl
  · rw [loop_pack]
    simp only [oldBest,statePack,discardPrefix_pairBits]
end MetricKMedianRecovery.BitMachine.BinaryBlueLoop

end OAI
