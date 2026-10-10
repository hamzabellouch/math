import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.BlueTableSize
import OAI.Combinatorics.KMedianRecovery.Recovery.LogSubsetBound

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueProgram
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n m : ℕ} {R : Type*} [LinearOrder R]
def pack (extra : List Bool) (er : R→List Bool) (B : Finset R) (F : Finset (Fin n))
    (label : R→Fin m) (q : R→Fin n→ℚ) (U : Finset (Fin m)) (c : ℕ) : List Bool :=
  encode [BinaryBlueItem.records (fun i=>i.val.bits) er B label q,BinaryFinSet.encode F,
    BinaryFinSet.encode U,List.replicate c true,extra]
noncomputable def states (d : ℕ) (x : List Bool) : List Bool := BinaryBlueStates.run d (pairBits (x,field 2 x))
noncomputable def states_computes (d : ℕ) : PolyComputes (states d) :=
  (id_computes.pair (field_computes 2)).comp (BinaryBlueStates.run_computes d)
noncomputable def prepare (d : ℕ) (x : List Bool) : List Bool := encode [field 0 x,field 1 x,states d x,field 2 x,field 3 x]
noncomputable def prepare_computes (d : ℕ) : PolyComputes (prepare d) :=
  cons_computes (field_computes 0) (cons_computes (field_computes 1) (cons_computes (states_computes d)
    (cons_computes (field_computes 2) (cons_computes (field_computes 3) (const_computes [])))))
lemma prepare_pack (d : ℕ) (extra : List Bool) (er : R→List Bool) (B : Finset R) (F : Finset (Fin n))
    (label : R→Fin m) (q : R→Fin n→ℚ) (U : Finset (Fin m)) (c : ℕ)
    (h : 2^U.card*(2*(BinaryFinSet.encode U).length+2)≤
      ((pairBits (pack extra er B F label q U c,BinaryFinSet.encode U)).length+1)^d) :
    prepare d (pack extra er B F label q U c)=BinaryBlueLoop.pack er B F label q U c := by
  have hs : states d (pack extra er B F label q U c)=encode ((BlueDP.states U).map BinaryFinSet.encode) := by
    unfold states
    rw [show field 2 (pack extra er B F label q U c)=BinaryFinSet.encode U by
      simp only [pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some],BinaryBlueStates.run_pack d _ U h]
  unfold prepare
  rw [hs]
  simp only [pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,BinaryBlueLoop.pack]
noncomputable def run (d : ℕ) : List Bool→List Bool := BinaryBlueLoop.run ∘ prepare d
noncomputable def run_computes (d : ℕ) : PolyComputes (run d) := (prepare_computes d).comp BinaryBlueLoop.run_computes
lemma run_pack (d : ℕ) (extra : List Bool) (er : R→List Bool) (B : Finset R) (F : Finset (Fin n))
    (label : R→Fin m) (q : R→Fin n→ℚ) (U : Finset (Fin m)) (c : ℕ)
    (h : 2^U.card*(2*(BinaryFinSet.encode U).length+2)≤
      ((pairBits (pack extra er B F label q U c,BinaryFinSet.encode U)).length+1)^d) :
    run d (pack extra er B F label q U c)=
      BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (BinaryBlueCell.atomEnc er)) (BlueDP.best (BlueDP.block B F label q) c U) := by
  rw [run,Function.comp_apply,prepare_pack d extra er B F label q U c h,BinaryBlueLoop.run_pack]
lemma source_run (A : ℝ) : ∃ d : ℕ, ∀ (extra : List Bool) (er : R→List Bool) (B : Finset R) (F : Finset (Fin n))
    (label : R→Fin m) (q : R→Fin n→ℚ) (U : Finset (Fin m)) (c N : ℕ),
    N≤extra.length → (U.card:ℝ)≤A*Real.log ((N:ℝ)+2) →
    run d (pack extra er B F label q U c)=
      BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (BinaryBlueCell.atomEnc er)) (BlueDP.best (BlueDP.block B F label q) c U) := by
  obtain ⟨d,hd⟩:=BinaryBlueStates.source_capacity A
  refine ⟨d,?_⟩
  intro extra er B F label q U c N hN hU
  apply run_pack
  apply hd _ _ N _ hU
  have he : extra.length≤(pack extra er B F label q U c).length := member_length (by simp)
  simp only [pairBits_length]
  omega
end MetricKMedianRecovery.BitMachine.BinaryBlueProgram

namespace MetricKMedianRecovery.BitMachine.BinaryBlueOutput
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {m n r : ℕ}
noncomputable def matching (x : List Bool) : Bool :=
  WordEq.eq (pairBits (extractPrefix (discardPrefix x),extractPrefix x))
noncomputable def matching_computes : PolyComputes (fun x=>[matching x]) :=
  ((discardPrefix_computes.comp extractPrefix_computes).pair extractPrefix_computes).comp WordEq.eq_computes
noncomputable def pick (x : List Bool) : List Bool := head (filterWith matching x)
noncomputable def pick_computes : PolyComputes pick := (filterWith_computes matching_computes).comp WordList.head_computes
abbrev atomEnc := BinaryBlueCell.atomEnc (fun i : Fin r=>i.val.bits) (m:=m) (n:=n)
lemma pick_pack (r0 : Fin r) (y0 : Fin n) (xs : List (BlueDP.Atom (Fin m) (Fin r) (Fin n)))
    (l : Fin m) (hl : l∈(BlueDP.labels xs).toFinset) :
    pick (pairBits (l.val.bits,BinaryBlueMerge.listEnc atomEnc xs))=atomEnc (BlueDP.pick r0 y0 xs l) := by
  have he : filterWith matching (pairBits (l.val.bits,BinaryBlueMerge.listEnc atomEnc xs))=
      encode ((xs.filter (fun a=>decide (a.1=l))).map atomEnc) := by
    simp only [BinaryBlueMerge.listEnc,filterWith_encode,List.filter_map,Function.comp_def,matching,atomEnc,
      BinaryBlueCell.atomEnc,BinaryBlueItem.atomEnc,extractPrefix_pairBits,discardPrefix_pairBits,
      WordEq.eq_pair,BinaryBlueCell.finValBits_injective.eq_iff]
  rw [pick,he]
  clear he
  induction xs with
  | nil=>simp only [BlueDP.labels,List.map_nil,List.toFinset_nil,Finset.notMem_empty] at hl
  | cons a xs ih=>
    by_cases ha : a.1=l
    · simp [BlueDP.pick,ha,encode]
    · have htail : l∈(BlueDP.labels xs).toFinset := by
        simpa [BlueDP.labels,Ne.symm ha] using hl
      simpa [BlueDP.pick,ha] using ih htail

noncomputable def query (x : List Bool) : List Bool := pairBits (discardPrefix x,extractPrefix x)
noncomputable def query_computes : PolyComputes query := discardPrefix_computes.pair extractPrefix_computes
noncomputable def source (x : List Bool) : List Bool := extractPrefix (discardPrefix (pick (query x)))
noncomputable def source_computes : PolyComputes source :=
  ((query_computes.comp pick_computes).comp discardPrefix_computes).comp extractPrefix_computes
noncomputable def destination (x : List Bool) : List Bool := discardPrefix (discardPrefix (pick (query x)))
noncomputable def destination_computes : PolyComputes destination :=
  ((query_computes.comp pick_computes).comp discardPrefix_computes).comp discardPrefix_computes
noncomputable def prepared (x : List Bool) : List Bool := pairBits (BinaryBlueMerge.payload (extractPrefix x),discardPrefix x)
noncomputable def prepared_computes : PolyComputes prepared :=
  (extractPrefix_computes.comp BinaryBlueMerge.payload_computes).pair discardPrefix_computes
noncomputable def run (x : List Bool) : List Bool := encode [mapWith source (prepared x),mapWith destination (prepared x)]
noncomputable def run_computes : PolyComputes run := by
  unfold run
  have computes := cons_computes (prepared_computes.comp (mapWith_computes source_computes))
    (cons_computes (prepared_computes.comp (mapWith_computes destination_computes)) (const_computes []))
  simpa only [Function.comp_def,encode] using computes
lemma run_some (r0 : Fin r) (y0 : Fin n) (k : ℚ) (xs : List (BlueDP.Atom (Fin m) (Fin r) (Fin n)))
    (h : (BlueDP.labels xs).toFinset=Finset.univ) :
    run (pairBits (BinaryBlueChoice.encode (BinaryBlueMerge.listEnc atomEnc) (some (k,xs)),
      BinaryFinSet.table (id : Fin m→Fin m)))=
      encode [BinaryFinSet.table (fun l=>(BlueDP.pick r0 y0 xs l).2.1),
        BinaryFinSet.table (fun l=>(BlueDP.pick r0 y0 xs l).2.2)] := by
  have hp (l : Fin m) : pick (pairBits (l.val.bits,BinaryBlueMerge.listEnc atomEnc xs))=atomEnc (BlueDP.pick r0 y0 xs l) :=
    pick_pack r0 y0 xs l (h ▸ Finset.mem_univ l)
  simp only [run,prepared,extractPrefix_pairBits,discardPrefix_pairBits,BinaryBlueMerge.payload,
    BinaryBlueChoice.encode,encode,head_cons,BinaryFinSet.table,mapWith_ofFn,source,destination,query,hp,
    atomEnc,BinaryBlueCell.atomEnc,BinaryBlueItem.atomEnc,id_eq]
lemma run_best (B : Finset (Fin r)) (F : Finset (Fin n)) (label : Fin r→Fin m) (q : Fin r→Fin n→ℚ)
    (c : ℕ) (r0 : Fin r) (y0 : Fin n) (k : ℚ) (xs : List (BlueDP.Atom (Fin m) (Fin r) (Fin n)))
    (h : BlueDP.best (BlueDP.block B F label q) c Finset.univ=some (k,xs)) :
    run (pairBits (BinaryBlueChoice.encode (BinaryBlueMerge.listEnc atomEnc) (BlueDP.best (BlueDP.block B F label q) c Finset.univ),
      BinaryFinSet.table (id : Fin m→Fin m)))=
      encode [BinaryFinSet.table (BlueDP.makePlan B F label q c r0 y0 k xs h).sel,
        BinaryFinSet.table (BlueDP.makePlan B F label q c r0 y0 k xs h).dst] := by
  have hs:=BlueDP.best_spec B F label q c Finset.univ
  rw [h] at hs
  rw [h,run_some r0 y0 k xs hs.1.2]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryBlueOutput

end OAI
