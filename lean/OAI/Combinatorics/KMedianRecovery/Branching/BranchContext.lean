import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.ClassFilter

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchContext
open WordOperations WordList
open BinaryOpeningPayment (field field_computes field_encode)
variable {n m : ℕ}
def pack (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (label : Fin n→Fin m) (k c : ℕ) (extra : List Bool) : List Bool :=
  encode [RationalMatrix.encode δ,BinaryFinSet.encode D,BinaryFinSet.encode F,BinaryFinSet.encode S,
    BinaryRational.encode Δ,BinarySamplingState.encode s,BinaryFinSet.table colors,BinaryFinSet.table label,
    BinaryFinSet.table (id : Fin m→Fin m),k.bits,List.replicate c true,extra]
noncomputable def remaining (x : List Bool) : List Bool := BinaryNatSet.diff (pairBits (field 3 x,extractPrefix (field 5 x)))
noncomputable def remaining_computes : PolyComputes remaining :=
  ((field_computes 3).pair ((field_computes 5).comp extractPrefix_computes)).comp BinaryNatSet.diff_computes
attribute [local irreducible] remaining
noncomputable def context (x : List Bool) : List Bool := encode [lengthBits (field 0 x),field 4 x,remaining x,discardPrefix (field 5 x)]
noncomputable def context_computes : PolyComputes context :=
  (cons_computes ((field_computes 0).comp lengthBits_computes) (cons_computes (field_computes 4) (cons_computes remaining_computes (cons_computes ((field_computes 5).comp discardPrefix_computes) (const_computes [])))))
attribute [local irreducible] context
noncomputable def oracle (x : List Bool) : List Bool := encode [field 0 x,field 1 x,context x]
noncomputable def oracle_computes : PolyComputes oracle :=
  (cons_computes (field_computes 0) (cons_computes (field_computes 1) (cons_computes context_computes (const_computes []))))
attribute [local irreducible] oracle
noncomputable def classOf (j : ℕ) (x : List Bool) : List Bool := BinaryClassFilter.run
  (pairBits (pairBits (field 6 x,j.bits),remaining x))
noncomputable def classOf_computes (j : ℕ) : PolyComputes (classOf j) :=
  (((field_computes 6).pair (const_computes j.bits)).pair remaining_computes).comp BinaryClassFilter.run_computes
attribute [local irreducible] classOf
noncomputable def greenContext (x : List Bool) : List Bool := encode [lengthBits (field 0 x),field 4 x,classOf 0 x,discardPrefix (field 5 x)]
noncomputable def greenContext_computes : PolyComputes greenContext :=
  (cons_computes ((field_computes 0).comp lengthBits_computes) (cons_computes (field_computes 4) (cons_computes (classOf_computes 0) (cons_computes ((field_computes 5).comp discardPrefix_computes) (const_computes [])))))
attribute [local irreducible] greenContext
noncomputable def greenOracle (x : List Bool) : List Bool := encode [field 0 x,field 1 x,greenContext x]
noncomputable def greenOracle_computes : PolyComputes greenOracle :=
  (cons_computes (field_computes 0) (cons_computes (field_computes 1) (cons_computes greenContext_computes (const_computes []))))
attribute [local irreducible] greenOracle
noncomputable def ballInput (x : List Bool) : List Bool := encode [field 0 x,field 2 x,discardPrefix (field 5 x)]
noncomputable def ballInput_computes : PolyComputes ballInput :=
  (cons_computes (field_computes 0) (cons_computes (field_computes 2) (cons_computes ((field_computes 5).comp discardPrefix_computes) (const_computes []))))
attribute [local irreducible] ballInput
noncomputable def copyData (x : List Bool) : List Bool := BinaryBranchBalls.run (ballInput x)
noncomputable def copyData_computes : PolyComputes copyData :=
  ballInput_computes.comp BinaryBranchBalls.run_computes
attribute [local irreducible] copyData
noncomputable def parts (x : List Bool) : List Bool := BinaryCopyTables.parts (copyData x)
noncomputable def parts_computes : PolyComputes parts :=
  copyData_computes.comp BinaryCopyTables.parts_computes
attribute [local irreducible] parts
noncomputable def origins (x : List Bool) : List Bool := BinaryCopyTables.origins (copyData x)
noncomputable def origins_computes : PolyComputes origins := by
  have originsComputes := copyData_computes.comp BinaryCopyTables.origins_computes
  unfold origins
  simpa only [Function.comp_def] using originsComputes
attribute [local irreducible] origins
noncomputable def locations (x : List Bool) : List Bool := BinaryCopyTables.locations (copyData x)
noncomputable def locations_computes : PolyComputes locations :=
  copyData_computes.comp BinaryCopyTables.locations_computes
attribute [local irreducible] locations
def balls (δ : Fin n→Fin n→ℚ) (F : Finset (Fin n)) (s : RationalSampling.State n) : Fin s.leaves.length→Finset (Fin n) :=
  fun i=>F.filter (fun f=>δ s.leaves[i.val].1 f ≤ s.leaves[i.val].2)
section Correct
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (label : Fin n→Fin m) (k c : ℕ) (extra : List Bool)
local notation "data" => pack δ D F S Δ s colors label k c extra
local notation "G" => Finset.filter (fun i=>colors i=0) (S\RationalSampling.State.deleted s)
local notation "H" => balls δ F s
lemma remaining_pack : remaining data=BinaryFinSet.encode (S\s.deleted) := by
  simp only [remaining,pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
    BinarySamplingState.encode,extractPrefix_pairBits,BinaryFinSet.diff_pack]
lemma context_pack : context data=BinarySamplingState.context Δ S s := by
  rw [context,remaining_pack]
  simp only [pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
    BinarySamplingState.encode,discardPrefix_pairBits,RationalMatrix.encode,lengthBits_encode,List.length_ofFn,
    BinarySamplingState.context]
lemma oracle_pack : oracle data=BinarySamplingOracle.pack δ D S Δ s := by
  rw [oracle,context_pack]
  simp only [pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,BinarySamplingOracle.pack]
lemma classOf_pack (j : Fin 3) : classOf j.val data=BinaryFinSet.encode ((S\s.deleted).filter (fun i=>colors i=j)) := by
  rw [classOf,remaining_pack]
  simp only [pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some]
  exact BinaryClassFilter.run_pack _ colors j
lemma greenContext_pack : greenContext data=BinarySamplingState.context Δ G ⟨∅,s.leaves⟩ := by
  have hj:=classOf_pack δ D F S Δ s colors label k c extra (0:Fin 3)
  change classOf 0 data=_ at hj
  rw [greenContext,hj]
  simp only [pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
    BinarySamplingState.encode,discardPrefix_pairBits,RationalMatrix.encode,lengthBits_encode,List.length_ofFn,
    BinarySamplingState.context,Finset.sdiff_empty]
lemma greenOracle_pack : greenOracle data=BinarySamplingOracle.pack δ D G Δ ⟨∅,s.leaves⟩ := by
  rw [greenOracle,greenContext_pack]
  simp only [pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,BinarySamplingOracle.pack]
lemma leavesBits_eq : BinaryNearestLeaf.leavesBits s.leaves=encode
    (List.ofFn (fun i : Fin s.leaves.length=>BinarySamplingReference.leafBits s.leaves[i.val].1 s.leaves[i.val].2)) := by
  unfold BinaryNearestLeaf.leavesBits
  congr 1
  exact (congrArg (List.map (fun z=>BinarySamplingReference.leafBits z.1 z.2)) (List.ofFn_get s.leaves)).symm.trans List.map_ofFn
lemma ballInput_pack : ballInput data=BinaryBranchBalls.pack δ F (fun i : Fin s.leaves.length=>s.leaves[i.val].1)
    (fun i=>s.leaves[i.val].2) := by
  simp only [ballInput,pack,field_encode,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,
    BinarySamplingState.encode,discardPrefix_pairBits,leavesBits_eq,BinaryBranchBalls.pack]
lemma copyData_pack : copyData data=BinaryCopyTables.pack H := by
  rw [copyData,ballInput_pack,BinaryBranchBalls.run_pack]
  rfl
lemma parts_pack : parts data=BinaryFinSet.table (Completion.CopyGround.part (n:=n) (a:=s.leaves.length)) := by
  rw [parts,copyData_pack,BinaryCopyTables.parts_pack]
lemma origins_pack (hH : ∀ i,(H i).Nonempty) : origins data=BinaryFinSet.table (Completion.CopyGround.origin H hH) := by
  rw [origins,copyData_pack,BinaryCopyTables.origins_pack _ hH]
lemma locations_pack (hH : ∀ i,(H i).Nonempty) : locations data=BinaryFinSet.table (Completion.CopyGround.location H hH) := by
  rw [locations,copyData_pack,BinaryCopyTables.locations_pack _ hH]
end Correct
end MetricKMedianRecovery.BitMachine.BinaryBranchContext

end OAI
