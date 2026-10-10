import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.LengthEncode
import OAI.Combinatorics.KMedianRecovery.Machines.LengthQuery

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySensitive
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalLengthView
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
def pack {m : ℕ} (base : List Bool) (n q key : ℕ) (b : ℚ) (k N : ℕ)
    (H : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) (J : Plan (Label (Fin m))) : List Bool :=
  encode [base,List.replicate n true,List.replicate q true,key.bits,BinaryRational.encode b,k.bits,List.replicate N true,
    labels H,historyBits T,historyBits U,BinaryLength.planBits J]
def jf (n : ℕ) : List Bool→List Bool := field n ∘ field 10
noncomputable def jf_computes (n : ℕ) : PolyComputes (jf n) := (field_computes 10).comp (field_computes n)
noncomputable def isFree (x : List Bool) : Bool := decide (value (jf 0 x)=0)
noncomputable def isFree_computes : PolyComputes (fun x=>[isFree x]) := by
  simpa only [isFree,value_bits] using NatOps.eq (jf_computes 0) (const_computes (0:ℕ).bits)
noncomputable def common (x : List Bool) : List Bool := if isFree x then field 7 x else jf 3 x++jf 4 x
noncomputable def common_computes : PolyComputes common := isFree_computes.cond (field_computes 7) ((jf_computes 3).append (jf_computes 4))
noncomputable def small (x : List Bool) : List Bool := if isFree x then field 9 x else field 8 x
noncomputable def small_computes : PolyComputes small := isFree_computes.cond (field_computes 9) (field_computes 8)
noncomputable def large (x : List Bool) : List Bool := if isFree x then field 8 x else field 9 x
noncomputable def large_computes : PolyComputes large := isFree_computes.cond (field_computes 8) (field_computes 9)
lemma views_pack {m : ℕ} (base : List Bool) (n q key : ℕ) (b : ℚ) (k N : ℕ)
    (H : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) (J : Plan (Label (Fin m))) :
    common (pack base n q key b k N H T U J)=labels (J.common H) ∧
    small (pack base n q key b k N H T U J)=historyBits (J.small T U) ∧
    large (pack base n q key b k N H T U J)=historyBits (J.large T U) ∧
    jf 1 (pack base n q key b k N H T U J)=BinaryLabel.encode J.root := by
  cases J <;> simp [common,small,large,isFree,jf,pack,BinaryLength.planBits,
    field_encode,value,Plan.common,Plan.small,Plan.large,Plan.root,BinaryFiniteContext.labels_append]

noncomputable def opened (x : List Bool) : List Bool := BinaryFiniteContext.union (pairBits (field 3 (field 0 x),common x))
noncomputable def opened_computes : PolyComputes opened :=
  (((field_computes 0).comp (field_computes 3)).pair common_computes).comp BinaryFiniteContext.union_computes
noncomputable def base (x : List Bool) : List Bool := BinaryFiniteContext.replaceOpen (pairBits (field 0 x,opened x))
noncomputable def base_computes : PolyComputes base := ((field_computes 0).pair opened_computes).comp BinaryFiniteContext.replaceOpen_computes
lemma base_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (b : ℚ) (k N : ℕ)
    (H : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) (J : Plan (Label (Fin m))) :
    base (pack (BinaryFiniteContext.pack distance loc F Q v z lam) n q key b k N H T U J)=
      BinaryFiniteContext.pack distance loc F (Q∪(J.common H).toFinset) v z lam := by
  have hh:=(views_pack (BinaryFiniteContext.pack distance loc F Q v z lam) n q key b k N H T U J).1
  unfold base opened
  rw [hh]
  simp only [pack,field_encode,List.getElem?_cons_zero,Option.getD_some]
  have hf : field 3 (BinaryFiniteContext.pack distance loc F Q v z lam)=setBits Q := by
    simp only [BinaryFiniteContext.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [hf,BinaryFiniteContext.union_list_pack,BinaryFiniteContext.replaceOpen_pack]
noncomputable def nextQ (x : List Bool) : List Bool := true::field 2 x
noncomputable def nextQ_computes : PolyComputes nextQ := (const_computes [true]).append (field_computes 2)
noncomputable def context (x : List Bool) : List Bool := encode [base x,field 1 x,nextQ x,field 3 x,jf 1 x,field 4 x,small x,large x]
noncomputable def context_computes : PolyComputes context :=
  list_computes [base,field 1,nextQ,field 3,jf 1,field 4,small,large] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨base_computes⟩
    · exact ⟨field_computes 1⟩
    · exact ⟨nextQ_computes⟩
    · exact ⟨field_computes 3⟩
    · exact ⟨jf_computes 1⟩
    · exact ⟨field_computes 4⟩
    · exact ⟨small_computes⟩
    · exact ⟨large_computes⟩)
lemma context_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (b : ℚ) (k N : ℕ)
    (H : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) (J : Plan (Label (Fin m))) :
    context (pack (BinaryFiniteContext.pack distance loc F Q v z lam) n q key b k N H T U J)=
      BinaryLengthQuery.ctxBits (BinaryFiniteContext.pack distance loc F (Q∪(J.common H).toFinset) v z lam)
        n (q+1) key J.root b (J.small T U) (J.large T U) := by
  obtain ⟨_,hs,hl,hr⟩:=views_pack (BinaryFiniteContext.pack distance loc F Q v z lam) n q key b k N H T U J
  unfold context
  rw [base_pack,hs,hl,hr]
  simp only [nextQ,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryLengthQuery.ctxBits,List.replicate_succ]
noncomputable def searchInput (x : List Bool) : List Bool := encode [field 6 x,context x,field 5 x,BinaryRational.encode 0,field 4 x]
noncomputable def searchInput_computes : PolyComputes searchInput :=
  list_computes [field 6,context,field 5,(fun _=>BinaryRational.encode 0),field 4] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    · exact ⟨field_computes 6⟩
    · exact ⟨context_computes⟩
    · exact ⟨field_computes 5⟩
    · exact ⟨const_computes (BinaryRational.encode 0)⟩
    · exact ⟨field_computes 4⟩)
noncomputable def atZero (x : List Bool) : List Bool := pairBits (context x,BinaryRational.encode 0)
noncomputable def atZero_computes : PolyComputes atZero := context_computes.pair (const_computes (BinaryRational.encode 0))
noncomputable def earlyEqual (x : List Bool) : Bool := decide (value (BinaryLengthQuery.count (atZero x))=value (field 5 x))
noncomputable def earlyEqual_computes : PolyComputes (fun x=>[earlyEqual x]) :=
  NatOps.eq (atZero_computes.comp BinaryLengthQuery.count_computes) (field_computes 5)
noncomputable def early (x : List Bool) : List Bool := encode [(0:ℕ).bits,BinaryRational.encode 0,[],small x,[]]
noncomputable def early_computes : PolyComputes early :=
  cons_computes (const_computes (0:ℕ).bits) (cons_computes (const_computes (BinaryRational.encode 0))
    (cons_computes (const_computes []) (cons_computes small_computes (cons_computes (const_computes []) (const_computes [])))))
noncomputable def run (x : List Bool) : List Bool := if earlyEqual x then early x else BinaryLengthSearch.run (searchInput x)
noncomputable def run_computes : PolyComputes run := earlyEqual_computes.cond early_computes
  (searchInput_computes.comp BinaryLengthSearch.run_computes)
lemma run_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (F : Finset (Fin m)) (Q : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (b : ℚ) (k N : ℕ)
    (H : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) (J : Plan (Label (Fin m))) :
    run (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q v z lam) n q key b k N H T U J)=
      BinaryLengthSearch.resultBits (CanonicalSensitiveEndpoint.run loc distance F Q v lam b q n k key N H T U J) := by
  let ctx:=BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q v z lam
  have hctx:=context_pack distance (fun j=>original (loc j)) (F.image original) Q v z lam n q key b k N H T U J
  have hsmall:=(views_pack ctx n q key b k N H T U J).2.1
  change run (pack ctx n q key b k N H T U J)=_
  unfold run early earlyEqual atZero searchInput
  rw [show context (pack ctx n q key b k N H T U J)=_ from hctx,hsmall]
  have hf5 : field 5 (pack ctx n q key b k N H T U J)=k.bits := by simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  have hf6 : field 6 (pack ctx n q key b k N H T U J)=List.replicate N true := by simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  have hf4 : field 4 (pack ctx n q key b k N H T U J)=BinaryRational.encode b := by simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  rw [hf5,hf6,hf4,BinaryLengthQuery.count_pack]
  simp only [value_bits,CanonicalLengthSearch.count,CanonicalLengthSearch.chosen,ite_true,decide_eq_true_eq]
  rw [←BinaryBisection.pack,BinaryLengthSearch.run_pack]
  dsimp only [CanonicalSensitiveEndpoint.run]
  split_ifs <;> rfl
end MetricKMedianRecovery.BitMachine.BinarySensitive

namespace MetricKMedianRecovery.PhaseHistoryTransfer
open PhaseSequence
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma History.phase_bound {loc : D → X} {F B Q : Finset X} {v lam eta : ℝ}
    {q : ℕ} {P : List (List X)} (h : History loc F B v lam eta q Q P) :
    ∀ H∈P,H.length≤F.card+B.card ∧ ∀ x∈H,x∈F∪B := by
  induction h with
  | nil=>simp
  | @cons q Q H T hh ht ih=>
    intro G hG
    rcases List.mem_cons.mp hG with rfl|hG
    · refine ⟨?_,fun x hx=>hh.1.opened_subset (List.mem_toFinset.mpr hx)⟩
      have hs:=Finset.card_le_card hh.1.opened_subset
      rw [List.toFinset_card_of_nodup hh.1.nodup] at hs
      exact hs.trans (Finset.card_union_le F B)
    · exact ih G hG

lemma History.flatten_bound {loc : D → X} {F B Q : Finset X} {v lam eta : ℝ}
    {q : ℕ} {P : List (List X)} (h : History loc F B v lam eta q Q P) :
    P.flatten.length≤P.length*(F.card+B.card) := by
  have hb:=h.phase_bound
  clear h
  induction P with
  | nil=>simp
  | cons H P ih=>
    have hH:=(hb H (List.mem_cons_self)).1
    have ht:=ih (fun G hG=>hb G (List.mem_cons_of_mem _ hG))
    simp only [List.flatten_cons,List.length_append,List.length_cons]
    nlinarith
end MetricKMedianRecovery.PhaseHistoryTransfer

end OAI
