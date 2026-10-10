import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.CoupledInitial
import OAI.Combinatorics.KMedianRecovery.Machines.BisectionMachine
import OAI.Combinatorics.KMedianRecovery.Recovery.CrossCount
import OAI.Combinatorics.KMedianRecovery.Machines.ResolveResources

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [DecidableEq V]
omit [DecidableEq V] in
lemma BankBound.empty (F : Finset V) (h key size : ℕ) : BankBound F h key size ∅ :=
  ⟨by simp,by simp,by intro c hc; simp at hc,by simp⟩
end MetricKMedianRecovery.RationalLeaves

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves RationalHeight
variable {V : Type*} [LinearOrder V] {d : ℕ}

def StartOutput.Resources (F : Finset V) (q h p : ℕ) : StartOutput V → Prop
  | .small o => o.Resources F q h p
  | .normal o => o.Resources F q h p

omit [LinearOrder V] in
lemma initial_resources (F : Finset V) (h p : ℕ) (l u : ℚ)
    (T U : List (List (Label V))) (hl : Height l p) (hu : Height u p) :
    (initial l u T U).Resources F 0 h p :=
  ⟨BankBound.empty F h _ _,True.intro,hl,hu⟩

lemma start_resources (loc : Fin d → V) (distance : V → Fin d → ℚ) (F : Finset V)
    (v lo M : ℚ) (N precision total k H P : ℕ) (hlo : Height lo P)
    (hhi : Height (8*(d:ℚ)*M) P) (hfar : Height (20*N*M) H) :
    (start loc distance F v lo M N precision total k).Resources F total
      (CanonicalLengthSearch.heightBudget (20*N*M) precision H)
      (3*P+2*PriceBisection.iterations lo (8*(d:ℚ)*M) precision+2) := by
  let p := 3*P+2*PriceBisection.iterations lo (8*(d:ℚ)*M) precision+2
  have hl : Height lo p := hlo.mono (by dsimp only [p]; omega)
  have hh := PriceBisection.iterate_height hlo hhi
    (fun lam=>initialCount loc distance F v lam total) k
    (PriceBisection.iterations lo (8*(d:ℚ)*M) precision)
  rw [←PriceBisection.search_eq_iterate] at hh
  dsimp only [start]
  split_ifs
  · exact ⟨BankBound.empty F _ _ _,hl⟩
  · exact ⟨BankBound.empty F _ _ _,hh.1⟩
  · exact ⟨BankBound.empty F _ _ _,hh.2⟩
  · let I := PriceBisection.search (fun lam=>initialCount loc distance F v lam total) k
      (PriceBisection.iterations lo (8*(d:ℚ)*M) precision) (lo,8*(d:ℚ)*M)
    simpa only [StartOutput.Resources,Nat.zero_add] using
      (run_resources loc distance F v M N precision k H p hfar 0 total _
        (initial_resources F _ p I.1 I.2 (initialHistory loc distance F v I.2 total)
          (initialHistory loc distance F v I.1 total) hh.1 hh.2))
end MetricKMedianRecovery.CanonicalCoupledMerge

namespace MetricKMedianRecovery.BitMachine.BinaryInitialQuery
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
attribute [local irreducible] BinaryFiniteMachine.continuation

def ctx (base : List Bool) (total : ℕ) : List Bool := pairBits (List.replicate total true,base)
def bf (j : ℕ) : List Bool→List Bool := field j ∘ discardPrefix ∘ extractPrefix
noncomputable def bf_computes (j : ℕ) : PolyComputes (bf j) :=
  (extractPrefix_computes.comp discardPrefix_computes).comp (field_computes j)
noncomputable def atPrice (x : List Bool) : List Bool :=
  encode [bf 0 x,bf 1 x,bf 2 x,bf 3 x,bf 4 x,bf 5 x,bf 6 x,discardPrefix x]
noncomputable def atPrice_computes : PolyComputes atPrice :=
  list_computes [bf 0,bf 1,bf 2,bf 3,bf 4,bf 5,bf 6,discardPrefix] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact ⟨bf_computes _⟩ | exact ⟨discardPrefix_computes⟩)
lemma atPrice_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam t : ℚ) (total : ℕ) :
    atPrice (pairBits (ctx (BinaryFiniteContext.pack distance loc F Q v z lam) total,BinaryRational.encode t))=
      BinaryFiniteContext.pack distance loc F Q v z t := by
  simp only [atPrice,bf,Function.comp_apply,ctx,extractPrefix_pairBits,discardPrefix_pairBits,
    BinaryFiniteContext.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
noncomputable def history (x : List Bool) : List Bool := BinaryFiniteMachine.continuation
  (pairBits (extractPrefix (extractPrefix x),pairBits ([],atPrice x)))
noncomputable def history_computes : PolyComputes history :=
  ((extractPrefix_computes.comp extractPrefix_computes).pair ((const_computes []).pair atPrice_computes)).comp
    BinaryFiniteMachine.continuation_computes
lemma history_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (F : Finset (Fin m)) (v z lam t : ℚ) (total : ℕ) :
    history (pairBits (ctx (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) ∅ v z lam) total,
      BinaryRational.encode t))=historyBits (initialHistory loc distance F v t total) := by
  unfold history
  rw [atPrice_pack]
  simp only [ctx,extractPrefix_pairBits]
  exact BinaryFiniteMachine.continuation_pack distance _ _ _ v z t 0 total
noncomputable def opened (x : List Bool) : List Bool := BinaryFiniteMachine.after (pairBits ([],history x))
noncomputable def opened_computes : PolyComputes opened :=
  ((const_computes []).pair history_computes).comp BinaryFiniteMachine.after_computes
noncomputable def count (x : List Bool) : List Bool := BinaryFiniteContext.countInter (pairBits (opened x,bf 2 x))
noncomputable def count_computes : PolyComputes count := (opened_computes.pair (bf_computes 2)).comp BinaryFiniteContext.countInter_computes
lemma count_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (F : Finset (Fin m)) (v z lam t : ℚ) (total : ℕ) :
    count (pairBits (ctx (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) ∅ v z lam) total,
      BinaryRational.encode t))=(initialCount loc distance F v t total).bits := by
  unfold count opened
  rw [history_pack]
  simp only [bf,Function.comp_apply,ctx,extractPrefix_pairBits,discardPrefix_pairBits,
    BinaryFiniteContext.pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  have ha : BinaryFiniteMachine.after (pairBits ([],historyBits (initialHistory loc distance F v t total)))=
      setBits (PhaseHistoryTransfer.after ∅ (initialHistory loc distance F v t total)) := by
    simpa only [setBits,BinaryLabel.orderedSort,Finset.sort_empty,labels,List.map_nil,encode] using
      BinaryFiniteMachine.after_pack ∅ (initialHistory loc distance F v t total)
  rw [ha,BinaryFiniteContext.countInter_pack]
  rfl
lemma search_pack {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (F : Finset (Fin m)) (v z lam a b : ℚ) (total precision k : ℕ) :
    BinaryBisection.run count (BinaryBisection.pack precision
      (ctx (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) ∅ v z lam) total) k a b)=
      let I:=PriceBisection.search (fun t=>initialCount loc distance F v t total) k
        (PriceBisection.iterations a b precision) (a,b)
      pairBits (BinaryRational.encode I.1,BinaryRational.encode I.2) := by
  rw [BinaryBisection.run_pack]
  simp only [count_pack,value_bits]
end MetricKMedianRecovery.BitMachine.BinaryInitialQuery

end OAI
