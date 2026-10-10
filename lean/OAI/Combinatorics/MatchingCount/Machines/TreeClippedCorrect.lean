import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeDPRepresentation
import OAI.Combinatorics.MatchingCount.Machines.TreeClippedRun
import OAI.Combinatorics.MatchingCount.Sampling.ClippedEnvelope

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped Finset

def runCapped (o : CountInput) : List ℕ → Bags → Table → Bags×Table
  | [],bs,t => (bs,t)
  | l::ls,bs,t => runCapped o ls (trim bs l)
      (cappedUpdate ((o,((bs,o.1.2),(l,t))),ls.length))
lemma cappedStep_fold (o : CountInput) (ls : List ℕ) (bs : Bags) (t : Table) :
    ls.foldl (fun z l=>cappedStep (l,z)) (o,(ls.length,(bs,t)))=(o,(0,runCapped o ls bs t)) := by
  induction ls generalizing bs t with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.foldl_cons,List.length_cons,cappedStep,Nat.add_sub_cancel]
    exact ih _ _
lemma cappedCount_run (o : CountInput) :
    cappedCount o=finish ((runCapped o o.2 o.1.1 (initial (nLabels o,BInitial o))).2,nLabels o) := by
  unfold cappedCount
  rw [cappedStep_fold]

variable {V : Type} [Fintype V] [DecidableEq V] {m : ℕ}
variable (bags : V → Finset (Fin m)) (parent : Fin m → Option (Fin m))
lemma rawEntry_source (R : Finset V) (l a : Fin m) (r : ℕ) (t : Table) (bs : Bags)
    (hbs : bs.Perm (activeRep bags R)) :
    rawEntry (((bs,parentRep parent),(l.val,t)),(a.val,r))=UnitRefresh.Materialized.entry bags R parent l a t r := by
  unfold rawEntry
  rw [context_perm hbs]
  unfold context
  rw [parentRep_getD]
  simp only [privateNumber_activeRep,sharedNumber_activeRep,totalNumber_activeRep]
  exact entry_eq bags R parent l a t r

lemma cappedUpdate_source (o : CountInput) (hps : o.1.2=parentRep parent)
    (hn : nVertices o=Fintype.card V) (R : Finset V) (l : Fin m) (B : ℕ)
    (hB : B≤nPlan o) (t : Table) (bs : Bags) (hbs : bs.Perm (activeRep bags R))
    (hsize : ∀ (a : Fin m) r,(UnitRefresh.Materialized.entry bags R parent l a t r).size≤capBits o) :
    cappedUpdate ((o,((bs,o.1.2),(l.val,t))),B)=UnitRefresh.Materialized.update bags R parent l (Fintype.card V*B) t := by
  have hm : nLabels o=m := by simp only [nLabels,hps,parentRep_length]
  unfold cappedUpdate updateRows updateColumns
  dsimp only
  rw [hm,hn,Nat.min_eq_left hB]
  rw [tabulate_materialized]
  unfold UnitRefresh.Materialized.update
  congr 1
  funext a r
  unfold cappedEntry
  dsimp only
  rw [hps,rawEntry_source bags parent R l a r t bs hbs]
  exact clip_eq _ _ (hsize a r)

lemma runCapped_source (o : CountInput) (hps : o.1.2=parentRep parent)
    (hn : nVertices o=Fintype.card V)
    (hp : ∀ l p,parent l=some p → p≠l) (ls : List (Fin m)) (R : Finset V)
    (t : Table) (bs : Bags) (hbs : bs.Perm (activeRep bags R))
    (w : Fin m → ℕ) (hw : ∀ a,1≤w a) (ht : UnitRefresh.Materialized.RowBound t w)
    (E : ℕ) (he : (∏ a,w a)≤2^E)
    (hL : ls.length≤nPlan o) (hK : Fintype.card V*ls.length+E+1≤capBits o) :
    (runCapped o (ls.map Fin.val) bs t).2=UnitRefresh.Materialized.run bags parent ls R t := by
  induction ls generalizing R bs t w E with
  | nil => rfl
  | cons l ls ih =>
    have hlen : ls.length≤nPlan o := by rw [List.length_cons] at hL; omega
    have hstepK : E+Fintype.card V+1≤capBits o := by
      rw [List.length_cons,Nat.mul_add,Nat.mul_one] at hK
      omega
    have hsize := UnitRefresh.Materialized.entry_size_budget bags R parent l t w hw ht (hp l) E (capBits o) he hstepK
    have hup:=cappedUpdate_source bags parent o hps hn R l ls.length hlen t bs hbs hsize
    simp only [List.map_cons,runCapped,List.length_map,UnitRefresh.Materialized.run]
    rw [hup]
    let v:=UnitRefresh.Materialized.nextEnvelope bags R parent l w
    have hv : ∀ a,1≤v a := UnitRefresh.Materialized.nextEnvelope_pos bags R parent l w hw
    have hvt : UnitRefresh.Materialized.RowBound (UnitRefresh.Materialized.update bags R parent l (Fintype.card V*ls.length) t) v :=
      UnitRefresh.Materialized.update_rowBound bags R parent l _ t w hw ht
    have hvp : (∏ a,v a)≤2^(E+Fintype.card V) := UnitRefresh.Materialized.nextEnvelope_power bags R parent l w (hp l) E he
    apply ih (UnitRefresh.trim bags R l) _ (trim bs l) ((hbs.filter _).trans (trim_activeRep bags R l)) v hv hvt
      (E+Fintype.card V) hvp hlen
    rw [List.length_cons,Nat.mul_add,Nat.mul_one] at hK
    omega

lemma cappedCount_rep (ls : List (Fin m)) (bs : Bags) (hbs : bs.Perm (activeRep bags univ))
    (hp : ∀ l p,parent l=some p → p≠l) :
    cappedCount ((bs,parentRep parent),ls.map Fin.val)=UnitRefresh.Materialized.count bags parent ls := by
  let o : CountInput := ((bs,parentRep parent),ls.map Fin.val)
  have hn : nVertices o=Fintype.card V := by
    dsimp only [o,nVertices]
    rw [hbs.length_eq]
    simp [activeRep]
  have hm : nLabels o=m := by simp [o,nLabels]
  have hL : nPlan o=ls.length := by simp [o,nPlan]
  rw [cappedCount_run]
  change finish ((runCapped o (ls.map Fin.val) (bs) (initial (nLabels o,BInitial o))).2,nLabels o)=_
  rw [hm,initial_eq]
  let B:=BInitial o
  let E:=B*B*m
  have hw : ∀ a : Fin m,1≤2^(B*B) := fun _=>Nat.one_le_iff_ne_zero.mpr (by positivity)
  have he : (∏ a : Fin m,2^(B*B))≤2^E := by
    simp only [prod_const,card_univ,Fintype.card_fin,←pow_mul,E]
    exact le_rfl
  have hK : Fintype.card V*ls.length+E+1≤capBits o := by
    unfold capBits
    rw [hn,hL]
    dsimp only [E,B]
    rw [hm,pow_two]
  rw [runCapped_source bags parent o rfl hn hp ls univ (UnitRefresh.Materialized.initial m B) (bs)
    hbs (fun _=>2^(B*B)) hw (UnitRefresh.Materialized.initial_rowBound B) E he (by rw [hL]) hK]
  rw [finish_eq]
  unfold UnitRefresh.Materialized.count
  rw [show B=Fintype.card V*m by dsimp only [B,BInitial]; rw [hn,hm]]

lemma cappedCount_source (ls : List (Fin m))
    (hp : ∀ l p,parent l=some p → p≠l) :
    cappedCount ((activeRep bags Finset.univ,parentRep parent),ls.map Fin.val)=UnitRefresh.Materialized.count bags parent ls :=
  cappedCount_rep bags parent ls _ (List.Perm.refl _) hp

omit [Fintype V] [DecidableEq V] in
lemma cappedCount_ordered {n : ℕ} (bags : Fin n → Finset (Fin m)) (ls : List (Fin m))
    (hp : ∀ l p,parent l=some p → p≠l) :
    cappedCount ((orderedRep bags,parentRep parent),ls.map Fin.val)=UnitRefresh.Materialized.count bags parent ls :=
  cappedCount_rep bags parent ls _ (orderedRep_perm bags) hp

theorem cappedCount_coloredPairings (rank : Fin m → ℕ)
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l) :
    cappedCount ((activeRep bags Finset.univ,parentRep parent),(UnitRefresh.rankOrder rank).map Fin.val)=
      Fintype.card (UnitRefresh.ColoredPairing bags) := by
  rw [cappedCount_source bags parent _ (by intro l p h; have :=hp l p h; intro e; subst p; omega)]
  exact UnitRefresh.Materialized.count_eq bags rank parent hb hne hp
end MatchingFPRAS.ExecutableDP

end OAI
