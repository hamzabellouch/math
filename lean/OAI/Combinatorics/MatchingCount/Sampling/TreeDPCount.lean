import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeDPProgram

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped

def initial (x : ℕ×ℕ) : Table :=
  tabulate (fun ar : ℕ×(ℕ×ℕ)=>UnitRefresh.pairingCount ar.2.2) (0,x)

def initialRealizer : Realizer initial :=
  composition (pair (constant 0) identity)
    (tabulateRealizer (composition second.snd pairingNumber))

lemma initial_eq (m B : ℕ) : initial (m,B)=UnitRefresh.Materialized.initial m B := by
  exact tabulate_materialized (fun x : ℕ×(ℕ×ℕ)=>UnitRefresh.pairingCount x.2.2) 0 m B

def finish (x : Table×ℕ) : ℕ := ((List.range x.2).map fun a=>read (x.1,(a,0))).prod

def finishRealizer : Realizer finish :=
  composition (composition (pair first (composition second range))
    (mapWith (composition (pair first (pair second (constant 0))) readRealizer))) listProd

lemma map_range_ofFn {A : Type} (f : ℕ → A) (n : ℕ) :
    (List.range n).map f=List.ofFn (fun i : Fin n=>f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'; simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]

lemma finish_eq (t : Table) (m : ℕ) :
    finish (t,m)=∏ a : Fin m,UnitRefresh.Materialized.read t a.val 0 := by
  rw [finish,map_range_ofFn,List.prod_ofFn]
  rfl

abbrev CountInput := (Bags×Parents)×List ℕ

def count (x : CountInput) : ℕ :=
  let n:=x.1.1.length
  let m:=x.1.2.length
  finish (run ((n,(m,x.1.2)),(x.2,(x.1.1,initial (m,n*m)))),m)

def countRealizer : Realizer count := by
  let bs : Realizer (fun x : CountInput=>x.1.1) := first.fst
  let ps : Realizer (fun x : CountInput=>x.1.2) := first.snd
  let ls : Realizer (fun x : CountInput=>x.2) := second
  let n := composition bs listLength
  let m := composition ps listLength
  let B := composition (pair n m) multiply
  let t := composition (pair m B) initialRealizer
  let p := pair n (pair m ps)
  let table := composition (pair p (pair ls (pair bs t))) runRealizer
  exact (composition (pair table m) finishRealizer).congr (fun _=>rfl)

lemma count_eq {V : Type} [Fintype V] [DecidableEq V] {m : ℕ}
    (bags : V → Finset (Fin m)) (parent : Fin m → Option (Fin m)) (ls : List (Fin m)) :
    count ((activeRep bags Finset.univ,parentRep parent),ls.map Fin.val)=
      UnitRefresh.Materialized.count bags parent ls := by
  unfold count
  rw [show (activeRep bags Finset.univ).length=Fintype.card V by simp [activeRep]]
  rw [parentRep_length]
  dsimp only
  rw [initial_eq]
  unfold run
  rw [run_eq bags parent ls Finset.univ _ _ (List.Perm.refl _),finish_eq]
  rfl

theorem count_coloredPairings {V : Type} [Fintype V] [DecidableEq V] {m : ℕ}
    (bags : V → Finset (Fin m)) (rank : Fin m → ℕ) (parent : Fin m → Option (Fin m))
    (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l) :
    count ((activeRep bags Finset.univ,parentRep parent),(UnitRefresh.rankOrder rank).map Fin.val)=
      Fintype.card (UnitRefresh.ColoredPairing bags) := by
  rw [count_eq]
  exact UnitRefresh.Materialized.count_eq bags rank parent hb hne hp

end MatchingFPRAS.ExecutableDP

end OAI
